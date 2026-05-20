pub(crate) const SYNTAX_MATCH_HELPERS: &str = r##"
-- Syntax template and quote-pattern runtime helpers.
local function __syntax_copy_captures(captures)
  local out = {}
  for k, v in pairs(captures) do out[k] = v end
  return out
end

local function __syntax_slice(nodes, first, last)
  local out = {}
  for i = first, last do out[#out + 1] = nodes[i] end
  return out
end

local function __syntax_sequence_value(nodes)
  if #nodes == 1 then return nodes[1] end
  return { _tag = "Sequence", _0 = { nodes, {} } }
end

local function __syntax_template_append(out, value)
  if value._tag == "Sequence" then
    for i = 1, #value._0[1] do out[#out + 1] = value._0[1][i] end
  else
    out[#out + 1] = value
  end
end

local function __syntax_template_append_many(out, values)
  for i = 1, #values do __syntax_template_append(out, values[i]) end
end

local function __syntax_template_tree(delimiter, children)
  local out = {}
  for i = 1, #children do
    local child = children[i]
    if child.kind == "node" then
      out[#out + 1] = child.value
    elseif child.kind == "splice" then
      __syntax_template_append(out, child.value)
    elseif child.kind == "many" then
      __syntax_template_append_many(out, child.value)
    end
  end
  return { _tag = "Tree", _0 = { delimiter, out, {} } }
end

-- Hygiene-aware syntax shape equality. Identifier tokens compare both text and scope.
local function __syntax_equal(lhs, rhs)
  if lhs == rhs then return true end
  if type(lhs) ~= "table" or type(rhs) ~= "table" then return false end
  if lhs._tag == nil and rhs._tag == nil then
    if #lhs ~= #rhs then return false end
    for i = 1, #lhs do if not __syntax_equal(lhs[i], rhs[i]) then return false end end
    return true
  end
  if lhs._tag ~= rhs._tag then return false end
  if lhs._tag == "Token" then
    local lt, rt = lhs._0[1], rhs._0[1]
    if lt._tag ~= rt._tag then return false end
    if lt._tag == "Ident" then return lt._0[1] == rt._0[1] and lt._0[2] == rt._0[2] end
    return lt._0 == rt._0
  elseif lhs._tag == "Tree" then
    if lhs._0[1]._tag ~= rhs._0[1]._tag then return false end
    local lc, rc = lhs._0[2], rhs._0[2]
    if #lc ~= #rc then return false end
    for i = 1, #lc do if not __syntax_equal(lc[i], rc[i]) then return false end end
    return true
  elseif lhs._tag == "Sequence" then
    local lc, rc = lhs._0[1], rhs._0[1]
    if #lc ~= #rc then return false end
    for i = 1, #lc do if not __syntax_equal(lc[i], rc[i]) then return false end end
    return true
  end
  return false
end

local function __syntax_token_category(node, tag)
  return node and node._tag == "Token" and node._0[1]._tag == tag
end

local function __syntax_token_tag(node)
  if not node or node._tag ~= "Token" then return nil end
  return node._0[1]._tag
end

local function __syntax_token_text(node)
  if not node or node._tag ~= "Token" then return nil end
  local token = node._0[1]
  if token._tag == "Ident" then return token._0[1] end
  return token._0
end

local function __syntax_is_operator(node, text)
  return __syntax_token_tag(node) == "Operator" and (text == nil or __syntax_token_text(node) == text)
end

local function __syntax_is_punct(node, text)
  return __syntax_token_tag(node) == "Punct" and (text == nil or __syntax_token_text(node) == text)
end

-- Public syntax helper surface used by runtime code and macro-expanded programs.
function syntax_delimiter(node)
  if node and node._tag == "Tree" then return Some(node._0[1]) end
  return None
end

function syntax_kind(node)
  if not node then return "unknown" end
  if node._tag == "Token" then return "token" end
  if node._tag == "Sequence" then return "sequence" end
  if node._tag == "Tree" then
    local delimiter = node._0[1]._tag
    if delimiter == "Paren" then return "tree:paren" end
    if delimiter == "Brace" then return "tree:brace" end
    if delimiter == "Bracket" then return "tree:bracket" end
  end
  return "unknown"
end

function syntax_span(node)
  local meta = node and node._0 and node._0[#node._0]
  return (meta and meta.span) or { 0, 0, 0, 0 }
end

function syntax_origin(node)
  local meta = node and node._0 and node._0[#node._0]
  return (meta and meta.origin) or "generated"
end

function syntax_eq_shape(lhs, rhs)
  return __syntax_equal(lhs, rhs) and 1 or 0
end

function syntax_same_binding(lhs, rhs)
  if not __syntax_token_category(lhs, "Ident") or not __syntax_token_category(rhs, "Ident") then
    return 0
  end
  local li, ri = lhs._0[1], rhs._0[1]
  return (li._0[1] == ri._0[1] and li._0[2] == ri._0[2]) and 1 or 0
end

local function __syntax_generated_meta()
  return { span = { 0, 0, 0, 0 }, origin = "generated" }
end

local __syntax_fresh_scope = 100000

function syntax_token(token)
  return { _tag = "Token", _0 = { token, __syntax_generated_meta() } }
end

function syntax_tree(delimiter, children)
  return { _tag = "Tree", _0 = { delimiter, children, __syntax_generated_meta() } }
end

function syntax_sequence(children)
  return { _tag = "Sequence", _0 = { children, __syntax_generated_meta() } }
end

function syntax_ident(text)
  return syntax_token({ _tag = "Ident", _0 = { text, 1 } })
end

function syntax_literal(text)
  return syntax_token({ _tag = "Literal", _0 = text })
end

function syntax_operator(text)
  return syntax_token({ _tag = "Operator", _0 = text })
end

function syntax_punct(text)
  return syntax_token({ _tag = "Punct", _0 = text })
end

function syntax_fresh_ident(text)
  local scope = __syntax_fresh_scope
  __syntax_fresh_scope = __syntax_fresh_scope + 1
  return syntax_token({ _tag = "Ident", _0 = { text, scope } })
end

function syntax_ident_at_use_site(text)
  return syntax_token({ _tag = "Ident", _0 = { text, 20000 } })
end

local function __syntax_source(node)
  if not node then return "<unknown>" end
  if node._tag == "Token" then
    return __syntax_token_text(node) or "<token>"
  elseif node._tag == "Tree" then
    local delimiter = node._0[1]._tag
    local open, close = "(", ")"
    if delimiter == "Brace" then open, close = "{", "}" end
    if delimiter == "Bracket" then open, close = "[", "]" end
    local parts = {}
    for i = 1, #node._0[2] do parts[#parts + 1] = __syntax_source(node._0[2][i]) end
    return open .. table.concat(parts, " ") .. close
  elseif node._tag == "Sequence" then
    local parts = {}
    for i = 1, #node._0[1] do parts[#parts + 1] = __syntax_source(node._0[1][i]) end
    return table.concat(parts, " ")
  end
  return "<syntax>"
end

function syntax_map_children(node, mapper)
  if node._tag == "Tree" then
    local mapped = {}
    for i = 1, #node._0[2] do mapped[#mapped + 1] = mapper(node._0[2][i]) end
    return { _tag = "Tree", _0 = { node._0[1], mapped, node._0[3] } }
  elseif node._tag == "Sequence" then
    local mapped = {}
    for i = 1, #node._0[1] do mapped[#mapped + 1] = mapper(node._0[1][i]) end
    return { _tag = "Sequence", _0 = { mapped, node._0[2] } }
  end
  return node
end

function syntax_find(node, predicate)
  if predicate(node) ~= 0 then return Some(node) end
  local children = nil
  if node._tag == "Tree" then children = node._0[2] end
  if node._tag == "Sequence" then children = node._0[1] end
  if children then
    for i = 1, #children do
      local found = syntax_find(children[i], predicate)
      if found._tag == "Some" then return found end
    end
  end
  return None
end

function syntax_replace(node, target, replacement)
  if __syntax_equal(node, target) then return replacement end
  if node._tag == "Tree" then
    local replaced = {}
    for i = 1, #node._0[2] do replaced[#replaced + 1] = syntax_replace(node._0[2][i], target, replacement) end
    return { _tag = "Tree", _0 = { node._0[1], replaced, node._0[3] } }
  elseif node._tag == "Sequence" then
    local replaced = {}
    for i = 1, #node._0[1] do replaced[#replaced + 1] = syntax_replace(node._0[1][i], target, replacement) end
    return { _tag = "Sequence", _0 = { replaced, node._0[2] } }
  end
  return node
end

function syntax_join(items, separator)
  local out = {}
  for i = 1, #items do
    if i > 1 then out[#out + 1] = separator end
    out[#out + 1] = items[i]
  end
  return syntax_sequence(out)
end

function syntax_debug(node)
  return syntax_kind(node) .. " " .. __syntax_source(node)
end

local function __syntax_is_name(node, text)
  local tag = __syntax_token_tag(node)
  return (tag == "Ident" or tag == "Keyword") and (text == nil or __syntax_token_text(node) == text)
end

local __syntax_parse_expr
local __syntax_parse_type
local __syntax_parse_pat

-- Mirrored parser subset for runtime syntax categories; pinned against Rust tests.
local function __syntax_parse_comma_list(nodes, parser, allow_empty)
  if #nodes == 0 then return allow_empty end
  local index = 1
  while index <= #nodes do
    local next_index = parser(nodes, index)
    if not next_index then return false end
    index = next_index
    if index > #nodes then return true end
    if not __syntax_is_punct(nodes[index], ",") then return false end
    index = index + 1
    if index > #nodes then return false end
  end
  return true
end

local function __syntax_parse_expr_primary(nodes, index)
  local node = nodes[index]
  if not node then return nil end
  local tag = __syntax_token_tag(node)
  if tag == "Ident" or tag == "Literal" then return index + 1 end
  if __syntax_is_name(node, "if") then
    local cond_end = __syntax_parse_expr(nodes, index + 1)
    if not cond_end then return nil end
    local then_branch = nodes[cond_end]
    if not then_branch or then_branch._tag ~= "Tree" or then_branch._0[1]._tag ~= "Brace" then return nil end
    local next_index = cond_end + 1
    if __syntax_is_name(nodes[next_index], "else") then
      local else_end = __syntax_parse_expr(nodes, next_index + 1)
      if not else_end then return nil end
      return else_end
    end
    return next_index
  end
  if __syntax_is_name(node, "fn") then
    local params = nodes[index + 1]
    local body = nodes[index + 2]
    if not params or params._tag ~= "Tree" or params._0[1]._tag ~= "Paren" then return nil end
    if not body or body._tag ~= "Tree" or body._0[1]._tag ~= "Brace" then return nil end
    return index + 3
  end
  if __syntax_is_punct(node, "#") then
    local record = nodes[index + 1]
    if record and record._tag == "Tree" and record._0[1]._tag == "Brace" then return index + 2 end
    return nil
  end
  if __syntax_is_operator(node, "-") or __syntax_is_operator(node, "!") then
    return __syntax_parse_expr_primary(nodes, index + 1)
  end
  if node._tag == "Tree" then
    local delimiter, children = node._0[1]._tag, node._0[2]
    if delimiter == "Paren" then
      return __syntax_parse_comma_list(children, __syntax_parse_expr, false) and index + 1 or nil
    elseif delimiter == "Bracket" then
      return __syntax_parse_comma_list(children, __syntax_parse_expr, true) and index + 1 or nil
    elseif delimiter == "Brace" then
      return index + 1
    end
  end
  return nil
end

__syntax_parse_expr = function(nodes, index)
  local next_index = __syntax_parse_expr_primary(nodes, index)
  if not next_index then return nil end
  while next_index <= #nodes do
    local node = nodes[next_index]
    if node and node._tag == "Tree" and node._0[1]._tag == "Paren" then
      if not __syntax_parse_comma_list(node._0[2], __syntax_parse_expr, true) then return nil end
      next_index = next_index + 1
    elseif node and node._tag == "Tree" and node._0[1]._tag == "Bracket" then
      local key_end = __syntax_parse_expr(node._0[2], 1)
      if not key_end or key_end <= #node._0[2] then return nil end
      next_index = next_index + 1
    elseif __syntax_is_punct(node, ".") then
      if not __syntax_is_name(nodes[next_index + 1]) then return nil end
      next_index = next_index + 2
    elseif __syntax_is_punct(node, "::") then
      if not __syntax_is_name(nodes[next_index + 1]) then return nil end
      next_index = next_index + 2
    elseif __syntax_is_operator(node) then
      next_index = __syntax_parse_expr_primary(nodes, next_index + 1)
      if not next_index then return nil end
    else
      break
    end
  end
  return next_index
end

__syntax_parse_type = function(nodes, index)
  local node = nodes[index]
  if __syntax_is_punct(node, "#") then
    local record = nodes[index + 1]
    if record and record._tag == "Tree" and record._0[1]._tag == "Brace" then return index + 2 end
    return nil
  end
  if node and node._tag == "Tree" and node._0[1]._tag == "Bracket" then
    return __syntax_parse_comma_list(node._0[2], __syntax_parse_type, false) and index + 1 or nil
  end
  if __syntax_is_name(node, "fn") then
    local params = nodes[index + 1]
    if not params or params._tag ~= "Tree" or params._0[1]._tag ~= "Paren" then return nil end
    if not __syntax_parse_comma_list(params._0[2], __syntax_parse_type, true) then return nil end
    if not __syntax_is_operator(nodes[index + 2], "->") then return nil end
    local ret = __syntax_parse_type(nodes, index + 3)
    return ret
  end
  if not (__syntax_is_name(node) or (__syntax_token_tag(node) == "Operator" and __syntax_token_text(node) == "->")) then
    return nil
  end
  local next_index = index + 1
  if next_index <= #nodes and nodes[next_index]._tag == "Tree" and nodes[next_index]._0[1]._tag == "Paren" then
    if not __syntax_parse_comma_list(nodes[next_index]._0[2], __syntax_parse_type, true) then return nil end
    next_index = next_index + 1
  end
  return next_index
end

__syntax_parse_pat = function(nodes, index)
  local node = nodes[index]
  if not node then return nil end
  local tag = __syntax_token_tag(node)
  if tag == "Literal" then return index + 1 end
  if __syntax_is_punct(node, "#") then
    local record = nodes[index + 1]
    if record and record._tag == "Tree" and record._0[1]._tag == "Brace" then return index + 2 end
    return nil
  end
  if tag == "Ident" then
    local next_index = index + 1
    if next_index <= #nodes and nodes[next_index]._tag == "Tree" and nodes[next_index]._0[1]._tag == "Paren" then
      if not __syntax_parse_comma_list(nodes[next_index]._0[2], __syntax_parse_pat, false) then return nil end
      next_index = next_index + 1
    end
    return next_index
  end
  if node._tag == "Tree" then
    local delimiter, children = node._0[1]._tag, node._0[2]
    if delimiter == "Bracket" and #children >= 1 and __syntax_is_operator(children[1], "..") then
      return (#children == 1 or (#children == 2 and __syntax_token_tag(children[2]) == "Ident")) and index + 1 or nil
    elseif delimiter == "Paren" or delimiter == "Bracket" then
      return __syntax_parse_comma_list(children, __syntax_parse_pat, true) and index + 1 or nil
    elseif delimiter == "Brace" then
      return index + 1
    end
  end
  return nil
end

local function __syntax_matches_parser_category(category, nodes, first, last)
  local slice = __syntax_slice(nodes, first, last)
  local parser = category == "expr" and __syntax_parse_expr
    or category == "type" and __syntax_parse_type
    or category == "pat" and __syntax_parse_pat
    or nil
  if parser == nil then return false end
  local next_index = parser(slice, 1)
  return next_index ~= nil and next_index > #slice
end

local function __syntax_match_category(category, nodes, first, last)
  local count = last - first + 1
  if category == "tokens" then return count >= 0 end
  if count <= 0 then return false end
  if category == "expr" or category == "type" or category == "pat" then
    return __syntax_matches_parser_category(category, nodes, first, last)
  end
  if count ~= 1 then return false end
  local node = nodes[first]
  if category == "ident" then return __syntax_token_category(node, "Ident") end
  if category == "literal" then return __syntax_token_category(node, "Literal") end
  if category == "operator" then return __syntax_token_category(node, "Operator") end
  if category == "punct" then return __syntax_token_category(node, "Punct") end
  if category == "token" then return node and node._tag == "Token" end
  if category == "tree" then return node and node._tag == "Tree" end
  if category == "block" then return node and node._tag == "Tree" and node._0[1]._tag == "Brace" end
  return false
end

-- Recursive quote-pattern matcher. Successful matches return a capture table.
local function __syntax_match_repeated_category(category, nodes, first, last)
  if last < first then return true end
  for i = first, last do
    if not __syntax_match_category(category, nodes, i, i) then return false end
  end
  return true
end

local function __syntax_capture_value(pattern, nodes, first, last)
  local slice = __syntax_slice(nodes, first, last)
  if pattern.repeat_capture then return slice end
  return __syntax_sequence_value(slice)
end

local function __syntax_match_token_pattern(pattern, node)
  if not node or node._tag ~= "Token" then return false end
  local actual, expected = node._0[1], pattern.token
  if actual._tag ~= expected._tag then return false end
  if actual._tag == "Ident" then return actual._0[1] == expected._0 end
  return actual._0 == expected._0
end

local __syntax_match_node
local __syntax_match_sequence

__syntax_match_node = function(pattern, node, captures)
  if pattern.kind == "token" then
    return __syntax_match_token_pattern(pattern, node) and captures or nil
  elseif pattern.kind == "tree" then
    if not node or node._tag ~= "Tree" or node._0[1]._tag ~= pattern.delimiter then return nil end
    return __syntax_match_sequence(pattern.children, node._0[2], 1, 1, captures)
  elseif pattern.kind == "capture" then
    if not __syntax_match_category(pattern.category, { node }, 1, 1) then return nil end
    local next_captures = __syntax_copy_captures(captures)
    local value = pattern.repeat_capture and { node } or node
    if next_captures[pattern.name] ~= nil and not __syntax_equal(next_captures[pattern.name], value) then return nil end
    next_captures[pattern.name] = value
    return next_captures
  end
  return nil
end

__syntax_match_sequence = function(patterns, nodes, pattern_index, node_index, captures)
  if pattern_index > #patterns then
    if node_index > #nodes then return captures else return nil end
  end
  local pattern = patterns[pattern_index]
  if pattern.kind == "capture" then
    local min_count = pattern.repeat_capture and 0 or 1
    for count = min_count, (#nodes - node_index + 1) do
      local last = node_index + count - 1
      local category_matches
      if pattern.repeat_capture then
        category_matches = __syntax_match_repeated_category(pattern.category, nodes, node_index, last)
      else
        category_matches = __syntax_match_category(pattern.category, nodes, node_index, last)
      end
      if category_matches then
        local value = __syntax_capture_value(pattern, nodes, node_index, last)
        local next_captures = __syntax_copy_captures(captures)
        if next_captures[pattern.name] == nil or __syntax_equal(next_captures[pattern.name], value) then
          next_captures[pattern.name] = value
          local result = __syntax_match_sequence(patterns, nodes, pattern_index + 1, last + 1, next_captures)
          if result ~= nil then return result end
        end
      end
    end
    return nil
  else
    local next_captures = __syntax_match_node(pattern, nodes[node_index], captures)
    if next_captures == nil then return nil end
    return __syntax_match_sequence(patterns, nodes, pattern_index + 1, node_index + 1, next_captures)
  end
end

local function __syntax_match(pattern, node)
  return __syntax_match_node(pattern, node, {})
end
"##;
