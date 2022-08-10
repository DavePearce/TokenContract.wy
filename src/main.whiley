import uint256, MAX_UINT256 from evm::ints
import uint160, MAX_UINT160 from evm::ints
import evm::map with map
import evm::msg

// ============================================================================
// Contract State
// ============================================================================

// Maintains the tokens of all accounts.
public map<uint256> tokens = [0; MAX_UINT160+1]
// Records the total number of coins in circulation
public uint256 total = 0
// Records the owner of this contract.
public uint160 owner = 0

// ============================================================================
// Contract Methods
// ============================================================================

// Mint new coins into a given target uint160
public method mint(uint160 to, uint256 value)
// Only the owner can mint new coins
requires msg::sender == owner
// Prevent overflow in target account
requires tokens[to] + value <= MAX_UINT256
// Prevent overflow of total
requires total + value <= MAX_UINT256
// Ensures total increased as expected
ensures total == old(total) + value
// Ensure target balance increased
ensures tokens[to] == old(tokens[to]) + value:
   // Increase target balance
   tokens[to] = tokens[to] + value
   // Increase total
   total = total + value

// Burn a given number of coins, thereby reducing the overall total in
// circulation.
public method burn(uint160 to, uint256 amount)
// Only the owner can burn coins
requires msg::sender == owner
// Cannot burn more tokens than held in account
requires tokens[to] >= amount && total >= amount
// Ensures total decreased as expected
ensures total == old(total) - amount
// Ensure target balance decreased
ensures tokens[to] == old(tokens[to]) - amount:
   // Decrease target balance
   tokens[to] = tokens[to] - amount
   // Decrease total
   total = total - amount

// Transfer some amount of tokens from one account to another.
public method transfer(uint160 to, uint256 value)
// Ensure sufficient funds in source account
requires tokens[msg::sender] >= value
// Prevent overflow in target account
requires tokens[to] + value <= MAX_UINT256
// Cannot transfer to myself!
requires msg::sender != to
// Token invariant
requires sum(tokens,0) == total
// Token invariant preserved
ensures sum(tokens,0) == total
// Ensure source balance decreased
ensures tokens[msg::sender] == old(tokens[msg::sender]) - value
// Ensure target balance increased
ensures tokens[to] == old(tokens[to]) + value:
    // Reduce source balance
    map<uint256> otokens = tokens
    tokens[msg::sender] = tokens[msg::sender] - value
    // Apply delta lemma
    lemma_2(otokens,tokens,msg::sender,0,value)
    // Increase target balance
    otokens = tokens
    tokens[to] = tokens[to] + value
    // Apply delta lemma
    lemma_2(tokens,otokens,to,0,value)

// ============================================================================
// Contract Property
// ============================================================================

public property sum(map<uint256> tokens, int i) -> (int r)
requires i >= 0 && i <= |tokens|:
    if i == |tokens|:
        return 0
    else:
        return tokens[i] + sum(tokens,i+1)

function lemma_1(map<uint256> xs, map<uint256> ys, int i)
// Arrays must have same size
requires |xs| == |ys|
// Index must be within bounds
requires i >= 0 && i <= |xs|
// Everything beyond this is the same
requires all { k in i..|xs| | xs[k] == ys[k] }
// Conclusion
ensures sum(xs,i) == sum(ys,i):
   //
   if i == |xs|:
      // base case
   else:
      lemma_1(xs,ys,i+1)

// Index i identifies position within the two arrays which differ.
// Index j is current index through arrays (starting from zero).
function lemma_2(map<uint256> xs, map<uint256> ys, uint160 i, int j, uint256 d)
// Arrays must have same size
requires |xs| == |ys|
// Indices must be within bounds
requires j >= 0 && j <= i && i < |xs|
// Everything else must be same
requires all { k in 0..|xs| | k == i || xs[k] == ys[k] }
// Ith element must have increased
requires xs[i] == ys[i] + d
// Conclusion
ensures sum(xs,j) == sum(ys,j) + d:
    //
    if j < i:
        lemma_2(xs,ys,i,j+1,d)
    else:
        lemma_1(xs,ys,i+1)      
