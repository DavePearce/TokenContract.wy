import uint256, address, map, msg, EXP_160, EXP_256 from evm::types

// Maintains the balances of all accounts.
public map<uint256> balances = [0; EXP_160]

// Records the total number of coins in circulation
public uint256 total = 0

// Records the owner of this contract.
public address owner = 0

// Mint new coins into a given target address
public method mint(address to, uint256 value)
// Only the owner can mint new coins
requires msg.sender == owner
// Prevent overflow in target account
requires balances[to] + value < EXP_256
// Prevent overflow of total
requires total + value < EXP_256
// Ensures total increased as expected
ensures total == old(total) + value
// Ensure target balance increased
ensures balances[to] == old(balances[to]) + value:
   // Increase target balance
   balances[to] = balances[to] + value
   // Increase total
   total = total + value

// Burn a given number of coins, thereby reducing the overall total in
// circulation.
public method burn(address to, uint256 amount)
// Only the owner can burn coins
requires msg.sender == owner
// Cannot burn more tokens than held in account
requires balances[to] >= amount && total >= amount
// Ensures total decreased as expected
ensures total == old(total) - amount
// Ensure target balance decreased
ensures balances[to] == old(balances[to]) - amount:
   // Decrease target balance
   balances[to] = balances[to] - amount
   // Decrease total
   total = total - amount

// Transfer some amount of tokens from one account to another.
public method transfer(address to, uint256 value)
// Ensure sufficient funds in source account
requires balances[msg.sender] >= value
// Prevent overflow in target account
requires balances[to] + value < EXP_256
// Cannot transfer to myself!
requires msg.sender != to
// Ensure source balance decreased
ensures balances[msg.sender] == old(balances[msg.sender]) - value
// Ensure target balance increased
ensures balances[to] == old(balances[to]) + value:
    // Reduce source balance
    balances[msg.sender] = balances[msg.sender] - value
    // Increase target balance
    balances[to] = balances[to] + value
