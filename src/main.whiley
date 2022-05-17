import uint256, address, map, msg, EXP_160, EXP_256 from evm::types

public map<uint256> balances = [0; EXP_160]

public method transfer(address to, uint256 value)
// Ensure sufficient funds in source account
requires balances[msg.sender] >= value
// Provent overflow in target account
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