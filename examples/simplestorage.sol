//pragma solidity ^0.4.0;

contract SimpleStorage {
  mapping (uint => uint) nameRegistry; // state variable on the contract storage
 
  function nameRegister(uint key, uint value) {
    if (nameRegistry[key] == 0)
	nameRegistry[key] = value;
  }
}

