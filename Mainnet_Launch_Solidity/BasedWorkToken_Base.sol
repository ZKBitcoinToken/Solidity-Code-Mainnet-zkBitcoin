// Based Work Token - BWORK Token - Mining Contract Base Network
//
// Website: https://BasedWorkToken.org/
// Github: https://github.com/BasedWorkToken/
// Discord: https://discord.gg/QrGNf47ATk/
// Twitter: https://x.com/BasedWorkToken/
//
//
// Distrubtion of Based Work Token - BWORK Token is as follows:
//
// 100% of BWORK Token is distributed using this contract which distributes tokens to users by using Proof of work and is considered a Version 2 & Layer 2 0xBitcoin allowing all 0xBitcoin to be converted to BWORK Tokens.
// Computers solve a complicated problem to gain tokens!
// 100% of 0xBitcoin accepted for BWORK Tokens
// 100% Of the Token is distributed to the users! No dev fee!
//
//
// Symbol: BWORK
// Decimals: 18
//
// Total supply: 21,000,000.000000000000000000
//   =
// 10,835,900 0xBitcoin Tokens able to transfered to BWORK Tokens.
// +
// 10,164,100 Mined over 100+ years using Bitcoins Distrubtion halvings every ~4 years. Uses Proof-oF-Work to distribute the tokens. Public Miner is available see https://BasedWorkToken.org 
//  
//
// No dev cut, or advantage taken at launch. Public miner available at launch. 100% of the token is given away fairly over 100+ years using Bitcoins model!
// 
// Mint 2016 answers per challenge in this cost savings Bitcoin!! Less failed transactions as the challenge only changes every 2016 answers instead of every answer.
//
// Credits: 0xBitcoin
//
// startTime =  1738771200;  //Date and time (GMT): Wednesday, Feb 5, 2025 4:00:00 PM GMT then openMining functioncan then be called and mining will have rewards, until then all rewards will be 0.















/////
//IMPORT Includes below, then main BasedWorkToken contract
/////

// File: contracts/draft-IERC20Permit.sol

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)


pragma solidity ^0.8.13;



contract Ownable {
    address public owner;
    event TransferOwnership(address _from, address _to);

    constructor() {
        owner = msg.sender;
        emit TransferOwnership(address(0), msg.sender);
    }

    modifier onlyOwner() {
        require(msg.sender == owner, "only owner, paymaster for this contract");
        _;
    }
/* WE DONT EVER WANT OWNERSHIP TRANSFERED
    function setOwner(address _owner) public onlyOwner {
        emit TransferOwnership(owner, _owner);
        owner = _owner;
    }
    */
}




/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// File: contracts/IERC20.sol

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// File: contracts/IERC20Metadata.sol

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

// File: contracts/Context.sol

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// File: contracts/ERC20.sol

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC20
 * applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *tot
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    string private _name;
    string private _symbol;
    uint _maxTotalSupply;
    uint8 _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_, uint8 decimals_, uint totalSupply_) {
        _name = name_;
        _symbol = symbol_;
        _maxTotalSupply = totalSupply_;
        _decimals = decimals_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _maxTotalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
        }
        _balances[to] += amount;

        emit Transfer(from, to, amount);

    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {

        _balances[account] += amount;
        emit Transfer(address(0), account, amount);

    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
        }

        emit Transfer(account, address(0), amount);

    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }
}

// File: contracts/Strings.sol


/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant _HEX_SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        // Inspired by OraclizeAPI's implementation - MIT licence
        // https://github.com/oraclize/ethereum-api/blob/b42146b063c7d6ee1358846c198246239e9360e8/oraclizeAPI_0.4.25.sol

        if (value == 0) {
            return "0";
        }
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0x00";
        }
        uint256 temp = value;
        uint256 length = 0;
        while (temp != 0) {
            length++;
            temp >>= 8;
        }
        return toHexString(value, length);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _HEX_SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), _ADDRESS_LENGTH);
    }
}

// File: contracts/ECDSA.sol

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS,
        InvalidSignatureV
    }

    function _throwError(RecoverError error) private pure {
        if (error == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (error == RecoverError.InvalidSignature) {
            revert("ECDSA: invalid signature");
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert("ECDSA: invalid signature length");
        } else if (error == RecoverError.InvalidSignatureS) {
            revert("ECDSA: invalid signature 's' value");
        } else if (error == RecoverError.InvalidSignatureV) {
            revert("ECDSA: invalid signature 'v' value");
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature` or error string. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError) {
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength);
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, signature);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     *
     * _Available since v4.3._
     */
    function tryRecover(
        bytes32 hash,
        bytes32 r,
        bytes32 vs
    ) internal pure returns (address, RecoverError) {
        bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        uint8 v = uint8((uint256(vs) >> 255) + 27);
        return tryRecover(hash, v, r, s);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
     *
     * _Available since v4.2._
     */
    function recover(
        bytes32 hash,
        bytes32 r,
        bytes32 vs
    ) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, r, vs);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     *
     * _Available since v4.3._
     */
    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address, RecoverError) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS);
        }
        if (v != 27 && v != 28) {
            return (address(0), RecoverError.InvalidSignatureV);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature);
        }

        return (signer, RecoverError.NoError);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function recover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, v, r, s);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from a `hash`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes32 hash) internal pure returns (bytes32) {
        // 32 is the length in bytes of hash,
        // enforced by the type signature above
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", hash));
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from `s`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes memory s) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n", Strings.toString(s.length), s));
    }

    /**
     * @dev Returns an Ethereum Signed Typed Data, created from a
     * `domainSeparator` and a `structHash`. This produces hash corresponding
     * to the one signed with the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`]
     * JSON-RPC method as part of EIP-712.
     *
     * See {recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
    }
}

// File: contracts/draft-EIP712.sol


/**
 * @dev https://eips.ethereum.org/EIPS/eip-712[EIP 712] is a standard for hashing and signing of typed structured data.
 *
 * The encoding specified in the EIP is very generic, and such a generic implementation in Solidity is not feasible,
 * thus this contract does not implement the encoding itself. Protocols need to implement the type-specific encoding
 * they need in their contracts using a combination of `abi.encode` and `keccak256`.
 *
 * This contract implements the EIP 712 domain separator ({_domainSeparatorV4}) that is used as part of the encoding
 * scheme, and the final step of the encoding to obtain the message digest that is then signed via ECDSA
 * ({_hashTypedDataV4}).
 *
 * The implementation of the domain separator was designed to be as efficient as possible while still properly updating
 * the chain id to protect against replay attacks on an eventual fork of the chain.
 *
 * NOTE: This contract implements the version of the encoding known as "v4", as implemented by the JSON RPC method
 * https://docs.metamask.io/guide/signing-data.html[`eth_signTypedDataV4` in MetaMask].
 *
 * _Available since v3.4._
 */
abstract contract EIP712 {
    /* solhint-disable var-name-mixedcase */
    // Cache the domain separator as an immutable value, but also store the chain id that it corresponds to, in order to
    // invalidate the cached domain separator if the chain id changes.
    bytes32 private immutable _CACHED_DOMAIN_SEPARATOR;
    uint256 private immutable _CACHED_CHAIN_ID;
    address private immutable _CACHED_THIS;

    bytes32 private immutable _HASHED_NAME;
    bytes32 private immutable _HASHED_VERSION;
    bytes32 private immutable _TYPE_HASH;

    /* solhint-enable var-name-mixedcase */

    /**
     * @dev Initializes the domain separator and parameter caches.
     *
     * The meaning of `name` and `version` is specified in
     * https://eips.ethereum.org/EIPS/eip-712#definition-of-domainseparator[EIP 712]:
     *
     * - `name`: the user readable name of the signing domain, i.e. the name of the DApp or the protocol.
     * - `version`: the current major version of the signing domain.
     *
     * NOTE: These parameters cannot be changed except through a xref:learn::upgrading-smart-contracts.adoc[smart
     * contract upgrade].
     */
    constructor(string memory name, string memory version) {
        bytes32 hashedName = keccak256(bytes(name));
        bytes32 hashedVersion = keccak256(bytes(version));
        bytes32 typeHash = keccak256(
            "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
        );
        _HASHED_NAME = hashedName;
        _HASHED_VERSION = hashedVersion;
        _CACHED_CHAIN_ID = block.chainid;
        _CACHED_DOMAIN_SEPARATOR = _buildDomainSeparator(typeHash, hashedName, hashedVersion);
        _CACHED_THIS = address(this);
        _TYPE_HASH = typeHash;
    }

    /**
     * @dev Returns the domain separator for the current chain.
     */
    function _domainSeparatorV4() internal view returns (bytes32) {
        if (address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID) {
            return _CACHED_DOMAIN_SEPARATOR;
        } else {
            return _buildDomainSeparator(_TYPE_HASH, _HASHED_NAME, _HASHED_VERSION);
        }
    }

    function _buildDomainSeparator(
        bytes32 typeHash,
        bytes32 nameHash,
        bytes32 versionHash
    ) private view returns (bytes32) {
        return keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)));
    }

    /**
     * @dev Given an already https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct[hashed struct], this
     * function returns the hash of the fully encoded EIP712 message for this domain.
     *
     * This hash can be used together with {ECDSA-recover} to obtain the signer of a message. For example:
     *
     * ```solidity
     * bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
     *     keccak256("Mail(address to,string contents)"),
     *     mailTo,
     *     keccak256(bytes(mailContents))
     * )));
     * address signer = ECDSA.recover(digest, signature);
     * ```
     */
    function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {
        return ECDSA.toTypedDataHash(_domainSeparatorV4(), structHash);
    }
}

// File: contracts/Counters.sol


/**
 * @title Counters
 * @author Matt Condon (@shrugs)
 * @dev Provides counters that can only be incremented, decremented or reset. This can be used e.g. to track the number
 * of elements in a mapping, issuing ERC721 ids, or counting request ids.
 *
 * Include with `using Counters for Counters.Counter;`
 */
library Counters {
    struct Counter {
        // This variable should never be directly accessed by users of the library: interactions must be restricted to
        // the library's function. As of Solidity v0.5.2, this cannot be enforced, though there is a proposal to add
        // this feature: see https://github.com/ethereum/solidity/issues/4637
        uint256 _value; // default: 0
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }

    function reset(Counter storage counter) internal {
        counter._value = 0;
    }
}

// File: contracts/draft-ERC20Permit.sol

/**
 * @dev Implementation of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on `{IERC20-approve}`, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * _Available since v3.4._
 */
abstract contract ERC20Permit is ERC20, IERC20Permit, EIP712 {
    using Counters for Counters.Counter;

    mapping(address => Counters.Counter) private _nonces;

    // solhint-disable-next-line var-name-mixedcase
    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    /**
     * @dev In previous versions `_PERMIT_TYPEHASH` was declared as `immutable`.
     * However, to ensure consistency with the upgradeable transpiler, we will continue
     * to reserve a slot.
     * @custom:oz-renamed-from _PERMIT_TYPEHASH
     */
    // solhint-disable-next-line var-name-mixedcase
    bytes32 private _PERMIT_TYPEHASH_DEPRECATED_SLOT;

    /**
     * @dev Initializes the {EIP712} domain separator using the `name` parameter, and setting `version` to `"1"`.
     *
     * It's a good idea to use the same `name` that is defined as the ERC20 token name.
     */
    constructor(string memory name) EIP712(name, "1") {}

    /**
     * @dev See {IERC20Permit-permit}.
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public virtual override {
        require(block.timestamp <= deadline, "ERC20Permit: expired deadline");

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, value, _useNonce(owner), deadline));

        bytes32 hash = _hashTypedDataV4(structHash);

        address signer = ECDSA.recover(hash, v, r, s);
        require(signer == owner, "ERC20Permit: invalid signature");

        _approve(owner, spender, value);
    }

    /**
     * @dev See {IERC20Permit-nonces}.
     */
    function nonces(address owner) public view virtual override returns (uint256) {
        return _nonces[owner].current();
    }

    /**
     * @dev See {IERC20Permit-DOMAIN_SEPARATOR}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view override returns (bytes32) {
        return _domainSeparatorV4();
    }

    /**
     * @dev "Consume a nonce": return the current value and increment.
     *
     * _Available since v4.1._
     */
    function _useNonce(address owner) internal virtual returns (uint256 current) {
        Counters.Counter storage nonce = _nonces[owner];
        current = nonce.current();
        nonce.increment();
    }
}

// File: contracts/BasedWorkToken.sol

// Based Work Token - BWORK Token - Token and Mining Contract Base Network
//
// Website: https://BasedWorkToken.org/
// Github: https://github.com/BasedWorkToken/
// Discord: https://discord.gg/QrGNf47ATk/
// Twitter: https://x.com/BasedWorkToken/
//
//
// Distrubtion of Based Work Token - BWORK Token is as follows:
//
// 100% of BWORK Token is distributed using this contract which distributes tokens to users by using Proof of work and is considered a Layer 2 and v2 of 0xBitcoin allowing all 0xBitcoin to be converted to BWORK Tokens.
// Computers solve a complicated problem to gain tokens!
// 100% of 0xBitcoin accepted for BWORK Tokens
// 100% Of the Token is distributed to the users! No dev fee!
//
//
// Symbol: BWORK
// Decimals: 18
//
// Total supply: 21,000,000.000000000000000000
//   =
// 10,835,900 0xBitcoin Tokens able to transfered to BWORK Tokens.
// +
// 10,164,100 Mined over 100+ years using Bitcoins Distrubtion halvings every ~4 years. Uses Proof-oF-Work to distribute the tokens. Public Miner is available see https://dWorkToken.org 
//  
//
// No dev cut, or advantage taken at launch. Public miner available at launch. 100% of the token is given away fairly over 100+ years using Bitcoins model!
// 
// Mint 2016 answers per challenge in this cost savings Bitcoin!! Less failed transactions as the challenge only changes every 2016 answers instead of every answer.
//
// Credits: 0xBitcoin
//
// startTime =  1738771200;  //Date and time (GMT): Wednesday, Feb 5, 2025 4:00:00 PM GMT then openMining functioncan then be called and mining will have rewards, until then all rewards will be 0.






library IsContract {
    function isContract(address _addr) internal view returns (bool) {
        bytes32 codehash;
        /* solium-disable-next-line */
        assembly { codehash := extcodehash(_addr) }
        return codehash != bytes32(0) && codehash != bytes32(0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470);
    }
}



// File: contracts/utils/SafeMath.sol

library SafeMath2 {
    function add(uint256 x, uint256 y) internal pure returns (uint256) {
        uint256 z = x + y;
        require(z >= x, "Add overflow");
        return z;
    }

    function sub(uint256 x, uint256 y) internal pure returns (uint256) {
        require(x >= y, "Sub underflow");
        return x - y;
    }

    function mult(uint256 x, uint256 y) internal pure returns (uint256) {
        if (x == 0) {
            return 0;
        }

        uint256 z = x * y;
        require(z / x == y, "Mult overflow");
        return z;
    }

    function div(uint256 x, uint256 y) internal pure returns (uint256) {
        require(y != 0, "Div by zero");
        return x / y;
    }

    function divRound(uint256 x, uint256 y) internal pure returns (uint256) {
        require(y != 0, "Div by zero");
        uint256 r = x / y;
        if (x % y != 0) {
            r = r + 1;
        }

        return r;
    }
}



// File: contracts/utils/Math.sol

library ExtendedMath2 {


    //return the smaller of the two inputs (a or b)
    function limitLessThan(uint a, uint b) internal pure returns (uint c) {

        if(a > b) return b;

        return a;

    }
}





contract BasedWorkToken {



////
// Based Work Token Mining Initializations 
////

    uint public targetTime = 60*10;
    uint public startTime =  1738771200;  //Date and time (GMT): Wednesday, Feb 5, 2025 4:00:00 PM GMT

    //Events
    using SafeMath2 for uint256;
    using ExtendedMath2 for uint;
    event Mint(address indexed from, uint reward_amount, uint epochCount, bytes32 newChallengeNumber);
    event MegaMint(address indexed from, uint epochCount, bytes32 newChallengeNumber, uint NumberOfTokensMinted, uint256 TokenMultipler);

    // This mapping can be used to store combinations of challenge, user, and nonce which is the digest
    // to ensure they are not used again.
    mapping(bytes32 => mapping(bytes32 => bool) )public usedCombinations;
	
    uint public constant _totalSupply = 21000000000000000000000000;
    uint public latestDifficultyPeriodStarted2 = block.timestamp; //BlockTime of last readjustment
    uint public latestDifficultyPeriodStarted = block.number; // for readjustments
    uint public epochCount = 0;//number of 'blocks' mined

    uint public _BLOCKS_PER_READJUSTMENT = 2016; // should be 2016 blocks more inline with BTC
    uint public  _MAXIMUM_TARGET = 2**253;

    //a little number
    uint public  _MINIMUM_TARGET =  2**16;
    uint public miningTarget = 2**234;  //1 difficulty to start normalized to 0xBitcoins starting difficulty
  
    bytes32 public challengeNumber = blockhash(block.number - 1); //this is the next first challenge that will be used, challengeNumber is the main challenge to solve for
    mapping(bytes32 => bool) public usedChallenges;
    uint public rewardEra = 1;
    uint public maxSupplyForEra = (_totalSupply - _totalSupply.div( 2**(rewardEra + 1)));
    uint public reward_amount = 0;
    //Stuff for Functions
    uint public tokensMinted = 10_835_900 * 10**18;  //Tokens Minted, 0xBitcoin had 10_835_900 0xBitcoin mined so start there.
    uint public epochOld = 0;  //Epoch count at each readjustment 
    // startup locks
    bool initeds = false;
    bool locked = false;
    
    address public _BasedWorkToken_Address = address(0xc4D4FD4F4459730d176844c170F2bB323c87Eb3B); //ZeroXBitcoin Address;  //Should be 0xc4D4FD4F4459730d176844c170F2bB323c87Eb3B = Mainnet Base
      
    
	constructor(){
		latestDifficultyPeriodStarted2 = block.timestamp;
		latestDifficultyPeriodStarted = block.number;	
		challengeNumber = blockhash(block.number -1); //generate a new one so we can start with a fresh
		usedChallenges[blockhash(block.number - 1)] = true;
	}


    function calculateCompensation(uint256 multiplier) public pure returns (uint256) {
        if(multiplier < 4){
        	return 1;
        }
        return log2(multiplier/2) + 1;
    }
    
    /**
     * @dev Simple log2 implementation
     */
    function log2(uint256 x) internal pure returns (uint256) {
        uint256 n = 0;
        while (x > 1) {
            x >>= 1;
            n++;
        }
        return n;
    }
    

	

	//Starts mining after a few days period for miners to setup is done
	function openMining() public returns (bool success) {
		require(!locked, "Only allowed to run once");
		locked = true;
		require(block.timestamp >= startTime && block.timestamp <= startTime + 60* 60 * 24* 7, "Must wait until after startTime (Feb 5th 2025 @ 4PM GMT) epcohTime = 1738771200");
		challengeNumber = blockhash(block.number -1); //generate a new one so we can start fresh
        reward_amount = ( 50 * 10**18)/( 2**(rewardEra) );
		miningTarget = (2**234);  //0xBTCs starting difficulty of 1
		latestDifficultyPeriodStarted2 = block.timestamp;
		latestDifficultyPeriodStarted = block.number;	
		
		require(usedChallenges[challengeNumber] == false, "Must never have used this challenge before.");
		usedChallenges[challengeNumber] = true;
		return true;
	}


	///
	// Based Work Token Multi Minting
	///



	function multiMint_SameAddress(address mintToAddress, uint256 [] memory nonce) public {
        uint NextEpochCount = blocksToReadjust();
		uint xLoop = 0;
		uint GoodLoops = 0;
		bytes32 localChallengeNumber=challengeNumber;
		uint localMiningTarget = miningTarget;
		for (xLoop = 0; xLoop < nonce.length; xLoop++) {
		    bytes32 digest = keccak256(abi.encodePacked(localChallengeNumber, msg.sender, nonce[xLoop]));
		    uint localDigestINT = uint256(digest);
		    if (usedCombinations[localChallengeNumber][digest] || localDigestINT >= localMiningTarget) {
		        continue;
		    }
		
		    uint multiplier_local = localMiningTarget / localDigestINT;
		    uint compensation = calculateCompensation(multiplier_local);
		    GoodLoops = GoodLoops.add(compensation);
		    
	        usedCombinations[localChallengeNumber][digest] = true;
		    if (GoodLoops >= NextEpochCount) {
		    	GoodLoops = NextEpochCount;
			    break;
		    }

		  
		}

       	_startNewMiningEpoch_MultiMint_Mass_Epochs(GoodLoops, NextEpochCount);

		uint payout = GoodLoops * reward_amount;

		//if max supply for the era will be exceeded next reward round then enter the new era before that happens
		//59 is the final reward era, almost all tokens minted
		if( tokensMinted.add(payout) > maxSupplyForEra && rewardEra < 59)
		{
			rewardEra = rewardEra + 1;
			maxSupplyForEra = _totalSupply - _totalSupply.div( 2**(rewardEra + 1));
			reward_amount = ( 50 * 10**18)/( 2**(rewardEra) );
			payout = payout.div(2);
		}

        ERC20(_BasedWorkToken_Address).transfer(mintToAddress, payout);
		emit Mint(mintToAddress, payout, epochCount, localChallengeNumber );	
		
		tokensMinted = tokensMinted.add(payout);

	
	}
	
	///
	// Based Work Token Multi Minting With ReWritter for when at the end of a challenge period. Very rare usage.
	///

	function multiMint_SameAddress_2(address mintToAddress, uint256 [] memory nonce) public {
        uint NextEpochCount = blocksToReadjust();
		uint xLoop = 0;
		uint GoodLoops = 0;
		bytes32 localChallengeNumber=challengeNumber;
		uint localMiningTarget = miningTarget;
		for (xLoop = 0; xLoop < nonce.length; xLoop++) {
		    bytes32 digest = keccak256(abi.encodePacked(localChallengeNumber, msg.sender, nonce[xLoop]));
		    uint localDigestINT = uint256(digest);
		    if (usedCombinations[localChallengeNumber][digest] || localDigestINT >= localMiningTarget) {
		        continue;
		    }
		
		    uint multiplier_local = localMiningTarget / localDigestINT;
		    uint compensation = calculateCompensation(multiplier_local);
		    GoodLoops = GoodLoops.add(compensation);
		    
	        usedCombinations[localChallengeNumber][digest] = true;
		    if (GoodLoops >= NextEpochCount) {
		    	GoodLoops = NextEpochCount;
                for(uint xaa = 0; xaa<=xLoop; xaa++){
                    bytes32 digest2 = keccak256(abi.encodePacked(localChallengeNumber, msg.sender, nonce[xaa]));
                    usedCombinations[localChallengeNumber][digest2]=false;
                }
			    break;
		    }

		  
		}

       	_startNewMiningEpoch_MultiMint_Mass_Epochs(GoodLoops, NextEpochCount);

		uint payout = GoodLoops * reward_amount;

		//if max supply for the era will be exceeded next reward round then enter the new era before that happens
		//59 is the final reward era, almost all tokens minted
		if( tokensMinted.add(payout) > maxSupplyForEra && rewardEra < 59)
		{
			rewardEra = rewardEra + 1;
			maxSupplyForEra = _totalSupply - _totalSupply.div( 2**(rewardEra + 1));
			reward_amount = ( 50 * 10**18)/( 2**(rewardEra) );
			payout = payout.div(2);
		}


        ERC20(_BasedWorkToken_Address).transfer(mintToAddress, payout);

		emit Mint(mintToAddress, payout, epochCount, localChallengeNumber );	
		
		tokensMinted = tokensMinted.add(payout);

	
	}
	

	///
	// Based Work Token Single Minting
	///

	//compatibility function
	function mint(uint256 nonce, bytes32 challenge_digest) public {
		mintTo(nonce, msg.sender);
	}
	

	function mintTo(uint256 nonce, address mintToAddress) public {
		bytes32 localChallengeNumber = challengeNumber;
		bytes32 digest =  keccak256(abi.encodePacked(localChallengeNumber, msg.sender, nonce));

		uint localDigestINT = uint256(digest);
		uint localMiningTarget = miningTarget;
		
		//the digest must be smaller than the target
		require(uint256(localDigestINT) < localMiningTarget, "Digest must be smaller than miningTarget");
		require(!usedCombinations[localChallengeNumber][digest], "Must not been the first time this solve has been used");
		usedCombinations[localChallengeNumber][digest] = true;
		
		uint multiplier_local = localMiningTarget / localDigestINT;
		uint compensation = calculateCompensation(multiplier_local);
		uint local_epoch_cnt = epochCount;
       	_startNewMiningEpoch_MultiMint_Mass_Epochs(compensation, blocksToReadjust());
		local_epoch_cnt = epochCount - local_epoch_cnt;
		uint localreward = local_epoch_cnt*reward_amount;
		
		
		//if max supply for the era will be exceeded next reward round then enter the new era before that happens
		//59 is the final reward era, almost all tokens minted
		if( tokensMinted.add(localreward) > maxSupplyForEra && rewardEra < 59)
		{
			rewardEra = rewardEra + 1;
			maxSupplyForEra = _totalSupply - _totalSupply.div( 2**(rewardEra + 1));
			reward_amount = ( 50 * 10**18)/( 2**(rewardEra) );
			localreward = localreward.div(2);
		}

        
        ERC20(_BasedWorkToken_Address).transfer(mintToAddress, localreward);
        
		tokensMinted = tokensMinted.add(localreward);
		

		emit Mint(mintToAddress, localreward, epochCount, localChallengeNumber);


	}



	function blocksFromReadjust() public view returns (uint256 blocks){
		blocks = (epochCount - epochOld);
		return blocks;
	}
	

	function blocksToReadjust() public view returns (uint blocks){
		
		uint256 blktimestamp = block.timestamp;
		uint local_BLOCKS_PER_READJUSTMENT = _BLOCKS_PER_READJUSTMENT;
		uint localEpochCount = epochCount;
		uint localEpochOld = epochOld;
		
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2;
		uint adjusDiffTargetTime = targetTime * local_BLOCKS_PER_READJUSTMENT;
		
		uint MultiplierOfTime = 3;
		if(localEpochCount - localEpochOld > 0){
			
			MultiplierOfTime = (((localEpochCount - localEpochOld - 1)/(local_BLOCKS_PER_READJUSTMENT/4))+3);
		}
		
		if(MultiplierOfTime == 6){
			MultiplierOfTime=5;
		}

		uint adjustFinal = adjusDiffTargetTime * MultiplierOfTime;

		if( TimeSinceLastDifficultyPeriod2 > adjustFinal)
		{
				blocks = 1; //Complicated math not needed if only moving 1 block; otherwize, local_BLOCKS_PER_READJUSTMENT/difficulty_adjust_multiplier - ((localEpochCount - localEpochOld) % (local_BLOCKS_PER_READJUSTMENT/difficulty_adjust_multiplier));
				return (blocks);
		}else{
			    blocks = local_BLOCKS_PER_READJUSTMENT - ((localEpochCount - localEpochOld) % local_BLOCKS_PER_READJUSTMENT);
			    return (blocks);
		}
	
	}


    function seconds_Until_adjustmentSwitch() public view returns (uint secs) {
        uint256 blktimestamp = block.timestamp;
        uint256 local_BLOCKS_PER_READJUSTMENT = _BLOCKS_PER_READJUSTMENT;
        uint256 adjusDiffTargetTime = local_BLOCKS_PER_READJUSTMENT * targetTime;
        uint256 localEpochCount = epochCount;
        uint256 localEpochOld = epochOld;

        uint256 MultiplierOfTime = 3;
        if (localEpochCount - localEpochOld > 0) {
            MultiplierOfTime = (((localEpochCount - localEpochOld - 1) / (local_BLOCKS_PER_READJUSTMENT / 4)) + 3);
        }

        if (MultiplierOfTime == 6) {
            MultiplierOfTime = 5;
        }

        uint256 adjustFinal = adjusDiffTargetTime * MultiplierOfTime;

        adjusDiffTargetTime = adjustFinal + latestDifficultyPeriodStarted2;
        int useThisForTimeLeft = int256(adjusDiffTargetTime) - int256(blktimestamp);
        if (useThisForTimeLeft < 0) {
            return 0;
        }
        return adjusDiffTargetTime - blktimestamp;
    }





	function _startNewMiningEpoch_MultiMint_Mass_Epochs(uint epochsz, uint nextEpoch) internal{
	
			
		uint localEpochCount = epochCount;
		uint blocksToReadjust_local = nextEpoch;
		
        if(epochsz >= blocksToReadjust_local){
			epochsz = blocksToReadjust_local;
            epochCount = localEpochCount.add(epochsz);
            if(_totalSupply < tokensMinted){
                    reward_amount = 0;
            }
            _reAdjustDifficulty();
            
            bytes32 localChallenge = blockhash(block.number - 1);
            localChallenge = bytes32(keccak256(abi.encodePacked(localChallenge, challengeNumber)));
            require(usedChallenges[localChallenge] == false, "Must never have used this challenge before.");
            usedChallenges[localChallenge] = true;
            challengeNumber = localChallenge;
					
		}else{

            epochCount = localEpochCount.add(epochsz);
        }
				
	
    }



	function reAdjustsToWhatDifficultyAVG(uint extraTime) public view returns (uint difficulty) {
		uint blktimestamp = block.timestamp;
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2 + extraTime+1;
		uint epochTotal = epochCount - epochOld;
		uint adjusDiffTargetTime = targetTime * epochTotal+1;
		uint miningTarget2 = 0;

		//if there were less eth blocks passed in time than expected
		if( TimeSinceLastDifficultyPeriod2 < adjusDiffTargetTime )
		{
			uint excess_block_pct = (adjusDiffTargetTime.mult(100)).div( TimeSinceLastDifficultyPeriod2 );
			uint excess_block_pct_extra = excess_block_pct.sub(100).limitLessThan(1000);
			//make it harder 
			miningTarget2 = miningTarget.sub(miningTarget.div(1333).mult(excess_block_pct_extra));   //by up to 4x
		}else{
			uint shortage_block_pct = (TimeSinceLastDifficultyPeriod2.mult(100)).div( adjusDiffTargetTime );

			uint shortage_block_pct_extra = shortage_block_pct.sub(100).limitLessThan(1000); //always between 0 and 1000
			//make it easier
			miningTarget2 = miningTarget.add(miningTarget.div(333).mult(shortage_block_pct_extra));   //by up to 4x
		}

		if(miningTarget2 < _MINIMUM_TARGET) //very difficult
		{
			miningTarget2 = _MINIMUM_TARGET;
		}
		if(miningTarget2 > _MAXIMUM_TARGET) //very easy
		{
			miningTarget2 = _MAXIMUM_TARGET;
		}
		difficulty = _MAXIMUM_TARGET.div(miningTarget2);
			return difficulty;
	}


	function reAdjustsToWhatDifficulty_MaxPain_Difficulty() public view returns (uint difficulty) {
		difficulty = _MAXIMUM_TARGET.div(reAdjustsToWhatDifficulty_MaxPain_Target());
		return difficulty;
	}

	function reAdjustsToWhatDifficulty_MaxPain_Target() public view returns (uint target) {
		uint epochTotal = blocksToReadjust() + blocksFromReadjust();
		uint adjusDiffTargetTime = targetTime *  epochTotal; 
		uint256 blktimestamp = block.timestamp;
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2+1;
        uint miningTarget2 = 0;

		//if there were less eth blocks passed in time than expected
		if( TimeSinceLastDifficultyPeriod2 < adjusDiffTargetTime )
		{
			uint excess_block_pct = (adjusDiffTargetTime.mult(100)).div( TimeSinceLastDifficultyPeriod2 );
			uint excess_block_pct_extra = excess_block_pct.sub(100).limitLessThan(1000);
			//make it harder 
			miningTarget2 = miningTarget.sub(miningTarget.div(1333).mult(excess_block_pct_extra));   //by up to 4x
		}else{
			uint shortage_block_pct = (TimeSinceLastDifficultyPeriod2.mult(100)).div( adjusDiffTargetTime );

			uint shortage_block_pct_extra = shortage_block_pct.sub(100).limitLessThan(1000); //always between 0 and 1000
			//make it easier
			miningTarget2 = miningTarget.add(miningTarget.div(333).mult(shortage_block_pct_extra));   //by up to 4x
		}

		if(miningTarget2 < _MINIMUM_TARGET) //very difficult
		{
			miningTarget2 = _MINIMUM_TARGET;
		}
		if(miningTarget2 > _MAXIMUM_TARGET) //very easy
		{
			miningTarget2 = _MAXIMUM_TARGET;
		}
		//difficulty = _MAXIMUM_TARGET.div(miningTarget2);
			return miningTarget2;
	}


	function reAdjustsToWhatDifficulty_MaxPain_Difficulty_AdditionalTime(uint addTime) public view returns (uint difficulty) {
		difficulty = _MAXIMUM_TARGET.div(reAdjustsToWhatDifficulty_MaxPain_Target_AdditionalTime(addTime));
		return difficulty;
	}
	
	

	function reAdjustsToWhatDifficulty_MaxPain_Target_AdditionalTime(uint addTime) public view returns (uint target) {
		uint epochTotal =  blocksToReadjust() + blocksFromReadjust();
		uint adjusDiffTargetTime = targetTime *  epochTotal; 
		uint256 blktimestamp = block.timestamp + addTime;
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2+1;
       	uint miningTarget2 = 0;

		//if there were less eth blocks passed in time than expected
		if( TimeSinceLastDifficultyPeriod2 < adjusDiffTargetTime )
		{
			uint excess_block_pct = (adjusDiffTargetTime.mult(100)).div( TimeSinceLastDifficultyPeriod2 );
			uint excess_block_pct_extra = excess_block_pct.sub(100).limitLessThan(1000);
			//make it harder 
			miningTarget2 = miningTarget.sub(miningTarget.div(1333).mult(excess_block_pct_extra));   //by up to 4x
		}else{
			uint shortage_block_pct = (TimeSinceLastDifficultyPeriod2.mult(100)).div( adjusDiffTargetTime );

			uint shortage_block_pct_extra = shortage_block_pct.sub(100).limitLessThan(1000); //always between 0 and 1000
			//make it easier
			miningTarget2 = miningTarget.add(miningTarget.div(333).mult(shortage_block_pct_extra));   //by up to 4x
		}

		if(miningTarget2 < _MINIMUM_TARGET) //very difficult
		{
			miningTarget2 = _MINIMUM_TARGET;
		}
		if(miningTarget2 > _MAXIMUM_TARGET) //very easy
		{
			miningTarget2 = _MAXIMUM_TARGET;
		}
		//difficulty = _MAXIMUM_TARGET.div(miningTarget2);
			return miningTarget2;
	}



	function _reAdjustDifficulty() internal {
		uint256 blktimestamp = block.timestamp;
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2 +1;
		uint epochTotal = epochCount - epochOld;
		uint adjusDiffTargetTime = targetTime *  epochTotal; 
		epochOld = epochCount;

		//if there were less eth blocks passed in time than expected
		if( TimeSinceLastDifficultyPeriod2 < adjusDiffTargetTime )
		{
			uint excess_block_pct = (adjusDiffTargetTime.mult(100)).div( TimeSinceLastDifficultyPeriod2 );

			uint excess_block_pct_extra = excess_block_pct.sub(100).limitLessThan(1000);
			//make it harder 
			miningTarget = miningTarget.sub(miningTarget.div(1333).mult(excess_block_pct_extra));   //by up to 4x
		}else{
			uint shortage_block_pct = (TimeSinceLastDifficultyPeriod2.mult(100)).div( adjusDiffTargetTime );

			uint shortage_block_pct_extra = shortage_block_pct.sub(100).limitLessThan(1000); //always between 0 and 1000
			//make it easier
			miningTarget = miningTarget.add(miningTarget.div(333).mult(shortage_block_pct_extra));   //by up to 4x
		}

		latestDifficultyPeriodStarted2 = blktimestamp;
		latestDifficultyPeriodStarted = block.number;

		if(miningTarget < _MINIMUM_TARGET) //very difficult
		{
			miningTarget = _MINIMUM_TARGET;
		}
		if(miningTarget > _MAXIMUM_TARGET) //very easy
		{
			miningTarget = _MAXIMUM_TARGET;
		}
		
	}


	//Stat Functions

	function inflationMined () public view returns (uint YearlyInflation, uint EpochsPerYear, uint RewardsAtTime, uint TimePerEpoch){
		if(epochCount - epochOld == 0){
			return (0, 0, 0, 0);
		}
		uint256 blktimestamp = block.timestamp;
		uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2;

        
		TimePerEpoch = TimeSinceLastDifficultyPeriod2 / blocksFromReadjust(); 
		RewardsAtTime = reward_amount;
		uint year = 365 * 24 * 60 * 60;
		EpochsPerYear = year / TimePerEpoch;
		YearlyInflation = RewardsAtTime * EpochsPerYear;
		return (YearlyInflation, EpochsPerYear, RewardsAtTime, TimePerEpoch);
	}

	

	function toNextEraDays () public view returns (uint daysToNextEra, uint _maxSupplyForEra, uint _tokensMinted, uint amtDaily){

        (uint totalamt,,,) = inflationMined();
		(amtDaily) = totalamt / 365;
		if(amtDaily == 0){
			return(0,0,0,0);
		}
		daysToNextEra = (maxSupplyForEra - tokensMinted) / amtDaily;
		return (daysToNextEra, maxSupplyForEra, tokensMinted, amtDaily);
	}
	


	function toNextEraEpochs () public view returns ( uint epochs, uint epochTime, uint daysToNextEra){
		if(blocksFromReadjust() == 0){
			return (0,0,0);
        }
		uint256 blktimestamp = block.timestamp;
        uint TimeSinceLastDifficultyPeriod2 = blktimestamp - latestDifficultyPeriodStarted2;
		uint timePerEpoch = TimeSinceLastDifficultyPeriod2 / blocksFromReadjust();
		(uint daysz,,,) = toNextEraDays();
		uint amt = daysz * (60*60*24) / timePerEpoch;
		return (amt, timePerEpoch, daysz);
	}


	//help debug mining software
	function checkMintSolution(uint256 nonce, bytes32 challenge_digest, bytes32 challenge_number, uint testTarget) public view returns (bool success) {
		bytes32 digest = bytes32(keccak256(abi.encodePacked(challenge_number,msg.sender,nonce)));
		if(uint256(digest) > testTarget) revert();

		return (digest == challenge_digest);
	}


	//help debug mining software2
	function checkMintSolution2(uint256 nonce, bytes32 challenge_digest, bytes32 challenge_number, uint testTarget, address senda) public view returns (bytes32 success) {
		bytes32 digest = bytes32(keccak256(abi.encodePacked(challenge_number,senda,nonce)));
		if(uint256(digest) > testTarget) revert();

		return digest;
	}


	//this is a recent ethereum block hash
	function getChallengeNumber() public view returns (bytes32) {

		return challengeNumber;  

	}

	
	//the number of zeroes the digest of the PoW solution requires.  Auto adjusts
	function getMiningDifficulty() public view returns (uint) {
			return _MAXIMUM_TARGET.div(miningTarget);
	}


	function getMiningTarget() public view returns (uint) {
			return (miningTarget);
	}



	function getMiningMinted() public view returns (uint) {
		return tokensMinted;
	}

	function getCirculatingSupply() public view returns (uint) {
		return tokensMinted;
	}
	
	//21m coins total
	//reward begins at 150 and is cut in half every reward era (as tokens are mined)
	function getMiningReward() public view returns (uint) {
		//once we get half way thru the coins, only get 25 per block
		//every reward era, the reward amount halves.

		return ( 50 * 10**18)/( 2**(rewardEra) );
	}



	function getEpoch() public view returns (uint) {

		return epochCount ;

	}


	//help debug mining software
	function getMintDigest(uint256 nonce, bytes32 challenge_digest, bytes32 challenge_number) public view returns (bytes32 digesttest) {

		bytes32 digest =  keccak256(abi.encodePacked(challengeNumber, msg.sender, nonce));

		return digest;

	}



}

/*
*
* MIT License
* ===========
*
* Copyright (c) 2025 Based Work Token (BWORK)
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in all
* copies or substantial portions of the Software.   
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
*/
