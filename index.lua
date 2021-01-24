--[[

CUSTOM CAMERA IMPLEMENTATION FOR MARS: NEW WASTELAND. FEATURES FREE LOOK MODE, 3RD PERSON VIEW AND A SMOOTH CAMERA DAMP ALGORITHM

Might as well open source it, since it took me a considerable amount of time
24/01/2021
Elia171

Also available on github:
https://github.com/InvadePolandAndClaimDanzig/roblox-camera-api-Mars-NW-

  ]]

local cameraAPI = {}



-- Cache variables and shorthands, includes math functions as well

local CFRAME = CFrame.new
local ANGLES = CFrame.Angles
local FROMORIENTATION = CFrame.fromOrientation

local V3 = Vector3.new

local PI = math.pi
local TAU = math.pi * 2

local ABS = math.abs
local DEG = math.deg
local RAD = math.rad
local SQRT = math.sqrt
local CLAMP = math.clamp

local MIN = math.min
local MAX = math.max

-- Trigonometry functions
local SIN = math.sin
local COS = math.cos

local ATAN2 = math.atan2

-- Declare globals as local
local tick = tick
local workspace = workspace

-- Get services

local userInputService = game:GetService("UserInputService")
local runService = game:GetService("RunService")
local players = game:GetService("Players")

-- Input control
local SWITCH_MODE_ENUM = Enum.KeyCode.V
local FREE_VIEW_ENUM = Enum.KeyCode.C

-- Constants

local CAM_OFFSET = Vector3.new(0, 2, -1)
local CAM_OFFSET_3RD_PERSON = Vector3.new(1, 2.5, 1)
local EFFECTIVE_OFFSET = CAM_OFFSET -- current camera offset

local Y_AXIS_LOCK = 65 -- maximum angle along Y axis
local FREE_LOOK_MAX_ANGLE = 60

local X_SENSITIVITY = 0.015
local Y_SENSITIVITY = 0.075

local CAMERA_MODE_SWITCH_LERP_FACTOR = 0.3 -- speed of the camera wihle switching modes
local CAMERA_LERP_FACTOR = 0.2 -- typically between .1 and 2.5

-- Everything related to camera shake
local FULL_SHAKE_WALKSPEED = 16 -- the speed we need to reach to apply full camera shake, doesn't impact the game too much even if changed to a high value

local Y_SHAKE_FREQUENCY  	=  5		-- how frequently the camera will bounce vertically, where frequency corresponds to t * f
local Y_SHAKE_MULTIPLIER 	= .5	-- intensity multiplier

local X_SHAKE_FREQUENCY  	=  10	-- how frequently the camera will move horizontally, where frequency corresponds to t * f
local X_SHAKE_MULTIPLIER 	= .25 	-- intensity multiplier

-- Define misc variables

local currentCharacter
local currentHumanoid
local currentCamera
local currentGyro

local waist, neck

local inputListener

-- Non-static variables

local xAngle, yAngle = 0, 0
local cameraMode = 0 -- whenever the mode is set to 1, the camera will gradually snap to 3rd person
local lookAround = false
local lockXangle = 0

-- Head transparency controller
local head

local current_transparency_status = 1
local head_transparency_tween_time = 0.2 -- Time in seconds we need to completely tween the head transparency

head_transparency_tween_time = head_transparency_tween_time ^ -1 -- Expentionally invert the value

-- Motion controller

local NEAR_ZERO_FLOAT = 0.0001
local THRESHOLD = math.pow(10, 3) -- maximum  velocity
local NORMALIZED_UP = Vector3.new(0, 1, 0) -- up vector
local EMPTY_VECTOR = Vector3.new()

local m_posPosCoef, m_posVelCoef = 0, 0
local m_velPosCoef, m_velVelCoef = 0, 0

local D = 0.1 -- 0.1 by default
local P = 5 -- 5 by default

local pPos, pVel = EMPTY_VECTOR, EMPTY_VECTOR
local shakeEffect = EMPTY_VECTOR

-- Body and functions

local function lerp(a, b, f)
	return a + (b - a) * f
end

local function easeInSine(x)
	return 1 - COS((x * PI) / 2)
end

-- Calculate damped spring motion parameters
local function dampedSpringMotion(dt, angularFrequency, dampingRatio)
	
	-- Force values into legal range
	if (dampingRatio     	< 0) then dampingRatio = 0 end
	if (angularFrequency 	< 0) then angularFrequency = 0 end
	
	-- In the case the angular frequency is set to a minor value, the spring will not move and we can return identity
	if (angularFrequency < NEAR_ZERO_FLOAT) then
		m_posPosCoef = 1
		m_posVelCoef = 0
		
		m_velPosCoef = 0
		m_velVelCoef = 1
		
		return
	end
	
	if (dampingRatio > 1 + NEAR_ZERO_FLOAT) then
		-- Over damped
		local za = -angularFrequency * dampingRatio
		local zb = angularFrequency * math.sqrt(dampingRatio ^ 2 - 1)
		
		local z1, z2 = za - zb, za + zb
		local e1, e2 = math.exp(z1 * dt), math.exp(z2 * dt)
		
		local invTwoZb = 1 / (2 * zb)
		
		local e1_Over_TwoZb = e1 * invTwoZb
		local e2_Over_TwoZb = e2 * invTwoZb
		
		local z1e1_Over_TwoZb = z1 * e1_Over_TwoZb
		local z2e2_Over_TwoZb = z2 * e2_Over_TwoZb
		
		m_posPosCoef =  e1_Over_TwoZb * z2 - z2e2_Over_TwoZb + e2
		m_posVelCoef = -e1_Over_TwoZb    + e2_Over_TwoZb

		m_velPosCoef = (z1e1_Over_TwoZb - z2e2_Over_TwoZb + e2) * z2
		m_velVelCoef = -z1e1_Over_TwoZb + z2e2_Over_TwoZb
	elseif (dampingRatio < 1 - NEAR_ZERO_FLOAT) then
		-- Under damped
		local omegaZeta = angularFrequency * dampingRatio
		local alpha = angularFrequency * math.sqrt(1 - dampingRatio ^ 2)
		
		local expTerm = math.exp(-omegaZeta * dt)
		local cosTerm = math.cos(alpha * dt)
		local sinTerm = math.sin(alpha * dt)
		
		local invAlpha = 1 / alpha
		
		local expSin = expTerm * sinTerm
		local expCos = expTerm * cosTerm
		local expOmegaZetaSin_Over_Alpha = expTerm * omegaZeta * sinTerm * invAlpha
		
		m_posPosCoef = expCos + expOmegaZetaSin_Over_Alpha
		m_posVelCoef = expSin * invAlpha

		m_velPosCoef = -expSin * alpha - omegaZeta * expOmegaZetaSin_Over_Alpha
		m_velVelCoef =  expCos - expOmegaZetaSin_Over_Alpha
	else
		-- Critically damped
		local expTerm = math.exp(-angularFrequency * dt)
		local timeExp = dt * expTerm
		local timeExpFreq = timeExp * angularFrequency;
		
		m_posPosCoef = timeExpFreq + expTerm
		m_posVelCoef = timeExp

		m_velPosCoef = -angularFrequency * timeExpFreq
		m_velVelCoef = -timeExpFreq + expTerm
	end
end

local function deltaAngle(current)
	local num = current
	
	if (num > -TAU) then
		num = (num - TAU)
	end
	
	return 0
end

local function deltaAngleV3(pos1, pos2) -- A solution that somewhat solves tau motion problem
	local x = deltaAngle(pos1.X, pos2.X)
	local y = deltaAngle(pos1.Y, pos2.Y)
	local z = deltaAngle(pos1.Z, pos2.Z)
	
	return V3(x, y, z)
end

local function update(dt) -- Main calculations are done here, tasks are separated in multiple events because I consider this too expensive in term of resources
	local rootPart = currentCharacter.PrimaryPart -- Define character root part, if nil then disconnect
	
	if not rootPart then runService:UnbindFromRenderStep("HandleCamera") warn("Couldn't find character") print(debug.traceback()) return end
	
	local displaced = rootPart.CFrame -- * CAM_OFFSET -- equilibrium
	local cf = ANGLES(0, RAD(xAngle), 0) * ANGLES(RAD(yAngle), 0, 0)
	
	local rotation = ATAN2(-cf.LookVector.X, -cf.LookVector.Z)
	
	local x, y, z = cf:ToOrientation() -- goal orientation
	local cX, cY, cZ = currentCamera.CFrame:ToOrientation() -- current orientation
	
	local current = V3(cX, cY, cZ)
	local goal = V3(x, y, z)
	
	local theta = goal.Y - current.Y
	
	if (theta > PI) then
		current = current + V3(0, TAU, 0)
	elseif (theta < -PI) then
		current = current - V3(0, TAU, 0)
	end
	
	pVel = (pVel + (P * ((goal - current) + (-pVel * D))))
	pPos = (pPos + (pVel * dt))
	
	if ABS(pVel:Dot(NORMALIZED_UP)) > THRESHOLD then
		pVel = Vector3.new()
		pPos = goal
		
		warn(("Abnormal velocity, damping config : %sD ; %sP ; threshold : %s"):format(D, P, THRESHOLD))
	end
	
	local vX, vZ = rootPart.Velocity.X, rootPart.Velocity.Z
	local magnitude = (vX ^ 2 + vZ ^ 2) ^ 0.5 -- Get rid of the Y vector without loses of precision, normalize X & Z pos
	
	if (magnitude > 0.5) or currentHumanoid.MoveDirection ~= EMPTY_VECTOR then -- is moving on X-Z plane
		local t = tick()
		
		local common = magnitude / FULL_SHAKE_WALKSPEED
		
		local shakeX = COS(t * X_SHAKE_FREQUENCY) * X_SHAKE_MULTIPLIER * common
		local shakeY = ABS(SIN(t * Y_SHAKE_FREQUENCY)) * Y_SHAKE_MULTIPLIER * common
		
		local shakeV3 = V3(shakeX, shakeY, 0)
		
		shakeEffect = shakeEffect:Lerp(shakeV3, 0.25)
	else -- not moving
		shakeEffect = shakeEffect * 0.95 -- smoothly interpolate the value back to 0
	end
	
	if not lookAround then
		currentGyro.CFrame = currentGyro.CFrame:Lerp(ANGLES(0, rotation, 0), CAMERA_LERP_FACTOR) -- Apply force to match camera orientation
	end
	
	EFFECTIVE_OFFSET = EFFECTIVE_OFFSET:Lerp(cameraMode == 1 and CAM_OFFSET_3RD_PERSON or CAM_OFFSET, 0.5)
	current_transparency_status = cameraMode == 0 and MIN(current_transparency_status + dt * head_transparency_tween_time, 1) 
												  or  MAX(current_transparency_status - dt * head_transparency_tween_time, 0)
	
	if head and head.LocalTransparencyModifier ~= current_transparency_status then -- update head transparency
		-- Transparency update
		head.LocalTransparencyModifier = easeInSine(current_transparency_status)
	end
	
	currentCamera.CFrame = FROMORIENTATION(pPos.X, pPos.Y, 0) + (displaced * (EFFECTIVE_OFFSET + shakeEffect))
end

local function onInput() -- alternative to mouse moved
	local delta = userInputService:GetMouseDelta()
	local x, y = delta.X, delta.Y
	
	if lookAround then
		local min, max = lockXangle - FREE_LOOK_MAX_ANGLE, lockXangle + FREE_LOOK_MAX_ANGLE
		
		if min > max then -- invert the min-max angles in the case min is greater
			max, min = lockXangle - FREE_LOOK_MAX_ANGLE, lockXangle + FREE_LOOK_MAX_ANGLE
		end
		
		xAngle = CLAMP(xAngle - x * X_SENSITIVITY * PI, min, max)
		yAngle = CLAMP(yAngle - y * Y_SENSITIVITY * PI, -Y_AXIS_LOCK, Y_AXIS_LOCK)
	else
		xAngle = (xAngle - x * X_SENSITIVITY * PI) % 360
		yAngle = CLAMP(yAngle - y * Y_SENSITIVITY * PI, -Y_AXIS_LOCK, Y_AXIS_LOCK)
	end
end

local function mouseMoved(input, robloxHandled)
	if input.UserInputType.Value ~= 4 or robloxHandled then return end
	
	xAngle = (xAngle - input.Delta.X * X_SENSITIVITY * PI) % 360
	yAngle = CLAMP(yAngle - input.Delta.Y * Y_SENSITIVITY * PI, -Y_AXIS_LOCK, Y_AXIS_LOCK)
end

local function switchCameraRelative(bool)
	if _G.activeController and _G.activeController.controls.activeController then
		_G.activeController.controls.activeController.moveVectorIsCameraRelative = bool
		
		if not bool and currentCharacter.PrimaryPart then 
			local look = currentCharacter.PrimaryPart.CFrame.LookVector - V3(0, currentCharacter.PrimaryPart.CFrame.LookVector.Y, 0)
			
			if look.X ~= look.X or look.Z ~= look.Z then -- look for potential NaN numbers
				look = EMPTY_VECTOR
			end
			
			_G.activeController.controls.activeController.relativeTo = look
		else
			_G.activeController.controls.activeController.relativeTo = nil
		end
	else
		warn("Couldn't find activeController")
	end
end

-- Input functions

local inputStatic = {} -- contains only keyboard inputs

inputStatic["input" .. FREE_VIEW_ENUM.Value] = function()
	lockXangle = xAngle
	lookAround = not lookAround
	switchCameraRelative(not lookAround)
end

inputStatic["input" .. SWITCH_MODE_ENUM.Value] = function()
	cameraMode = cameraMode == 0 and 1 or 0
end

-- ]]

local function processInput(input, robloxHandled) -- listen for key inputs
	if input.UserInputType ~= Enum.UserInputType.Keyboard or robloxHandled then return end
	
	if inputStatic["input" .. input.KeyCode.Value] then
		inputStatic["input" .. input.KeyCode.Value]()
	end
end

local function applyTransparency()
	for i, v in pairs(currentCharacter:GetChildren()) do
		if v:IsA("BasePart") and v.Name ~= "Head" then
			local connection
			
			connection = v:GetPropertyChangedSignal("LocalTransparencyModifier"):Connect(function()
				if v.Name == "Head" and cameraMode == 1 then return end
				
				v.LocalTransparencyModifier = 0
			end)
		end
	end
end

local function setupBodyGyro(remove)
	if remove and currentGyro then currentGyro:Destroy() return end
	
	local bodyGyro = Instance.new("BodyGyro")
	
	bodyGyro.Parent = currentCharacter.PrimaryPart
	bodyGyro.D = 40
	bodyGyro.P = 10000
	bodyGyro.MaxTorque = Vector3.new(1, 1, 1) * math.huge
	
	currentGyro = bodyGyro
end

-- Module

function cameraAPI:Init(character)
	local camera = workspace.CurrentCamera
	
	-- Reset settings for free camera
	switchCameraRelative(true)
	lookAround = false
	
	-- Setup camera
	camera.CameraType = Enum.CameraType.Scriptable
	
	userInputService.MouseBehavior = Enum.MouseBehavior.LockCenter
	players.LocalPlayer.CameraMode = Enum.CameraMode.LockFirstPerson
	
	currentCamera = camera
	currentCharacter = character
	currentHumanoid = currentCharacter:WaitForChild("Humanoid")
	
	currentHumanoid.AutoRotate = false
	
	if inputListener and typeof(inputListener) == "RBXScriptConnection" then
		inputListener:Disconnect()
	end
	
	local t = runService.RenderStepped:Wait()
	local angularFrequency = (math.pi / 2) / 3 -- Full rotation in 3 seconds
	
	-- Demonstrates damping ratio effect : https://upload.wikimedia.org/wikipedia/commons/thumb/f/fd/Damping_1.svg/880px-Damping_1.svg.png
	
	applyTransparency()
	setupBodyGyro()
	dampedSpringMotion(math.min(t, 0.2), angularFrequency, 0.5)
	
	pPos = currentCharacter.PrimaryPart and Vector3.new(currentCharacter.PrimaryPart.CFrame:ToOrientation()) or Vector3.new()
	
	-- Define neck and waist attachments
	waist, neck = currentCharacter:WaitForChild("UpperTorso"):WaitForChild("Waist"),
				  currentCharacter:WaitForChild("Head")		 :WaitForChild("Neck")
	
	head = currentCharacter:WaitForChild("Head")
	
	inputListener = userInputService.InputBegan:Connect(processInput)
	
	runService:BindToRenderStep("ListenInputs", Enum.RenderPriority.Input.Value, onInput)
	runService:BindToRenderStep("HandleCamera", Enum.RenderPriority.Camera.Value, update)
end

function cameraAPI:Stop()
	
end

return cameraAPI
