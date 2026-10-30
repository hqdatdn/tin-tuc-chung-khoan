# Register a Windows scheduled task that runs tin_tuc.py every 10 minutes (hidden, no console window).
# Run once:  powershell -ExecutionPolicy Bypass -File dang_ky_tu_dong.ps1
# Remove:    Unregister-ScheduledTask -TaskName TinTucChungKhoan -Confirm:$false
$pythonw = (Get-Command pythonw).Source
$script = Join-Path $PSScriptRoot "tin_tuc.py"
$action = New-ScheduledTaskAction -Execute $pythonw -Argument "`"$script`"" -WorkingDirectory $PSScriptRoot
$trigger = New-ScheduledTaskTrigger -Once -At (Get-Date) -RepetitionInterval (New-TimeSpan -Minutes 10)
$settings = New-ScheduledTaskSettingsSet -StartWhenAvailable -DontStopIfGoingOnBatteries -AllowStartIfOnBatteries -ExecutionTimeLimit (New-TimeSpan -Minutes 5)
Register-ScheduledTask -TaskName "TinTucChungKhoan" -Action $action -Trigger $trigger -Settings $settings -Force | Out-Null
Write-Host "OK: TinTucChungKhoan runs every 10 minutes."
