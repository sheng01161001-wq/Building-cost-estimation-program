@echo off
schtasks /Create /F /SC DAILY /ST 08:30 /TN "XiaoBangChui-Update" /TR "powershell -NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File \"%~dp0update.ps1\""
pause
