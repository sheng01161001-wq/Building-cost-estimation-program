# 小棒槌 建築估算程式:從 GitHub 下載最新版,覆蓋到本檔案所在的資料夾
$ErrorActionPreference = 'Stop'
try { [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12 } catch {}
$dest = $PSScriptRoot
$url  = 'https://github.com/sheng01161001-wq/building-cost-estimation-program/archive/refs/heads/main.zip'
$tmp  = Join-Path $env:TEMP ('xbc_' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $tmp | Out-Null
try {
  $zip = Join-Path $tmp 'main.zip'
  Write-Host '正在下載最新版...'
  Invoke-WebRequest -Uri $url -OutFile $zip -UseBasicParsing
  Expand-Archive -Path $zip -DestinationPath $tmp -Force
  $src = Get-ChildItem -Path $tmp -Directory | Select-Object -First 1
  # 覆蓋程式檔案;.bat 不覆蓋(避免正在執行的批次檔被改掉);你自己放在資料夾裡的其他檔案不會被刪除
  robocopy $src.FullName $dest /E /XF *.bat /NJH /NJS /NP /NFL /NDL | Out-Null
  if ($LASTEXITCODE -ge 8) { throw "複製檔案失敗(robocopy 代碼 $LASTEXITCODE)" }
  $line = '{0}  已更新到最新版' -f (Get-Date -Format 'yyyy-MM-dd HH:mm')
  Add-Content -Path (Join-Path $dest 'update-log.txt') -Value $line -Encoding UTF8
  Write-Host ('完成:已更新 ' + $dest)
  exit 0
} catch {
  Write-Host ('更新失敗:' + $_.Exception.Message)
  Add-Content -Path (Join-Path $dest 'update-log.txt') -Value ('{0}  更新失敗:{1}' -f (Get-Date -Format 'yyyy-MM-dd HH:mm'), $_.Exception.Message) -Encoding UTF8
  exit 1
} finally {
  Remove-Item -Path $tmp -Recurse -Force -ErrorAction SilentlyContinue
}
