scp -r src root@120.24.94.232:~/GMServer/src
scp main.go root@120.24.94.232:~/GMServer/main.go

TIME6=`date +%Y%m%d%H%M`
BACKUP_FOLDER=“../GMServer_backup$TIME6"
mkdir $BACKUP_FOLDER

cp -r src $BACKUP_FOLDER/
cp main.go $BACKUP_FOLDER/main.go
