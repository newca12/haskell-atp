
Logging utilities.

* Signature

> module ATP.Util.Log
>   ( module ATP.Util.Log.Class
>   , initialize
>   , stdout
>   , logFileName
>   , readPrio
>   , setLevel
>   , defaultPrio
>   )
> where

* Imports

> import Prelude hiding (log)
> import qualified Directory
> import ATP.Util.Log.Class
> import qualified IO 
> import qualified System.Log.Handler.Simple as S
> import qualified System.Log.Logger as Log
> import qualified System.IO.UTF8 as S

* Implementation

> type Handler = S.GenericHandler IO.Handle 

Parse a priority.

> readPrio :: String -> Maybe Priority
> readPrio s | s == "debug" = Just DEBUG
>            | s == "info" = Just INFO
>            | s == "notice" = Just NOTICE
>            | s == "warning" = Just WARNING
>            | s == "error" = Just ERROR
>            | s == "critical" = Just CRITICAL
>            | s == "alert" = Just ALERT
>            | s == "emergency" = Just EMERGENCY
>            | otherwise = Nothing

Print to both stdout and the log.

> stdout :: String -> IO ()
> stdout s = do logM "stdout" INFO s
>               S.putStrLn s

ATP starts logging with the default priority.

> defaultPrio :: Priority
> defaultPrio = WARNING

Log output to logFileName

> logFileName :: String
> logFileName = "imogen.log"

| Initialize the log file

initialize prio file term

If file is True, log all messages >= prio to the log file.
If term is True, also log all messages >= prio to stdout.

We set two handlers under the global logger.  The file handler logs to
a file.  Its priority is set at DEBUG.  Thus, it will get all messages
that can get by the logger.  The terminal handler logs to stdout, and
has priority given by an input parameter that defaults to WARNING.
Thus, no debug messages will ever go to the terminal unless they can
get through the logger.  

> initialize :: Priority -> Bool -> Bool -> IO ()
> initialize prio file term = 
>   let update = Log.updateGlobalLogger Log.rootLoggerName in
>   do -- Erase the default stderr handler.
>      update $ Log.setHandlers ([] :: [Handler])
>      -- Create the terminal handler.  
>      let termprio = if term then prio else defaultPrio
>      tout <- S.streamHandler IO.stdout termprio
>      update $ Log.addHandler tout
>      -- Set the logger priority
>      update $ Log.setLevel prio
>      -- If we want file output, open a handler to the log file
>      if file 
>        then do
>          -- Remove existing log file
>          logExists <- Directory.doesFileExist logFileName
>          if logExists then Directory.removeFile logFileName else return ()
>          -- Open new log file
>          handler <- S.fileHandler logFileName DEBUG
>          -- Add our handler
>          update $ Log.addHandler handler
>        else return ()

Update the logging priority for a given logger.  Note that we
set both the global and the file log prioriteies.

> setLevel :: String -> Priority -> IO ()
> setLevel log = Log.updateGlobalLogger log . Log.setLevel

