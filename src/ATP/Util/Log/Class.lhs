
* Signature

> module ATP.Util.Log.Class 
>   ( Log(..)
>   , Priority(..)
>   )
> where

* Imports

> import ATP.Util.Prelude hiding (log, putStrLn)
> import qualified ATP.Util.Prelude as Prelude
> import Control.Monad.Reader (ReaderT)
> import qualified Control.Monad.State as State
> import Control.Monad.State (StateT)
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Doc, (<>))
> import qualified System.IO as IO
> import qualified System.Log.Logger as Logger
> import System.Log.Logger (Priority(..))

* Log class

While the monad requirement is not strictly needed here, (we do not
use bind or return), it is convenient since Log will always be treated
as a monad.  This means we don't have to write (Log m, Monad m) => 
when we want to define a class restriction.

> class Monad m => Log m where
>   putStrLn :: String -> m ()
>   putStrLn' :: Doc -> m ()
>   logM' :: String -> Priority -> PP.Doc -> m ()
>   logM :: String -> Priority -> String -> m ()
>   logM log p = logM' log p . PP.text
>   debugM :: String -> String -> m ()
>   debugM s = logM s DEBUG
>   debugM' :: String -> PP.Doc -> m ()
>   debugM' s = logM' s DEBUG
>   infoM :: String -> String -> m ()
>   infoM s = logM s INFO
>   infoM' :: String -> PP.Doc -> m ()
>   infoM' s = logM' s INFO
>   noticeM :: String -> String -> m ()
>   noticeM s = logM s NOTICE
>   noticeM' :: String -> PP.Doc -> m ()
>   noticeM' s = logM' s NOTICE
>   warningM :: String -> String -> m ()
>   warningM s = logM s WARNING
>   warningM' :: String -> PP.Doc -> m ()
>   warningM' s = logM' s WARNING
>   errorM :: String -> String -> m ()
>   errorM s = logM s ERROR
>   errorM' :: String -> PP.Doc -> m ()
>   errorM' s = logM' s ERROR
>   criticalM :: String -> String -> m ()
>   criticalM s = logM s CRITICAL
>   criticalM' :: String -> PP.Doc -> m ()
>   criticalM' s = logM' s CRITICAL
>   alertM :: String -> String -> m ()
>   alertM s = logM s ALERT
>   alertM' :: String -> PP.Doc -> m ()
>   alertM' s = logM' s ALERT
>   emergencyM :: String -> String -> m ()
>   emergencyM s = logM s EMERGENCY
>   emergencyM' :: String -> PP.Doc -> m ()
>   emergencyM' s = logM' s EMERGENCY

Write a log entry in the IO monad.  If we are in the "stdout" log,
don't record the priority. 

> instance Log IO where
>   putStrLn = Prelude.putStrLn
>   putStrLn' = PP.putStrLn
>   logM' log prio msg = do Logger.logM log prio (PP.render doc)
>                           --IO.hFlush IO.stdout
>     where doc = PP.vcat [ header, PP.text "  " <> msg ]
>           header = PP.brackets $ PP.text (log ++ priop)
>           priop = if log == "stdout" then "" else ": " ++ show prio

> instance Log m => Log (StateT s m) where
>   putStrLn = State.lift . putStrLn
>   putStrLn' = State.lift . putStrLn'
>   logM' log prio msg = State.lift $ logM' log prio msg

> instance Log m => Log (ReaderT r m) where
>   putStrLn = State.lift . putStrLn
>   putStrLn' = State.lift . putStrLn'
>   logM' log prio msg = State.lift $ logM' log prio msg

