-- This is to create an NFData instance
-- for number types and the Value class
-- in order to be able to evaluate them fully
-- by using force in Control.DeepSeq.
-- That will be necessary
-- for writing the interruption mechanism
-- in Shell.Interaction.
{-# OPTIONS --erased-matches #-}

module HaskellInstance.NFData where
{-# FOREIGN AGDA2HS {-# LANGUAGE DeriveGeneric, StandaloneDeriving, ScopedTypeVariables #-} #-}

-- adding these imports to sign
-- this depends on them
import Implementation.Frac
import Implementation.Dyadic
import Tool.ErasureProduct
import RealTheory.Completion
import Shell.Value

{-# FOREIGN AGDA2HS
import GHC.Generics (Generic, Generic1)
import Control.DeepSeq

import Implementation.Frac
import Implementation.Dyadic
import Tool.ErasureProduct
import RealTheory.Completion
import Shell.Value

deriving instance Generic (Frac a)
deriving instance Generic1 Frac
instance NFData a => NFData (Frac a)
instance NFData1 Frac

-- we need this for PosRationals
deriving instance Generic (Σ0 a)
deriving instance Generic1 Σ0
instance NFData a => NFData (Σ0 a)
instance NFData1 Σ0

deriving instance Generic Dyadic
instance NFData Dyadic

deriving instance Generic (C a)
deriving instance Generic1 C
instance NFData a => NFData (C a)
-- instance NFData1 C -- (->) PosRational has no NFData1 instance

deriving instance Generic (Value a)
deriving instance Generic1 Value
instance NFData a => NFData (Value a)
instance NFData1 Value

#-}
