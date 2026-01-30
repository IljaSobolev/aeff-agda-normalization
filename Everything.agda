{-# OPTIONS --guardedness #-}

-- ORIGINAL AEFF

import AEff.AEff
import AEff.EffectAnnotations
import AEff.Finality
import AEff.Preservation
import AEff.ProcessFinality
import AEff.ProcessPreservation
import AEff.ProcessProgress
import AEff.Progress
import AEff.Renamings
import AEff.Substitutions
import AEff.Types
import AEff.Simulation

-- AEFF WITHOUT EFFECT ANNOTATIONS

import AEffBaseSN.AEffBase.Types
import AEffBaseSN.AEffBase.AEff
import AEffBaseSN.AEffBase.Renamings
import AEffBaseSN.AEffBase.Substitutions
import AEffBaseSN.AEffBase.Preservation
import AEffBaseSN.AEffBase.Progress
import AEffBaseSN.AEffBase.Finality
import AEffBaseSN.AEffBase.ProcessPreservation
import AEffBaseSN.AEffBase.ProcessProgress
import AEffBaseSN.AEffBase.ProcessFinality

-- STRONG NORMALISATION FOR AEFF WITHOUT EFFECT ANNOTATIONS

import AEffBaseSN.SubstitutionProperties
import AEffBaseSN.StronglyNormalising
import AEffBaseSN.Continuations
import AEffBaseSN.Main

-- STRONG NORMALISATION FOR AEFF WITH FINITE ANNOTATIONS

-- FLATTENED VARIANT OF THE PARALLEL PART

import AEffFinFlatSN.FiniteEffectAnnotations
import AEffFinFlatSN.AEffSequential
import AEffFinFlatSN.AEffParallelFlat
import AEffFinFlatSN.StronglyNormalising
import AEffFinFlatSN.Simulation
import AEffFinFlatSN.Main

-- TREE SHAPED VARIANT OF THE PARALLEL PART

import AEffFinTreeSN.FiniteEffectAnnotations
import AEffFinTreeSN.AEffSequential
import AEffFinTreeSN.AEffParallelTree
import AEffFinTreeSN.StronglyNormalising
import AEffFinTreeSN.Simulation
import AEffFinTreeSN.ParallelShape
import AEffFinTreeSN.Main

-- AEFF WITH REINSTALLABLE INTERRUPT HANDLERS

import AEffReinstSN.AEff
import AEffReinstSN.CoinductiveEffectAnnotations
import AEffReinstSN.Finality
import AEffReinstSN.Preservation
import AEffReinstSN.ProcessFinality
import AEffReinstSN.ProcessPreservation
import AEffReinstSN.ProcessProgress
import AEffReinstSN.Progress
import AEffReinstSN.Renamings
import AEffReinstSN.Substitutions
import AEffReinstSN.Types
import AEffReinstSN.Simulation

-- STRONG NORMALISATION FOR AEFF WITH REINSTALLABLE INTERRUPT HANDLERS

import AEffReinstSN.AEffReinstBaseSN.AEff
import AEffReinstSN.AEffReinstBaseSN.SubstitutionProperties
import AEffReinstSN.AEffReinstBaseSN.StronglyNormalising
import AEffReinstSN.AEffReinstBaseSN.Continuations
import AEffReinstSN.AEffReinstBaseSN.Main