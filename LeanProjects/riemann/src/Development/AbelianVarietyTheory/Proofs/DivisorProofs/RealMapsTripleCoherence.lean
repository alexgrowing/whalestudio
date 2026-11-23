import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseMain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_maps_triple_coherence : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a')
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E (a + a')) (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (R R₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (oa ob : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (oa' ob' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (Ra Rb Sa Sb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (ca cb da db : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xa oa oa' R Ra → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xb ob ob' R Rb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xa oa oa' R Ra ca → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xb ob ob' R Rb cb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa da → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb db →
      ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  intro hP hK _ F E _ _ _ _ _ σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db m1 m2 n1 n2 k1 k2 l1 l2
  exact GlobalTheory.ReBase.ratio_reG hP hK m1 m2 n1 n2 k1 k2 l1 l2
