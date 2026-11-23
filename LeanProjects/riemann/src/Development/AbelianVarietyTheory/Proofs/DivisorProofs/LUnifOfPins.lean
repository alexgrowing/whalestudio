import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JUnifAndLUnifOfTieIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TieInOfFwTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem lUnif_of_pins : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ (F : Face D A) (fw : FWTie T R κ v₀), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → BarTie fw → (∀ i, OMPins T R κ v₀ O i) → RhoGeo fw O → EquivAll T R κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.LUnif := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ O F fw hI hG hM hb hO hr ha hn
  have hT : TieIn T R κ v₀ := GlobalTheory.Div.tieIn_of_fwTie T R κ v₀ fw
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hI fw.laws hO
  have hu : JUnif T R κ v₀ := (GlobalTheory.HolDict.jUnif_and_lUnif_of_tieIn h1 h2 D G Pl0 T0 A T R κ v₀ hI hM hT hpb hn).1
  exact lUnif_of_rhoGeo_equivAll fw hM hG hb hr ha (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hI hT hpb hO) hu

end GlobalTheory.TiedUnif
