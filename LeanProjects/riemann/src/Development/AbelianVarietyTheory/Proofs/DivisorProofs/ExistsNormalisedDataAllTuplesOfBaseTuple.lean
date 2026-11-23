import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataGivenLevelCoeffMapsStatement
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinnedTuples

theorem exists_pins_of_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hχ hF hM hθ h1 h2 hfw i hO hG
  obtain ⟨fw⟩ := hfw
  obtain ⟨hpb, hV, hlev⟩ := GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap D G Pl0 T0 A T R κ v₀ O hL fw.laws i hO
  obtain ⟨gramR, c0R, c0L, htie⟩ := hF.tie
  obtain ⟨O', a, b, c, -⟩ := GlobalTheory.T.exists_normalisedTupleData_given_level_coeffMaps D G Pl0 T0 A T R κ v₀ hL hχ hF hM hθ ⟨fw⟩ hpb
    (GlobalTheory.TupleCover.finite_tuples R h1 h2) hG i hV (O i).lev hlev gramR c0R c0L htie
  exact ⟨O', a, b, c⟩

end GlobalTheory.PinnedTuples
