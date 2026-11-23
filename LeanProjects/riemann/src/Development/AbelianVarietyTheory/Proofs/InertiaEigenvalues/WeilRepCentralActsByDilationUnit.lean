import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TupDil

theorem card_mem {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ((Nat.card (𝓞 E ⧸ PP.asIdeal) : ℕ) : 𝓞 E) ∈ PP.asIdeal := by
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem card_ne_zero {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ PP.asIdeal) ≠ 0 := by
  have := (Ideal.absNorm_eq_zero_iff (I := PP.asIdeal)).not.2 PP.ne_bot
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem om_model_eq_unit_smul_dilate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) κ ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hz
  refine GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ (GlobalTheory.OnCmp.kerDat_tuple hC.lev hC.thP t)
    ⟨t, subset_rfl⟩ _ ?_ ?_ eg eQ fg heg heQ hfg ϖ (by exact_mod_cast hϖ0) hϖ z hz
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_ne_zero PP
  · intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hPP)
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_mem PP)

end GlobalTheory.TupDil
