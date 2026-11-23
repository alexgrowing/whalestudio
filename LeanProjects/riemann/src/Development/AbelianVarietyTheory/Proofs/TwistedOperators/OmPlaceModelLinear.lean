import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv in
open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm in

theorem om_placeModel_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∃ r : ℝ, 0 < r ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = ((r : ℂ) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he _ ha Tm hTm g h hg hh x y hx hy
  have orth : ∀ b : AE D, IsSplitIdem D b → GlobalTheory.PlaceModelSum.IsOrthSum b := fun b hb =>
    ⟨Unit, {()}, fun _ => b, fun _ _ => hb, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => b) ()).symm⟩
  have ho := orth e he
  rcases ha with ha | ha
  · rw [ha] at hTm ⊢
    refine ⟨modFac S T x y, modFac_pos S T x y, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho he.2.1 (base_theta hB) hB.2.2.2.2.2.lat one_ne_zero hTm hg hh hx hy Φ hΦ,
      fac, mul_comm]
  · rw [ha] at hTm ⊢
    have ho' := ho.conj
    have sc : ∀ (V : HSp D) (k : GA D V), SuppAt e V k → SuppAt (cA D e) V k := fun V k hk i j => by
      rw [GlobalTheory.SplitOnto.cA_cA, add_comm]; exact hk i j
    have dx := det_conj ho'.idem hx
    have dy := det_conj ho'.idem hy
    refine ⟨modFac S T (detAt _ ho'.idem S g) (detAt _ ho'.idem T h), modFac_pos S T _ _, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho' (by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, he.2.1]) (base_theta hB)
      hB.2.2.2.2.2.lat one_ne_zero hTm (sc S g hg) (sc T h hh) (isDetAt_detAt _ ho'.idem S g)
      (isDetAt_detAt _ ho'.idem T h) Φ hΦ, fac, mul_comm, splitFacO, splitFacO,
      GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resT _ _ dx, GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _ dy]

end GlobalTheory.PlaceTensor
