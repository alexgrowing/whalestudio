import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVacuumFixedByStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationInfinitePartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalZetaIntegralUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove

noncomputable section

namespace GlobalTheory.LemUB

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem coneFin_vac (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (hG₁ : G₁.IsGood B)
    {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    {ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b))}
    {ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ}
    (hei : ei' ≠ 0) (hev : ∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v))
    (hpure : ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v))
    {K : Subgroup (UA σ G.V'.J)} (hK : IsStab B K) {v : Pl F} (hv : v ∉ X.T)
    {μK : Measure (KAt K (evFin F v))} (hμK : IsNormK K (evFin F v) μK)
    {μ : Measure (idelesAt E (evFin F v))} (hμ : IsNormE E v μ) :
    coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) =
      unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v • G₁.M'.vac v := by
  have hB := hT.base
  have hfix := (GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer B G X om om' hT v hv).2 K hK
  have hSB := (hT.geo.hM'.vac v).1
  have h𝔟 := (GlobalTheory.T.adapted_plane_hermitian_ideal_coprime F E σ B H G.V' G₁.V' 0 (b + 1) _ _ hB hT.geo.hV' hC.hH (by omega) (by omega)).1
  have h𝔠 := (GlobalTheory.T.adapted_plane_skew_ideal_coprime F E σ B H' G.W G₁.W a (a + b + 1) _ _ hB hT.geo.hW hC.hH' (by omega) (by omega)).1
  have hunr : ∀ w ∈ aboveF (L := E) F v, UnrAt X.ν w := fun w hw => by
    have hw' : w ∉ above E (X.T : Set (Pl F)) := fun h => hv (by
      have h1 : w.under (𝓞 F) ∈ (X.T : Set (Pl F)) := h
      rwa [GlobalTheory.LFun.mem_aboveF.1 hw] at h1)
    rw [Chars.ν, div_eq_mul_inv]
    exact (hT.chars.unrα w hw').mul (hT.chars.unrβ w hw').inv
  have htate := GlobalTheory.T.local_zeta_integral_unramified X.ν v hunr μ hμ _ (mul_ne_zero (inv_ne_zero h𝔟) (conjI_ne_zero σ h𝔠)) ((a - (b + 2)) / 2 + 1) (by omega)
  funext y
  rw [coneFin_of_fixed hμK hSB hfix y]
  have e1 : ∀ l : idelesAt E (evFin F v),
      ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l.1))) (G.M'.vac v)) y * (X.ν l.1 : ℂ) *
        ((absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) =
      G₁.M'.vac v y * (if compFin F E v (l.1 : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) then
        (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) else 0) := fun l => by
    rw [GlobalTheory.T.config_b_evaluation_infinite_part B G G₁ H H' hB hT.geo hG₁ hC e' he' ei' ev' hei hev hpure v l.1 l.2]
    split_ifs <;> simp [mul_assoc]
  rw [integral_congr_ae (Eventually.of_forall e1), integral_const_mul, htate, Pi.smul_apply, smul_eq_mul, mul_comm]

end GlobalTheory.LemUB

end
