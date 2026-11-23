import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLocalPartConfigBFirst
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.RealBBound

open GlobalTheory.ConeArchBCont GlobalTheory.ArchUniq GlobalTheory.ConeArchB GlobalTheory.RealWeil GlobalTheory.IndLine GlobalTheory.ThK.RealB GlobalTheory.ConeSoB GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic
open scoped Classical

theorem coneInfInt_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}, CfgB B G G₁ H H' →
    ∀ {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W},
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)}, IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei' ≠ 0 → (∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v)) →
    (∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v)) →
    ∀ {K : Subgroup (UA σ G.V'.J)}, IsStab B K →
    ∀ (μKI : Measure (KAt K (evI F))) (μI : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKI → μI.IsHaarMeasure →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F),
      ∃ g : idelesAt E (evI F) → ℝ, Integrable g μI ∧
        ∀ k ∈ KAt K (evI F), ∀ l : idelesAt E (evI F), ‖coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k l.1 y‖ ≤ g l := by
  intro F E _ _ _ _ _ σ hKP B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' he ei' ev' _ hev hloc' K hK μKI μI _ hμ f y
  have hP : GlobalTheory.FunPr.Hypotheses₂ := hKP.base
  have hM := hT.geo.hM'
  have hψ := hT.base.std
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V' _ _ hT.base hT.geo.hV'
    rwa [show K = K' from Subgroup.ext fun g => (hK g).trans (hK' g).symm]
  have hSB : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ f, e' (pure f G.M'.vac) = pure (ei' f) G₁.M'.vac := fun f => by
    rw [hloc' f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  set z := (a - (b + 2)) / 2 + 1 with hz
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μI hμ z (by omega)
  obtain ⟨s, C₄, h4⟩ := shift_decay_lin hT.base hT.geo.hV' hC.hH hC.hH' hM hT₁.geo.hM' he hei 0 0 N
  obtain ⟨s', C₃, h3⟩ := locOpInf_unif_bound_of_weil hP G.M' hT.base.cm hψ hT.weil' (isCompact_KAt hKc (evI F))
    (fun k hk => hk.2) (fun k hk => inv_mem hk) s
  set q' := s'.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ℂ)
  refine ⟨fun l => max C₄ 0 * max C₃ 0 * q' f * ((absE F E l.1 : ℝ) ^ z /
    (1 + ∑ w, ‖piInf (B.emb w) (l.1 : AE F E)‖) ^ N), hN.const_mul _, fun k hk l => ?_⟩
  set q := s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ℂ)
  set P : ℝ := (1 + ∑ w, ‖piInf (B.emb w) (l.1 : AE F E)‖) ^ N with hPdef
  have hP0 : 0 < P := pow_pos (by positivity) _
  have hn : ‖(X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z‖ = (absE F E l.1 : ℝ) ^ z := by
    rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4' := h4 (locOpInf (om' (k, 1)) f) l.1
  have h3' := h3 k hk f
  have hq0 : 0 ≤ q (locOpInf (om' (k, 1)) f) := apply_nonneg _ _
  have hq0' : 0 ≤ q' f := apply_nonneg _ _
  set S := ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' l.1))) (locOpInf (om' (k, 1)) f))
  set Y := SchwartzMap.seminorm ℂ 0 0 S
  have hY : Y ≤ max C₄ 0 * (max C₃ 0 * q' f) / P := by
    rw [le_div_iff₀ hP0, mul_comm]
    calc P * Y ≤ C₄ * q (locOpInf (om' (k, 1)) f) := h4'
      _ ≤ max C₄ 0 * q (locOpInf (om' (k, 1)) f) := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
      _ ≤ max C₄ 0 * (max C₃ 0 * q' f) := by
        refine mul_le_mul_of_nonneg_left (h3'.trans ?_) (le_max_right _ _)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq0'
  have e1 : coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν z f k l.1 y =
      ((X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) * S y := rfl
  have hA : 0 ≤ (absE F E l.1 : ℝ) ^ z := by positivity
  rw [e1, norm_mul, hn]
  calc (absE F E l.1 : ℝ) ^ z * ‖S y‖ ≤ (absE F E l.1 : ℝ) ^ z * Y :=
        mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ S y) hA
    _ ≤ (absE F E l.1 : ℝ) ^ z * (max C₄ 0 * (max C₃ 0 * q' f) / P) := mul_le_mul_of_nonneg_left hY hA
    _ = _ := by rw [hPdef]; field_simp

end GlobalTheory.ThK.RealBBound
