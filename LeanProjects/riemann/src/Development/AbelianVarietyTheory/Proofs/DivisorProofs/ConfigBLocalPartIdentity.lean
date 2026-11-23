import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsECAUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarMemIdelesAtOfIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEmbeddingCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLocalPartTripleIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.LeviConeB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locOp_sum {κ : Type} [Fintype κ] {v : Pl F} {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} (hT : IsLinearMap ℂ T)
    (hex : ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁, φ₁ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ φ₁) {N : ℕ} (c : Fin N → ℂ)
    (f : Fin N → (κ → Fv F v) → ℂ) (hf : ∀ i, f i ∈ SB (κ → Fv F v)) :
    locOp v T (∑ i, c i • f i) = ∑ i, c i • locOp v T (f i) := by
  classical
  suffices h : ∀ s : Finset (Fin N), locOp v T (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • locOp v T (f i) from h _
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have h := locOp_lin (v := v) hT hex 0 0 (zero_mem _) (zero_mem _)
    simpa using h
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : ∑ i ∈ s, c i • f i ∈ SB (κ → Fv F v) := sum_mem fun i _ => (SB _).smul_mem _ (hf i)
    have h := locOp_lin hT hex (c j) 1 (hf j) hs
    rw [one_smul, one_smul] at h
    rw [h, ih]

theorem dint_sum {A C : Type} [MeasurableSpace A] [MeasurableSpace C] (μK : Measure A) (μ : Measure C) {N : ℕ}
    (cf : Fin N → A → C → ℂ) (w : Fin N → ℂ) (hc1 : ∀ i k, Integrable (cf i k) μ)
    (hc2 : ∀ i, Integrable (fun k => ∫ l, cf i k l ∂μ) μK) :
    ∫ k, ∫ l, ∑ i, cf i k l * w i ∂μ ∂μK = ∑ i, (∫ k, ∫ l, cf i k l ∂μ ∂μK) * w i := by
  have e : ∀ k, ∫ l, ∑ i, cf i k l * w i ∂μ = ∑ i, (∫ l, cf i k l ∂μ) * w i := fun k => by
    rw [integral_finset_sum _ (fun i _ => (hc1 i k).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  simp_rw [e]
  rw [integral_finset_sum _ (fun i _ => (hc2 i).mul_const _)]
  exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

theorem absE_pos (t : (AE F E)ˣ) : (0 : ℝ) < absE F E t := by
  have h : absE F E t ≠ 0 := fun h => by
    have e := map_mul (absE F E) t t⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at e
    exact one_ne_zero e
  exact_mod_cast pos_iff_ne_zero.2 h

theorem const_eq (X : Chars F E) (a b : ℕ) (hlt : b + 2 < a) (hev : Even (a + (b + 2))) (t : (AE F E)ˣ) :
    fac X.α ((b : ℝ) / 2) t * (X.ν t : ℂ)⁻¹ * ((absE F E t : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) =
      fac X.β ((a : ℝ) / 2) t := by
  have h2 : 2 * ((a - (b + 2)) / 2 + 1) + b = a := by obtain ⟨r, hr⟩ := hev; omega
  have hz : (((a - (b + 2)) / 2 + 1 : ℕ) : ℝ) = (a : ℝ) / 2 - (b : ℝ) / 2 := by
    have : ((2 * ((a - (b + 2)) / 2 + 1) + b : ℕ) : ℝ) = (a : ℝ) := by rw [h2]
    push_cast at this ⊢
    linarith
  have hpos := absE_pos t
  have hr : ((absE F E t : ℝ) ^ ((b : ℝ) / 2)) * (absE F E t : ℝ) ^ ((a - (b + 2)) / 2 + 1) =
      (absE F E t : ℝ) ^ ((a : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos, hz]
    congr 1
    ring
  have hν : (X.ν t : ℂ) = (X.α t : ℂ) / (X.β t : ℂ) := by
    show ((X.α / X.β) t : ℂ) = _
    rw [MonoidHom.div_apply, Circle.coe_div]
  have hα : (X.α t : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hβ : (X.β t : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [fac, hν]
  rw [← hr, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

theorem nu_conj_inv {σ : E →ₐ[F] E} (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om') (t : (AE F E)ˣ) :
    X.ν (Units.map (cA σ : AE F E →* AE F E) t) = (X.ν t)⁻¹ := by
  obtain ⟨ξ, hξ⟩ := GlobalTheory.NuConjInv.exists_isQuad hT.base.cm
  have hα := ResEtaPow.map_conj hξ hT.chars.resα t
  have hβ := ResEtaPow.map_conj hξ hT.chars.resβ t
  simp only [Chars.ν, MonoidHom.div_apply, hα, hβ, inv_div_inv, inv_div]

end GlobalTheory.ThK.LemF.LeviConeB

open GlobalTheory.ThK.LemF.LeviConeB in

theorem GlobalTheory.ThK.LemF.coneFin_leviB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) →
      h₁ ∈ UAt σ G₁.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m)) φ) =
          fac X.β ((a : ℝ) / 2) t •
            locOp v (om₁' (1, h₁)) (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) := by
  intro hPr F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ hμK hμ t h₁ m hL
    hm hh₁ φ hφ
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have P₁' := GlobalTheory.ThK.Inhab.pairV' T₁
  have hlt : b + 2 < a := T.geo.lt
  have hev2 : Even (a + (b + 2)) := T.geo.even
  set z := (a - (b + 2)) / 2 + 1 with hzdef
  set c : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) t⁻¹ with hcdef
  have htv : t ∈ idelesAt E (evFin F v) := GlobalTheory.LeviScalarAt.scalar_mem_idelesAt_of_isLevi B H' a (a + b + 1) cfg.hH' v t h₁ m hL hm
  have hcv : c ∈ idelesAt E (evFin F v) := by
    intro u hu
    have h0 := (inv_mem htv : t⁻¹ ∈ idelesAt E (evFin F v)) u hu
    change u • ((cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) - 1) = 0
    rw [← map_one (cA σ), ← map_sub, ← map_smul, h0, map_zero]
  let c' : idelesAt E (evFin F v) := ⟨c, hcv⟩
  obtain ⟨N, f, cf, hf, hc1, hc2, hsp⟩ := GlobalTheory.T.config_b_local_part_stabilizer hPr F E σ B a b G G₁ H H' cfg e' hev ei' ev' hloc K hK X om om' om₁
    om₁' T T₁ v μK μ hμK hμ z (by omega) φ hφ
  have hT₁ : IsLinearMap ℂ (om₁' (1, h₁)) := (om₁' (1, h₁)).isLinear
  have hex₁ : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v),
      ∃ ψ₁, ψ₁ ∈ SB (Fin b × Fin (a + b) → Fv F v) ∧ Acts (evFin F v) (om₁' (1, h₁)) ψ ψ₁ := fun ψ hψ =>
    ((hA F E σ B _ _ G₁.V' G₁.W G₁.M' _ _ om₁' _ _ _ _ P₁' v).1 1 (UAtSub σ G₁.V' (evFin F v)).one_mem h₁ hh₁ ψ
      hψ).exists
  have hD0 : ∀ l : (AE F E)ˣ, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ≠ 0 := fun l =>
    mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (absE_pos l).ne'))

  have hνc : (X.ν c : ℂ) = X.ν t := by
    rw [hcdef, nu_conj_inv B G X om om' T t⁻¹, map_inv, inv_inv]
  have habc : ((absE F E c : ℝ) : ℂ) = ((absE F E t : ℝ) : ℂ)⁻¹ := by
    rw [hcdef, GlobalTheory.absE_cA_units σ t⁻¹, map_inv, NNReal.coe_inv, Complex.ofReal_inv]
  have hC : ∀ l : (AE F E)ˣ, fac X.α ((b : ℝ) / 2) t * ((X.ν (l * c) : ℂ) * ((absE F E (l * c) : ℝ) : ℂ) ^ z)⁻¹ *
      ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) = fac X.β ((a : ℝ) / 2) t := by
    intro l
    rw [← const_eq X a b hlt hev2 t, map_mul, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, hνc, habc]
    have h1 : (X.ν l : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h2 : (X.ν t : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : ((absE F E l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (absE_pos l).ne'
    have h4 : ((absE F E t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (absE_pos t).ne'
    rw [mul_pow, inv_pow, ← hzdef]
    have h5 := pow_ne_zero z h3
    have h6 := pow_ne_zero z h4
    generalize ((absE F E l : ℝ) : ℂ) ^ z = p at h5 ⊢
    generalize ((absE F E t : ℝ) : ℂ) ^ z = q at h6 ⊢
    field_simp

  have key : ∀ (k : KAt K (evFin F v)) (l : idelesAt E (evFin F v)) y,
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν z (locOp v (om' (1, m)) φ) k.1 l.1 y =
        fac X.β ((a : ℝ) / 2) t * ∑ i, cf i k (l * c') * locOp v (om₁' (1, h₁)) (f i) y := by
    intro k l y
    have e1 := GlobalTheory.T.seesaw_local_part_triple_identity hPr F E σ B a b G G₁ H H' cfg e' hev ei' ev' hloc X om om' om₁ om₁' T T₁ v t h₁ m hL hm hh₁
      k.1 (mem_KAt.1 k.2).2 l.1 φ hφ
    have e2 : ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' (l.1 * c)))) (locOp v (om' (k.1, 1)) φ)) =
        ∑ i, (((X.ν (l.1 * c) : ℂ) * ((absE F E (l.1 * c) : ℝ) : ℂ) ^ z)⁻¹ * cf i k (l * c')) • f i := by
      funext y'
      have hs := hsp k (l * c') y'
      have hcc : (c' : (AE F E)ˣ) = c := rfl
      simp only [coneFinInt, Subgroup.coe_mul, hcc] at hs
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [← Finset.mul_sum, ← hs]
      rw [mul_assoc _ (X.ν (l.1 * c) : ℂ), mul_left_comm, inv_mul_cancel₀ (hD0 (l.1 * c)), mul_one]
    simp only [coneFinInt]
    rw [e1, e2, locOp_sum hT₁ hex₁ _ f hf, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [← Finset.mul_sum, ← hC l.1]
    ring

  have hφcone : coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν z φ =
      ∑ i, (∫ k, ∫ l, cf i k l ∂μ ∂μK) • f i := by
    funext y
    simp only [coneFin]
    simp_rw [hsp]
    rw [dint_sum μK μ cf (fun i => f i y) hc1 hc2, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  funext y
  rw [hφcone, locOp_sum hT₁ hex₁ _ f hf, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp only [coneFin]
  simp_rw [key]
  have sub : ∀ k : KAt K (evFin F v), ∫ l, fac X.β ((a : ℝ) / 2) t * ∑ i, cf i k (l * c') *
      locOp v (om₁' (1, h₁)) (f i) y ∂μ = fac X.β ((a : ℝ) / 2) t * ∫ l, ∑ i, cf i k l * locOp v (om₁' (1, h₁)) (f i) y ∂μ :=
    fun k => by
      rw [integral_const_mul]
      congr 1
      exact integral_mul_right_eq_self (fun l => ∑ i, cf i k l * locOp v (om₁' (1, h₁)) (f i) y) c'
  simp_rw [sub]
  rw [integral_const_mul, dint_sum μK μ cf (fun i => locOp v (om₁' (1, h₁)) (f i) y) hc1 hc2]
  simp only [Pi.smul_apply, smul_eq_mul]

end
