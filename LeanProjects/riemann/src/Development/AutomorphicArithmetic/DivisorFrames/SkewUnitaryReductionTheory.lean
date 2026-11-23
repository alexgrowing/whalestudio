import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AutomorphicArithmetic.LocalEmbeddings.LeviRedDef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

section
open GlobalTheory.LeviRed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem absE_rE (h : IsCMExt F E σ) {s : ℝ} (hs : 0 < s) (u : (AF F ⊗[F] E)ˣ) (hu : u.1 = rE F E s) :
    (GlobalTheory.Doubling.absE F E u : ℝ) = s ^ (2 * Fintype.card (InfinitePlace F)) := by
  have hN : Algebra.norm (AF F) u.1 = GlobalTheory.TorusTheta.infScale F s ^ 2 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
    rw [hu, rE, Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v u) = 1 := fun v => by
    have : evFin F v (GlobalTheory.TorusTheta.infScale F s) = 1 := rfl
    rw [GlobalTheory.Doubling.absEv_unitFin, hN, map_pow, this]
    simp
  have hinf : ∀ w, (GlobalTheory.Doubling.absEw F E w (GlobalTheory.Doubling.unitInf F E w u) : ℝ) = s ^ 2 := fun w => by
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    have e : infEmb τ (GlobalTheory.Doubling.unitInf F E w u).1 = s := by
      rw [← GlobalTheory.TorusMat.piInf_infScale h τ s]
      change infEmb τ (compInf F E w u.1) = _
      rw [hu]
      rfl
    rw [GlobalTheory.Doubling.absEw_eq_sq h τ, e, NNReal.coe_pow, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [GlobalTheory.Doubling.absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod,
    Finset.prod_congr rfl fun w _ => hinf w, Finset.prod_const, Finset.card_univ, pow_mul]

private theorem exists_unit (h : IsCMExt F E σ) {s : ℝ} (hs : 0 < s) :
    ∃ u : (AE F E)ˣ, u.1 = algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s) ∧ s ≤ 1 + (absE F E u : ℝ) := by
  let u : (AF F ⊗[F] E)ˣ := ⟨rE F E s, rE F E s⁻¹, by rw [← rE_mul, mul_inv_cancel₀ hs.ne', rE_one],
    by rw [← rE_mul, inv_mul_cancel₀ hs.ne', rE_one]⟩
  refine ⟨u, rfl, ?_⟩
  rw [absE_rE h hs u rfl]
  have hm : 2 * Fintype.card (InfinitePlace F) ≠ 0 := Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero
  rcases le_total s 1 with h1 | h1
  · exact h1.trans (le_add_of_nonneg_right (by positivity))
  · exact (le_self_pow₀ h1 hm).trans (le_add_of_nonneg_left zero_le_one)

end

theorem UpperTheory.skew_unitary_reduction_theory :
    GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
                 ∃ (q : ℕ) (x : Fin q → Fin n → E) (Cc : Set (UA σ W.J)) (C : ℝ) (A : ℕ), (∀ i, x i ≠ 0) ∧ IsCompact Cc ∧
                   ∀ g : UA σ W.J, ∃ γ ∈ ratU σ W.J, ∃ (τ : Fin q → (AE F E)ˣ) (a κ : UA σ W.J),
                     (∀ i, mat a *ᵥ incV F (x i) = (τ i).1 • incV F (x i)) ∧ κ ∈ Cc ∧ γ * g = a * κ ∧
                     (ht (γ * g) : ℝ) ≤ C * (∏ i, (1 + (absE F E (τ i) : ℝ))) ^ A := by
  intro hP F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨e₀, he₀, he₀s⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ' : IsHermND σ (e₀ • X.J.map σ) := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B n X r s hX e₀ he₀ he₀s
  let e : UA σ X.J ≃* GAd σ (e₀ • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ he₀)
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨q, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, -, hcov, ⟨C₀, hC₀, hconj⟩, -⟩ := hP F E σ hcm n _ hJ' q Xf Yf hW
  have hc'0 : 0 < min 1 c ^ q := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hh0⟩ := GlobalTheory.T.siegel_set_archimedean_norm_bound F E σ hcm n _ q Xf Yf _ hc'0
  have hh : ∀ t : Fin q → ℝ, (∀ i, min 1 c ^ q ≤ t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ _ Xf Yf t a →
      (height σ _ a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah := fun t ht a ha =>
    hh0 t ht a ha.1 (GlobalTheory.T.torus_element_archimedean_matrix_form F E σ hcm n _ hJ' q Xf Yf hW t (fun i => hc'0.trans_le (ht i)) a ha)
  let mul2 : GAd σ (e₀ • X.J.map σ) × GAd σ (e₀ • X.J.map σ) → GAd σ (e₀ • X.J.map σ) :=
    fun p => p.1 * p.2
  have hCK : IsCompact (mul2 '' (C₀ ×ˢ (K : Set (GAd σ (e₀ • X.J.map σ))))) :=
    (hC₀.prod hK).image continuous_mul
  have hhc : Continuous fun g : GAd σ (e₀ • X.J.map σ) => (height σ (e₀ • X.J.map σ) g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨Bd, hBd⟩ := (hCK.image hhc).bddAbove
  have hx0 : ∀ i, (fun k => Xf k i) ≠ 0 := fun i h0 => by
    have h1 := congrFun (congrFun hW.xy i) i
    have h2 : ∀ k, Xf k i = 0 := fun k => congrFun h0 k
    simp [Matrix.mul_apply, Formalism.UG.cT, h2] at h1
  refine ⟨q, fun i k => Xf k i, e.symm '' (mul2 '' (C₀ ×ˢ (K : Set _))),
    max Ch 0 * 2 ^ Ah * max Bd 0, Ah, hx0, hCK.image he', fun g => ?_⟩
  obtain ⟨γ, hγ, s', ⟨p, hp, t, htc, a, ha, k, hk, rfl⟩, hgs⟩ := hcov (e g)
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
  have hmem : a⁻¹ * p * a * k ∈ mul2 '' (C₀ ×ˢ (K : Set _)) := ⟨(a⁻¹ * p * a, k), ⟨hconj p hp t htc a ha, hk⟩, rfl⟩
  choose τ hτ hτle using fun i => exists_unit hcm (htc.1 i)
  have heq : (e.symm γ)⁻¹ * g = e.symm a * e.symm (a⁻¹ * p * a * k) := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hgs]
    group
  refine ⟨(e.symm γ)⁻¹, inv_mem hr, τ, e.symm a, e.symm (a⁻¹ * p * a * k), fun i => funext fun j => ?_,
    ⟨_, hmem, rfl⟩, heq, ?_⟩
  · have h1 := congrFun (congrFun (GlobalTheory.TorusMat.isTorusElt_mat F E σ hcm n _ q Xf Yf t htc.1 a ha).1 j) i
    rw [Matrix.mul_diagonal, ← hτ, mul_comm] at h1
    exact h1
  · rw [heq]
    have h1 : (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤
        (height σ _ a : ℝ) * (height σ _ (a⁻¹ * p * a * k) : ℝ) := by
      exact_mod_cast heightGL_mul_le F (e.symm a).1 (e.symm (a⁻¹ * p * a * k)).1
    have h2 := hh t (GlobalTheory.SiegelHt.cone_low hc htc) a ha
    have h3 : (height σ _ (a⁻¹ * p * a * k) : ℝ) ≤ max Bd 0 :=
      (hBd ⟨_, hmem, rfl⟩).trans (le_max_left _ _)
    have h4 : (0 : ℝ) ≤ height σ _ a := NNReal.coe_nonneg _
    have h5 : (0 : ℝ) ≤ height σ _ (a⁻¹ * p * a * k) := NNReal.coe_nonneg _
    have h6 : (0 : ℝ) ≤ ∏ i, t i := Finset.prod_nonneg fun i _ => (htc.1 i).le
    have h7 : ∏ i, t i ≤ ∏ i, (1 + (absE F E (τ i) : ℝ)) :=
      Finset.prod_le_prod (fun i _ => (htc.1 i).le) fun i _ => hτle i
    have h8 : (1 : ℝ) ≤ ∏ i, (1 + (absE F E (τ i) : ℝ)) :=
      (Finset.prod_const_one (s := Finset.univ)).ge.trans
        (Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (NNReal.coe_nonneg _))
    have h9 : (height σ _ a : ℝ) ≤ max Ch 0 * (2 * ∏ i, (1 + (absE F E (τ i) : ℝ))) ^ Ah :=
      h2.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity)
        (le_max_right _ _))
    calc (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤ _ := h1
      _ ≤ (max Ch 0 * (2 * ∏ i, (1 + (absE F E (τ i) : ℝ))) ^ Ah) * max Bd 0 := mul_le_mul h9 h3 h5 (h4.trans h9)
      _ = _ := by rw [mul_pow]; ring
