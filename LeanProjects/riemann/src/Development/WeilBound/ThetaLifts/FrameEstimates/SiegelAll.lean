import Development.WeilBound.ThetaLifts.FrameEstimates.LintegralLeOfCover
import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt

noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def ratOf (H : Subgroup (GL (Fin n) (AE F E))) : Subgroup H :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H

theorem countable_ratOf (H : Subgroup (GL (Fin n) (AE F E))) : Countable (ratOf H) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have : Countable (GL (Fin n) E) := Units.val_injective.countable
  have : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
    (MonoidHom.rangeRestrict_surjective _).countable
  exact Function.Injective.countable (f := fun γ : ratOf H =>
    (⟨γ.1.1, γ.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
    fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))

theorem ratPts_eq_ratOf : ratPts σ J = ratOf (HR (AF F) σ J) := by
  have : Nontrivial (AE F E) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    exact ((infEmb τ).comp (compInf F E w)).domain_nontrivial
  ext g
  refine ⟨fun ⟨δ, _, hδ⟩ => ⟨δ, hδ⟩, fun ⟨δ, hδ⟩ => ⟨δ, ?_, hδ⟩⟩
  show cT (σ : E →+* E) δ.1 * J * δ.1 = J
  apply Matrix.map_injective (inclR (F := F) (E := E) (AF F)).injective
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have e : δ.1.map (inclR (F := F) (AF F)) = (matHom _ σ J g).1 := congrArg Units.val hδ
  rw [← e] at hg
  simp only [Matrix.map_mul]
  exact hg

theorem siegel_GAd (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J} (hadd : ∀ s t, a (s + t) = a s * a t) (hcont : Continuous a)
    (htor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)) :
    (∃ Ω : Set (GAd σ J), IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ t ∈ Cone r, ∃ κ ∈ Ω, γ * g = a t * κ) ∧
    (∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratPts σ J) D μ →
      ∃ (K : ℝ≥0∞) (Ω : Set (GAd σ J)), K < ⊤ ∧ IsCompact Ω ∧ ∀ φ : (Fin r → ℝ) → ℝ≥0∞, Measurable φ →
        ∀ f : GAd σ J → ℝ≥0∞, Measurable f → (∀ γ ∈ ratPts σ J, ∀ g, f (γ * g) = f g) →
          (∀ t ∈ Cone r, ∀ κ ∈ Ω, f (a t * κ) ≤ φ t) →
          ∫⁻ g in D, f g ∂μ ≤ K * ∫⁻ t in Cone r, φ t * ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n t)))) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ t ∈ Cone r, (height σ J (a t) : ℝ) ≤ C * Real.exp (k * ∑ i, t i) ∧
      ∀ γ ∈ ratPts σ J, Real.exp (∑ i, t i) ≤ C * (height σ J (γ * a t) : ℝ) ^ k := by
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C, hC, hconj⟩, hμ, ⟨C₁, A, hht⟩, -⟩ := hS F E σ h n J hJ r X Y hW
  have hΩ' : IsCompact ((fun g => a (-shf r c) * g) '' (C * (K : Set (GAd σ J)))) :=
    (hC.mul hK).image (continuous_const.mul continuous_id)
  have hdec : ∀ p ∈ Ω, ∀ u ∈ cone r c, ∀ b, IsTorusElt σ J X Y u b → ∀ k ∈ K,
      ∃ κ ∈ (fun g => a (-shf r c) * g) '' (C * (K : Set (GAd σ J))),
        p * b * k = a ((fun i => Real.log (u i)) + shf r c) * κ := fun p hp u hu b hb k hk => by
    have e : a (fun i => Real.log (u i)) = b := isTorusElt_unique h hJ hW (by
      simpa only [Real.exp_log (hu.1 _)] using htor fun i => Real.log (u i)) hb
    refine ⟨_, ⟨_, ⟨_, hconj p hp u hu b hb, k, hk, rfl⟩, rfl⟩, ?_⟩
    rw [← mul_assoc, ← hadd, add_neg_cancel_right, e]
    group
  refine ⟨⟨_, hΩ', fun g => ?_⟩, fun μ D h1 h2 => ?_, ?_⟩
  · obtain ⟨γ, hγ, _, ⟨p, hp, u, hu, b, hb, k, hk, rfl⟩, rfl⟩ := hcov g
    obtain ⟨κ, hκ, e⟩ := hdec p hp u hu b hb k hk
    exact ⟨γ⁻¹, inv_mem hγ, _, log_mem_Cone hc hu, κ, hκ, by rw [inv_mul_cancel_left, e]⟩
  · obtain ⟨-, C₂, hC₂⟩ := hμ μ h1
    refine ⟨C₂ * ENNReal.ofReal (Real.exp (2 * Module.finrank ℚ F * rho2 n (shf r c))), _,
      ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top, hΩ', fun φ hφ f hf hi hb => ?_⟩
    have : Countable (ratPts σ J) := ratPts_eq_ratOf (σ := σ) (J := J) ▸ countable_ratOf _
    refine (lintegral_le_of_cover (ratPts σ J) μ h2 hcl.measurableSet (fun g => ?_) hf hi).trans
      ((hC₂ f (fun u => φ ((fun i => Real.log (u i)) + shf r c)) (hφ.comp ?_) fun p hp u hu b hb' k hk => ?_).trans ?_)
    · obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov g
      exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
    · exact (measurable_pi_lambda _ fun i => (measurable_pi_apply i).log).add_const _
    · obtain ⟨κ, hκ, e⟩ := hdec p hp u hu b hb' k hk
      rw [e]
      exact hb _ (log_mem_Cone hc hu) κ hκ
    · have e : (Module.finrank ℚ E : ℝ) = 2 * Module.finrank ℚ F := by
        rw [← Module.finrank_mul_finrank ℚ F E, h.2.2.1]
        push_cast
        ring
      rw [e, mul_assoc]
      exact mul_le_mul_right (cone_integral_le F n r hc φ) _
  · obtain ⟨C₃, k₃, h₃⟩ := le_exp_of_add (height σ J) (height_mul_le σ J) a hadd ((continuous_height_GAd σ J).comp hcont)
    obtain ⟨-, -, -, ⟨p, hp, -⟩, -⟩ := hcov 1
    obtain ⟨B, hB⟩ := height_bddAbove_of_isCompact σ J hC
    set B' := height σ J (a (shf r c)) with hB'
    refine ⟨max (max C₃ 0) ((B' * B * C₁ * (B' * B) ^ A : ℝ≥0) ^ r), max k₃ (A * r), fun t ht => ⟨?_, fun γ hγ => ?_⟩⟩
    · have h0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht.2 i
      refine (h₃ t ht.2).trans ?_
      refine mul_le_mul ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_le_exp.2 ?_) (by positivity)
        ((le_max_right _ _).trans (le_max_left _ _))
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left _ _) h0
    · have hu := exp_mem_cone hc ht
      have hκ := hB _ (hconj p hp _ hu _ (htor _))
      set κ := (a (t + shf r c))⁻¹ * p * a (t + shf r c) with hκ'
      have e : p * a (t + shf r c) * 1 = a t * (a (shf r c) * κ) := by
        rw [← mul_assoc, ← hadd, hκ']; group
      have h4 := hht _ ⟨p, hp, _, hu, _, htor _, 1, one_mem K, rfl⟩ γ hγ
      rw [e] at h4
      have h5 : height σ J (a (shf r c) * κ) ≤ B' * B := (height_mul_le σ J _ _).trans (mul_le_mul_right hκ _)
      have h6 : height σ J (a t) ≤ B' * B * C₁ * (B' * B) ^ A * height σ J (γ * a t) ^ A :=
        calc height σ J (a t) = height σ J (a t * (a (shf r c) * κ) * (a (shf r c) * κ)⁻¹) := by
              rw [mul_inv_cancel_right]
          _ ≤ C₁ * height σ J (γ * (a t * (a (shf r c) * κ))) ^ A * (B' * B) :=
              (height_mul_le σ J _ _).trans (mul_le_mul' h4 (by rwa [height_inv]))
          _ ≤ C₁ * (height σ J (γ * a t) * (B' * B)) ^ A * (B' * B) := by
              gcongr
              rw [← mul_assoc]
              exact (height_mul_le σ J _ _).trans (mul_le_mul_right h5 _)
          _ = _ := by ring
      have h7 : Real.exp (∑ i, t i) ≤ (height σ J (a t) : ℝ) ^ r := by
        rw [Real.exp_sum]
        refine (Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ =>
          le_height_of_isTorusElt hW (htor t) i).trans (le_of_eq ?_)
        simp
      have h8 : (1 : ℝ) ≤ height σ J (γ * a t) := by exact_mod_cast one_le_height σ J _
      refine h7.trans ((pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h6) r).trans ?_)
      generalize height σ J (γ * a t) = x at h8 ⊢
      generalize B' * B * C₁ * (B' * B) ^ A = y
      rw [NNReal.coe_mul, NNReal.coe_pow, mul_pow, ← pow_mul]
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h8 (le_max_right _ _)) (by positivity)
        ((le_max_right _ _).trans (le_max_left _ _))

theorem siegel_subgroup (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) :
    letI : MeasurableSpace H := borel H
    ∃ a : (Fin r → ℝ) → H, (∀ s t, a (s + t) = a s * a t) ∧ Continuous a ∧ (∀ t,
      (a t).1.1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))) ∧
      (a t).1.1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))) ∧
      ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (a t).1.1 *ᵥ incV F z = incV F z) ∧
    (∃ Ω : Set H, IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratOf H, ∃ t ∈ Cone r, ∃ κ ∈ Ω, γ * g = a t * κ) ∧
    (∀ (μ : Measure H) (D : Set H), μ.IsHaarMeasure → IsFundamentalDomain (ratOf H) D μ →
      ∃ (K : ℝ≥0∞) (Ω : Set H), K < ⊤ ∧ IsCompact Ω ∧ ∀ φ : (Fin r → ℝ) → ℝ≥0∞, Measurable φ →
        ∀ f : H → ℝ≥0∞, Measurable f → (∀ γ ∈ ratOf H, ∀ g, f (γ * g) = f g) →
          (∀ t ∈ Cone r, ∀ κ ∈ Ω, f (a t * κ) ≤ φ t) →
          ∫⁻ g in D, f g ∂μ ≤ K * ∫⁻ t in Cone r, φ t * ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n t)))) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ t ∈ Cone r, (heightGL F (a t).1 : ℝ) ≤ C * Real.exp (k * ∑ i, t i) ∧
      ∀ γ ∈ ratOf H, Real.exp (∑ i, t i) ≤ C * (heightGL F (γ * a t).1 : ℝ) ^ k := by
  subst hH
  obtain ⟨a, h1, h2, h3, h4⟩ := exists_torus h hJ hW
  have h5 := siegel_GAd hS h hJ hW h1 h2 h3
  rw [ratPts_eq_ratOf] at h5
  exact ⟨a, h1, h2, h4, h5⟩

theorem exists_herm_smul (h : IsCMExt F E σ) (hJ : EpsHerm σ J) : ∃ c : E, c ≠ 0 ∧ IsHermND σ (c • J.map σ) := by
  have hσ := sigma_sigma h
  have hd : ∀ c : E, c ≠ 0 → (c • J.map σ).det ≠ 0 := fun c hc => by
    have e : (J.map σ).det = σ J.det := ((σ : E →+* E).map_det _).symm
    rw [det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero σ).2 hJ.2)
  rcases hJ.1 with h1 | h1
  · exact ⟨1, one_ne_zero, fun i j => by simp [h1], hd 1 one_ne_zero⟩
  · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra! hx
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have := h.2.1
      refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
      rw [ComplexEmbedding.isReal_iff]
      ext z
      have := h.2.2.2 τ z
      rw [hx] at this
      exact this.symm
    refine ⟨σ x - x, sub_ne_zero.2 hx, fun i j => ?_, hd _ (sub_ne_zero.2 hx)⟩
    simp only [Matrix.smul_apply, map_apply, smul_eq_mul, map_mul, map_sub, hσ, h1 j i]
    ring

omit [NumberField F] [NumberField E] in
theorem gram_smul (hσ : ∀ x, σ (σ x) = x) (c : E) (Z : Matrix (Fin n) (Fin r) E) (u : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) Z * (c • J.map σ)) *ᵥ u) i = c * σ (form σ J (fun k => Z k i) u) := by
  simp only [form, mulVec, dotProduct, Matrix.mul_apply, cT, transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, hσ, RingHom.coe_coe, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  simp only [form, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp only [form, smul_dotProduct, smul_eq_mul]

omit [NumberField F] [NumberField E] in
theorem form_eq_zero_swap (hσ : ∀ x, σ (σ x) = x) (hJ : EpsHerm σ J) {x y : Fin n → E} (e : form σ J x y = 0) :
    form σ J y x = 0 := by
  have e2 := congrArg σ e
  simp only [form, mulVec, dotProduct, map_sum, map_mul, hσ, map_zero, Finset.mul_sum] at e2 ⊢
  rw [Finset.sum_comm]
  rcases hJ.1 with h1 | h1
  · rw [← e2]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [h1]; ring
  · rw [← neg_zero, ← e2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [h1]; ring

theorem _root_.PositivityTheory.ThKEst.siegelAll_of (hS : GlobalTheory.Published.SiegelSetUnitary) : SiegelAll := by
  intro F E _ _ _ _ _ σ h n J hJ
  have hσ := sigma_sigma h
  obtain ⟨c, hc, hJ'⟩ := exists_herm_smul h hJ
  obtain ⟨r, X, Y, hW⟩ := exists_isWittFrame h hJ'
  obtain ⟨a, h1, h2, h3, h4, h5, h6⟩ := siegel_subgroup hS h hJ' hW (UG (cA σ) (incM F J)) (ug_eq_hr hσ hc)
  have hG : ∀ (Z Z' : Matrix (Fin n) (Fin r) E) i j, (cT (σ : E →+* E) Z * (c • J.map σ) * Z') i j =
      c * σ (form σ J (fun k => Z k i) fun k => Z' k j) := fun Z Z' i j => gram_smul hσ c Z (fun k => Z' k j) i
  have h0 : ∀ (Z Z' : Matrix (Fin n) (Fin r) E), cT (σ : E →+* E) Z * (c • J.map σ) * Z' = 0 → ∀ i j,
      form σ J (fun k => Z k i) (fun k => Z' k j) = 0 := fun Z Z' e i j => by
    have := (hG Z Z' i j).symm.trans (congrFun (congrFun e i) j)
    simpa [hc] using this
  have hperp : ∀ u : Fin n → E, (∀ i, form σ J u (fun k => X k i) = 0 ∧ form σ J u (c • fun k => Y k i) = 0) →
      (cT (σ : E →+* E) X * (c • J.map σ)) *ᵥ u = 0 ∧ (cT (σ : E →+* E) Y * (c • J.map σ)) *ᵥ u = 0 := fun u hu => by
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · rw [gram_smul hσ, form_eq_zero_swap hσ hJ (hu i).1, map_zero, mul_zero]; rfl
    · have := (hu i).2
      rw [form_smul_right, mul_eq_zero, or_iff_right ((map_ne_zero σ).2 hc)] at this
      rw [gram_smul hσ, form_eq_zero_swap hσ hJ this, map_zero, mul_zero]; rfl
  refine ⟨⟨r, fun i k => X k i, fun i => c • fun k => Y k i, a⟩,
    ⟨h0 X X hW.xx, fun i j => ?_, fun i j => ?_, fun u hu e => ?_, h1, h2, fun t i => ?_, fun t i => ?_,
      fun t u hu => (h3 t).2.2 u (hperp u hu).1 (hperp u hu).2⟩,
    two_mul_le_of_wittFrame hσ hJ' hW, h4, h5, h6⟩
  · rw [form_smul_left, form_smul_right, h0 Y Y hW.yy, mul_zero, mul_zero]
  · have := congrArg σ ((hG X Y i j).symm.trans (congrFun (congrFun hW.xy i) j))
    rw [map_mul, hσ] at this
    rw [form_smul_right, this, Matrix.one_apply]
    split_ifs <;> simp
  · refine hW.aniso u (hperp u hu).1 (hperp u hu).2 ?_
    have := gram_smul (J := J) (r := 1) hσ c (of fun k _ => u k) u 0
    rw [show (fun k => (of fun k (_ : Fin 1) => u k) k 0) = u from rfl, e, map_zero, mul_zero] at this
    rw [← this]
    simp only [hE, Formalism.UG.hform, mulVec, dotProduct, Matrix.mul_apply, cT, transpose_apply, map_apply, of_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  · funext k
    have := congrFun (congrFun (h3 t).1 k) i
    rw [mul_diagonal, mul_comm, ← Algebra.smul_def] at this
    exact this
  · have e : incV F (c • fun k => Y k i) = inclR (F := F) (AF F) c • incV F fun k => Y k i :=
      funext fun k => map_mul (inclR (F := F) (AF F)) _ _
    change mat (a t) *ᵥ incV F (c • fun k => Y k i) = rId F (-t i) • incV F (c • fun k => Y k i)
    rw [e, mulVec_smul, smul_comm]
    congr 1
    funext k
    have := congrFun (congrFun (h3 t).2.1 k) i
    rw [mul_diagonal, mul_comm, ← Algebra.smul_def] at this
    exact this

end PositivityTheory.ThKEst.Sieg

end
