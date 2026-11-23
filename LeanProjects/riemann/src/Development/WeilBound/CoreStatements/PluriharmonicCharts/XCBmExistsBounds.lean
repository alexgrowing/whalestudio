import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_bounds

set_option linter.unusedSectionVars false

section LA
variable {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem inv_anti {X Y : Matrix m m ℂ} (hX : X.PosDef) (hY : Y.PosDef) (h : (Y - X).PosSemidef) :
    (X⁻¹ - Y⁻¹).PosSemidef := by
  have hXi : X⁻¹.PosDef := hX.inv
  haveI : Invertible Y := hY.isUnit.invertible
  haveI : Invertible X⁻¹ := hXi.isUnit.invertible
  have hii : X⁻¹⁻¹ = X := Matrix.nonsing_inv_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).1 hX.isUnit)
  have h1 := (Matrix.PosDef.fromBlocks₂₂ Y (1 : Matrix m m ℂ) hXi).2 (by
    simpa [hii] using h)
  have h2 := (Matrix.PosDef.fromBlocks₁₁ (1 : Matrix m m ℂ) X⁻¹ hY).1 (by simpa using h1)
  simpa using h2

theorem scal_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Matrix m m ℂ)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

theorem scal_psd {a : ℝ} (ha : 0 ≤ a) : ((a : ℂ) • (1 : Matrix m m ℂ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (by exact_mod_cast ha)

theorem scal_inv {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Matrix m m ℂ))⁻¹ = ((a⁻¹ : ℝ) : ℂ) • 1 := by
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [Matrix.inv_eq_left_inv]
  rw [smul_mul_smul_comm, Matrix.one_mul]
  push_cast
  rw [inv_mul_cancel₀ hne, one_smul]

def Btw (a b : ℝ) (X : Matrix m m ℂ) : Prop :=
  X.PosDef ∧ (X - (a : ℂ) • (1 : Matrix m m ℂ)).PosSemidef ∧ ((b : ℂ) • (1 : Matrix m m ℂ) - X).PosSemidef

theorem Btw.inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {X : Matrix m m ℂ} (h : Btw a b X) : Btw b⁻¹ a⁻¹ X⁻¹ := by
  obtain ⟨hX, h1, h2⟩ := h
  refine ⟨hX.inv, ?_, ?_⟩
  · have := inv_anti hX (scal_posDef (m := m) hb) h2
    rwa [scal_inv hb] at this
  · have := inv_anti (scal_posDef (m := m) ha) hX h1
    rwa [scal_inv ha] at this

theorem Btw.mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') {X : Matrix m m ℂ} (h : Btw a b X) : Btw a' b' X := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨h0, ?_, ?_⟩
  · have e : X - (a' : ℂ) • (1 : Matrix m m ℂ) = (X - (a : ℂ) • 1) + ((a - a' : ℝ) : ℂ) • 1 := by
      push_cast
      rw [sub_smul]
      abel
    rw [e]
    exact h1.add (scal_psd (by linarith))
  · have e : (b' : ℂ) • (1 : Matrix m m ℂ) - X = ((b : ℂ) • 1 - X) + ((b' - b : ℝ) : ℂ) • 1 := by
      push_cast
      rw [sub_smul]
      abel
    rw [e]
    exact h2.add (scal_psd (by linarith))

theorem Btw.sub {a b : ℝ} {X : Matrix m m ℂ} (h : Btw a b X) (e : m' → m) (he : Function.Injective e) :
    Btw a b (X.submatrix e e) := by
  obtain ⟨h0, h1, h2⟩ := h
  have h1' := h1.submatrix e
  have h2' := h2.submatrix e
  have e1 : (X - (a : ℂ) • (1 : Matrix m m ℂ)).submatrix e e = X.submatrix e e - (a : ℂ) • (1 : Matrix m' m' ℂ) := by
    ext i j
    simp [Matrix.one_apply, he.eq_iff]
  have e2 : ((b : ℂ) • (1 : Matrix m m ℂ) - X).submatrix e e = (b : ℂ) • (1 : Matrix m' m' ℂ) - X.submatrix e e := by
    ext i j
    simp [Matrix.one_apply, he.eq_iff]
  rw [e1] at h1'
  rw [e2] at h2'
  exact ⟨h0.submatrix he, h1', h2'⟩

theorem Btw.tr {a b : ℝ} {X : Matrix m m ℂ} (h : Btw a b X) : Btw a b Xᵀ := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨h0.transpose, ?_, ?_⟩
  · have := h1.transpose
    simpa [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] using this
  · have := h2.transpose
    simpa [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] using this

theorem psd_blocks {X : Matrix m m ℂ} {Y : Matrix m' m' ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (Matrix.fromBlocks X 0 0 Y).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hX.1.fromBlocks (by simp) hY.1, fun x => ?_⟩
  have h1 := hX.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hY.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  have e : star x ⬝ᵥ (Matrix.fromBlocks X 0 0 Y *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (X *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (Y *ᵥ (x ∘ Sum.inr)) := by
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg h1 h2

theorem norm_entry_le {b : ℝ} {X : Matrix m m ℂ} (hX : X.PosSemidef)
    (h : ((b : ℂ) • (1 : Matrix m m ℂ) - X).PosSemidef) (i j : m) : ‖X i j‖ ≤ b := by
  have dX : ∀ k, 0 ≤ (X k k).re ∧ (X k k).im = 0 := by
    intro k
    have := hX.diag_nonneg (i := k)
    rw [Complex.nonneg_iff] at this
    exact ⟨this.1, this.2.symm⟩
  have dN : ∀ k, (X k k).re ≤ b := by
    intro k
    have := h.diag_nonneg (i := k)
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at this
    simpa using (Complex.le_def.mp this).1
  by_cases hij : i = j
  · subst hij
    have e : X i i = ((X i i).re : ℂ) := Complex.ext (by simp) (by simp [(dX i).2])
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dX i).1]
    exact dN i
  · obtain ⟨s, hs⟩ : ∃ s, s = X i j := ⟨_, rfl⟩
    rw [← hs]
    by_cases h0 : s = 0
    · rw [h0, norm_zero]
      exact (dX i).1.trans (dN i)
    have hr : 0 < ‖s‖ := norm_pos_iff.mpr h0
    have hrc : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hss : s * star s = ((‖s‖ : ℂ)) ^ 2 := by
      show s * (starRingEnd ℂ) s = _
      rw [Complex.mul_conj']
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = star s / (‖s‖ : ℂ) := ⟨_, rfl⟩
    have hsw : s * w = (‖s‖ : ℂ) := by
      rw [hw, mul_div_assoc', hss]
      field_simp
    have hji : X j i = star s := by
      rw [hs]
      exact (hX.1.apply j i).symm
    have hws : star w = s / (‖s‖ : ℂ) := by
      rw [hw, star_div₀, star_star]
      congr 1
      simp [Complex.star_def]
    have hww : star w * w = 1 := by
      rw [hws, hw, div_mul_div_comm, hss]
      field_simp
    have e2 : star w * star s = (‖s‖ : ℂ) := by
      rw [← star_mul, hsw]
      simp [Complex.star_def]
    have key : ∀ (N : Matrix m m ℂ), star (Pi.single i 1 + Pi.single j w : m → ℂ) ⬝ᵥ (N *ᵥ (Pi.single i 1 + Pi.single j w)) =
        N i i + N i j * w + star w * N j i + star w * N j j * w := by
      intro N
      simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single, Pi.star_single, single_dotProduct, hij, Ne.symm hij, Pi.single_apply]
      ring
    have Q := h.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j w)
    rw [key] at Q
    have n1 : ((b : ℂ) • (1 : Matrix m m ℂ) - X) i i = b - X i i := by simp [Matrix.sub_apply]
    have n2 : ((b : ℂ) • (1 : Matrix m m ℂ) - X) j j = b - X j j := by simp [Matrix.sub_apply]
    have n3 : ((b : ℂ) • (1 : Matrix m m ℂ) - X) i j = - s := by simp [Matrix.sub_apply, Matrix.one_apply, hij, hs]
    have n4 : ((b : ℂ) • (1 : Matrix m m ℂ) - X) j i = - star s := by
      simp [Matrix.sub_apply, Matrix.one_apply, Ne.symm hij, hji]
    rw [n1, n2, n3, n4] at Q
    have eQ : (b : ℂ) - X i i + -s * w + star w * -star s + star w * ((b : ℂ) - X j j) * w =
        2 * (b : ℂ) - X i i - X j j - 2 * (‖s‖ : ℂ) := by
      linear_combination ((b : ℂ) - X j j) * hww - hsw - e2
    rw [eQ, Complex.nonneg_iff] at Q
    have := Q.1
    simp at this
    linarith [(dX i).1, (dX j).1]

end LA

section An
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : Type} [Fintype m] [DecidableEq m]

theorem contDiffAt_det {A : V → Matrix m m ℂ} {w : V}
    (h : ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => A w' a b) w) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => (A w').det) w := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  refine ContDiffAt.const_smul _ ?_
  exact contDiffAt_prod fun i _ => h _ _

theorem contDiffAt_inv {A : V → Matrix m m ℂ} {w : V}
    (h : ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => A w' a b) w) (hd : (A w).det ≠ 0) (a b : m) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => (A w')⁻¹ a b) w := by
  have e : (fun w' => (A w')⁻¹ a b) = fun w' => ((A w').det)⁻¹ * ((A w').updateRow b (Pi.single a 1)).det := by
    funext w'
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  refine ContDiffAt.mul ((contDiffAt_det h).inv hd) (contDiffAt_det fun i j => ?_)
  by_cases hi : i = b
  · subst hi
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simp only [Matrix.updateRow_ne hi]
    exact h i j

theorem norm_fderiv_inv {A : V → Matrix m m ℂ} {w : V}
    (h : ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => A w' a b) w) (hd : (A w).det ≠ 0) {β δ : ℝ}
    (hβ : ∀ a b, ‖(A w)⁻¹ a b‖ ≤ β) (hδ : ∀ a b, ‖fderiv ℝ (fun w' => A w' a b) w‖ ≤ δ) (a b : m) :
    ‖fderiv ℝ (fun w' => (A w')⁻¹ a b) w‖ ≤ (Fintype.card m) ^ 2 * (β ^ 2 * δ) := by
  set E : m → m → V →L[ℝ] ℂ := fun i j => fderiv ℝ (fun w' => (A w')⁻¹ i j) w with hEdef
  set D : m → m → V →L[ℝ] ℂ := fun i j => fderiv ℝ (fun w' => A w' i j) w with hDdef
  have hdA : ∀ i j, DifferentiableAt ℝ (fun w' => A w' i j) w := fun i j =>
    (h i j).differentiableAt (by simp)
  have hdB : ∀ i j, DifferentiableAt ℝ (fun w' => (A w')⁻¹ i j) w := fun i j =>
    (contDiffAt_inv h hd i j).differentiableAt (by simp)
  have hev : ∀ᶠ w' in nhds w, (A w').det ≠ 0 := (contDiffAt_det h).continuousAt.eventually_ne hd
  have key : ∀ i j, ∑ c, A w i c • E c j = -∑ c, (A w)⁻¹ c j • D i c := by
    intro i j
    have h0 := HasFDerivAt.sum (u := Finset.univ) fun c _ =>
      (hdA i c).hasFDerivAt.mul (hdB c j).hasFDerivAt
    have h1 : HasFDerivAt (fun w' => ∑ c, A w' i c * (A w')⁻¹ c j)
        (∑ c, (A w i c • E c j + (A w)⁻¹ c j • D i c)) w :=
      h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => by simp [Finset.sum_apply])
    have hc : (fun w' => ∑ c, A w' i c * (A w')⁻¹ c j) =ᶠ[nhds w] fun _ => (1 : Matrix m m ℂ) i j := by
      filter_upwards [hev] with w' hw'
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hw')]
    have h2 := (hasFDerivAt_const (𝕜 := ℝ) ((1 : Matrix m m ℂ) i j) w).congr_of_eventuallyEq hc
    have h3 := h1.unique h2
    rw [Finset.sum_add_distrib] at h3
    exact eq_neg_of_add_eq_zero_left h3
  have hBM : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
  have hE : E a b = -∑ i, ∑ c, ((A w)⁻¹ a i * (A w)⁻¹ c b) • D i c := by
    calc E a b = ∑ c, ((A w)⁻¹ * A w) a c • E c b := by
          rw [hBM]; simp [Matrix.one_apply]
      _ = ∑ i, (A w)⁻¹ a i • ∑ c, A w i c • E c b := by
          simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
      _ = _ := by
          simp only [key, Finset.smul_sum, smul_neg, smul_smul, Finset.sum_neg_distrib]
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ a b)
  show ‖E a b‖ ≤ _
  rw [hE, norm_neg]
  calc ‖∑ i, ∑ c, ((A w)⁻¹ a i * (A w)⁻¹ c b) • D i c‖
      ≤ ∑ i : m, ∑ c : m, β ^ 2 * δ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_smul, norm_mul, sq]
        exact mul_le_mul (mul_le_mul (hβ a i) (hβ c b) (norm_nonneg _) hβ0) (hδ i c) (norm_nonneg _)
          (mul_nonneg hβ0 hβ0)
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

private theorem point_lemma {r x : ℝ} (hr : Real.exp 1 ≤ r) (hx : 1 ≤ x) : r * x ≤ r ^ x := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h0 : 0 < r := by linarith
  have hsplit : r ^ x = r ^ (x - 1) * r := by
    rw [← Real.rpow_add_one h0.ne', sub_add_cancel]
  have h2 : Real.exp (x - 1) ≤ r ^ (x - 1) := by
    rw [← Real.exp_one_rpow]
    exact Real.rpow_le_rpow (Real.exp_pos 1).le hr (by linarith)
  have h3 : x ≤ Real.exp (x - 1) := by
    have := Real.add_one_le_exp (x - 1)
    linarith
  calc r * x ≤ r * r ^ (x - 1) := mul_le_mul_of_nonneg_left (h3.trans h2) h0.le
    _ = r ^ x := by rw [hsplit]; ring

private theorem point_lemma_2 {n : Type} [Fintype n] [DecidableEq n] {a b R : ℝ} (ha : 0 < a)
    {Z : Matrix n n ℂ} (h : Btw a b Z) (hb : b ≤ R) (haR : 1 ≤ R * a) :
    ((R : ℂ) • (1 : Matrix n n ℂ) - Z).PosSemidef ∧ ((R : ℂ) • Z - 1).PosSemidef := by
  obtain ⟨_, h1, h2⟩ := h
  have hR : 0 < R := by nlinarith
  constructor
  · have e1 : (R : ℂ) • (1 : Matrix n n ℂ) - Z = ((b : ℂ) • 1 - Z) + ((R - b : ℝ) : ℂ) • 1 := by
      push_cast
      rw [sub_smul]
      abel
    rw [e1]
    exact h2.add (scal_psd (by linarith))
  · have e2 : (R : ℂ) • Z - 1 = (R : ℂ) • (Z - (a : ℂ) • 1) + ((R * a - 1 : ℝ) : ℂ) • 1 := by
      push_cast
      rw [smul_sub, smul_smul, sub_smul, one_smul]
      abel
    rw [e2]
    exact (h1.smul (Complex.zero_le_real.mpr hR.le)).add (scal_psd (by linarith))

theorem point (p q : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) : ∃ C₀ : ℝ, ∀ (r : ℝ), Real.exp 1 ≤ r →
    ∀ (Γ : V → Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (w : V), (Γ w).PosDef →
    ((Γ w)⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef →
    (((C * r : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ w)⁻¹).PosSemidef →
    (∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ w' a b) w ∧
      ‖fderiv ℝ (fun w' => Γ w' a b) w‖ ≤ C * Real.exp (r / 2)) →
    (∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => blockG (Γ w') a b) w) ∧ ∀ C', C₀ ≤ C' →
      ((((r ^ C' : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ w)).PosSemidef ∧
      (((r ^ C' : ℝ) : ℂ) • blockG (Γ w) - 1).PosSemidef) ∧
      ∀ a b, ‖fderiv ℝ (fun w' => blockG (Γ w') a b) w‖ ≤ C' * r ^ C' * Real.exp (r / 2) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  refine ⟨2 + C + c⁻¹ + (q : ℝ) ^ 2 * C ^ 3, ?_⟩
  intro r hr Γ w hP hlo hhi hd
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hCr : 0 < C * r := by positivity
  have hom : Function.Injective (omEmb p q) := by
    intro a b h
    have := congrArg Fin.val h
    simp only [omEmb] at this
    exact Fin.ext this
  have hwm : Function.Injective (wEmb p q) := by
    intro a b h
    have := congrArg Fin.val h
    simp only [wEmb] at this
    exact Fin.ext (by omega)
  have hB : Btw (C * r)⁻¹ c⁻¹ (Γ w) := by
    have h0 : Btw c (C * r) (Γ w)⁻¹ := ⟨hP.inv, hlo, hhi⟩
    have h1 := h0.inv hc hCr
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP.det_pos.ne')] at h1
  have hY : Btw (C * r)⁻¹ c⁻¹ (wBlock (Γ w)) := hB.sub (wEmb p q) hwm
  have hO : Btw (C * r)⁻¹ c⁻¹ (omBlock (Γ w))ᵀ := (hB.sub (omEmb p q) hom).tr
  have hX : Btw c (C * r) ((omBlock (Γ w))ᵀ⁻¹) := by
    have h1 := hO.inv (inv_pos.mpr hCr) (inv_pos.mpr hc)
    simpa only [inv_inv] using h1
  have hA : ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => (omBlock (Γ w'))ᵀ a b) w :=
    fun a b => (hd (omEmb p q b) (omEmb p q a)).1
  have hdet : ((omBlock (Γ w))ᵀ).det ≠ 0 := hO.1.det_pos.ne'
  have hβ : ∀ a b, ‖((omBlock (Γ w))ᵀ)⁻¹ a b‖ ≤ C * r :=
    norm_entry_le hX.1.posSemidef (by exact_mod_cast hX.2.2)
  have hδ : ∀ a b, ‖fderiv ℝ (fun w' => (omBlock (Γ w'))ᵀ a b) w‖ ≤ C * Real.exp (r / 2) :=
    fun a b => (hd (omEmb p q b) (omEmb p q a)).2
  have key : ∀ i j : Fin q ⊕ Fin p,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w' => Matrix.fromBlocks ((omBlock (Γ w'))ᵀ⁻¹) 0 0 (wBlock (Γ w')) i j) w ∧
      ‖fderiv ℝ (fun w' => Matrix.fromBlocks ((omBlock (Γ w'))ᵀ⁻¹) 0 0 (wBlock (Γ w')) i j) w‖ ≤
        max ((q : ℝ) ^ 2 * ((C * r) ^ 2 * (C * Real.exp (r / 2)))) (C * Real.exp (r / 2)) := by
    have hpos : 0 ≤ max ((q : ℝ) ^ 2 * ((C * r) ^ 2 * (C * Real.exp (r / 2)))) (C * Real.exp (r / 2)) :=
      le_max_of_le_right (by positivity)
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁]
      refine ⟨contDiffAt_inv hA hdet i j, le_max_of_le_left ?_⟩
      have := norm_fderiv_inv hA hdet hβ hδ i j
      simpa using this
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      refine ⟨contDiffAt_const, ?_⟩
      simpa using hpos
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      refine ⟨contDiffAt_const, ?_⟩
      simpa using hpos
    · simp only [Matrix.fromBlocks_apply₂₂]
      exact ⟨(hd (wEmb p q i) (wEmb p q j)).1, le_max_of_le_right (hd (wEmb p q i) (wEmb p q j)).2⟩
  refine ⟨fun a b => (key ((blockEquiv p q).symm a) ((blockEquiv p q).symm b)).1, ?_⟩
  intro C' hC'
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hq : 0 ≤ (q : ℝ) ^ 2 * C ^ 3 := by positivity
  have hC'1 : 1 ≤ C' := by linarith
  have hrC := point_lemma hr hC'1
  have hR0 : 0 < r ^ C' := Real.rpow_pos_of_pos hr0 C'
  have hR1 : C * r ≤ r ^ C' := by nlinarith
  have hR2 : c⁻¹ ≤ r ^ C' := by nlinarith
  have hRc : 1 ≤ r ^ C' * c := by
    have := mul_le_mul_of_nonneg_right hR2 hc.le
    rwa [inv_mul_cancel₀ hc.ne'] at this
  have hRcr : 1 ≤ r ^ C' * (C * r)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hCr]
    linarith
  have hr2 : r ^ 2 ≤ r ^ C' := by
    have := Real.rpow_le_rpow_of_exponent_le hr1 (show (2 : ℝ) ≤ C' by linarith)
    simpa using this
  obtain ⟨hX1, hX2⟩ := point_lemma_2 hc hX hR1 hRc
  obtain ⟨hY1, hY2⟩ := point_lemma_2 (inv_pos.mpr hCr) hY hR2 hRcr
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have e1 : ((r ^ C' : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ w) =
        (Matrix.fromBlocks (((r ^ C' : ℝ) : ℂ) • 1 - (omBlock (Γ w))ᵀ⁻¹) 0 0
          (((r ^ C' : ℝ) : ℂ) • 1 - wBlock (Γ w))).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [← Matrix.submatrix_one_equiv (blockEquiv p q).symm]
      ext a b
      simp only [blockG, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply]
      generalize (blockEquiv p q).symm a = i
      generalize (blockEquiv p q).symm b = j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    rw [e1]
    exact (psd_blocks hX1 hY1).submatrix _
  · have e2 : ((r ^ C' : ℝ) : ℂ) • blockG (Γ w) - 1 =
        (Matrix.fromBlocks (((r ^ C' : ℝ) : ℂ) • (omBlock (Γ w))ᵀ⁻¹ - 1) 0 0
          (((r ^ C' : ℝ) : ℂ) • wBlock (Γ w) - 1)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [← Matrix.submatrix_one_equiv (blockEquiv p q).symm]
      ext a b
      simp only [blockG, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply]
      generalize (blockEquiv p q).symm a = i
      generalize (blockEquiv p q).symm b = j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    rw [e2]
    exact (psd_blocks hX2 hY2).submatrix _
  · intro a b
    refine (key ((blockEquiv p q).symm a) ((blockEquiv p q).symm b)).2.trans (max_le ?_ ?_)
    · have hE := Real.exp_pos (r / 2)
      have h1 : (q : ℝ) ^ 2 * C ^ 3 * r ^ 2 ≤ C' * r ^ C' := by
        have : (q : ℝ) ^ 2 * C ^ 3 ≤ C' := by linarith [inv_pos.mpr hc]
        exact mul_le_mul this hr2 (by positivity) (by linarith)
      calc (q : ℝ) ^ 2 * ((C * r) ^ 2 * (C * Real.exp (r / 2)))
          = (q : ℝ) ^ 2 * C ^ 3 * r ^ 2 * Real.exp (r / 2) := by ring
        _ ≤ C' * r ^ C' * Real.exp (r / 2) := mul_le_mul_of_nonneg_right h1 hE.le
    · have hE := Real.exp_pos (r / 2)
      have h1 : C ≤ C' * r ^ C' := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hE.le

end An

end PositivityTheory.Xgp.c_bm_exists_bounds

private theorem t_c_bm_exists_bounds_lemma {E : Type} [PseudoMetricSpace E] {s : Set E} (Q : E → ℝ → Prop)
    (hs : IsCompact s) (h : ∀ w₀ ∈ s, ∃ ε > 0, ∃ D : ℝ, ∀ w, dist w w₀ < ε → ∀ C ≥ D, Q w C) :
    ∃ D : ℝ, ∀ w ∈ s, ∀ C ≥ D, Q w C := by
  choose! ε hε D hD using h
  obtain ⟨t, hts, hcov⟩ := hs.elim_nhds_subcover (fun w₀ => Metric.ball w₀ (ε w₀))
    (fun w₀ hw₀ => Metric.ball_mem_nhds w₀ (hε w₀ hw₀))
  refine ⟨∑ w₀ ∈ t, |D w₀|, fun w hw C hC => ?_⟩
  obtain ⟨w₀, hw₀t, hww₀⟩ := Set.mem_iUnion₂.mp (hcov hw)
  apply hD w₀ (hts w₀ hw₀t) w hww₀ C
  calc D w₀ ≤ |D w₀| := le_abs_self _
    _ ≤ ∑ w₀ ∈ t, |D w₀| := Finset.single_le_sum (fun i _ => abs_nonneg (D i)) hw₀t
    _ ≤ C := hC

theorem PositivityTheory.Xgp.t_c_bm_exists_bounds : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
  intro n p q X _ _ _ A B Z Cl U r Γ hAB hball2 hcov hZ hCl hU hUCl hr hloc
  have key : ∀ x ∈ U \ Z, ∃ k : Fin B.n, x ∈ (B.chart k).source ∧ ∀ a b,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => blockG (Γ ((B.chart k).symm w')) a b) (B.chart k x) := by
    intro x hx
    obtain ⟨k, hxs, hxb⟩ := hcov x
    refine ⟨k, hxs, ?_⟩
    have hx' : (B.chart k).symm (B.chart k x) = x := (B.chart k).left_inv hxs
    have hw : B.chart k x ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) := by
      rw [Metric.mem_ball] at hxb
      rw [Metric.mem_closedBall]
      linarith
    obtain ⟨ε, c, C, hε, hc, hC, hl⟩ := hloc k _ hw (by rw [hx']; exact hUCl hx.1)
    obtain ⟨hpd, h1, h2, h3⟩ := hl (B.chart k x) (by simpa using hε) (by rw [hx']; exact hx.2)
    obtain ⟨D, hD⟩ := PositivityTheory.Xgp.c_bm_exists_bounds.point (V := Fin n → ℂ) p q hc hC
    exact (hD _ (hr _ (by rw [hx']; exact hx.2)) (fun w' => Γ ((B.chart k).symm w')) (B.chart k x)
      hpd h1 h2 h3).1
  have hsm : ∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧
      A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im) := by
    intro a b
    have gen : ∀ (L : ℂ →L[ℝ] ℝ), A.SmoothOn (U \ Z) (fun x => L (blockG (Γ x) a b)) := by
      intro L j v hv
      obtain ⟨hvt, hvU⟩ := hv
      obtain ⟨k, hxs, hk⟩ := key _ hvU
      have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((B.chart k) ∘ (A.chart j).symm) v :=
        ((hAB.1 j k v ⟨hvt, hxs⟩).contDiffAt).restrict_scalars ℝ
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w' => L (blockG (Γ ((B.chart k).symm w')) a b)) (((B.chart k) ∘ (A.chart j).symm) v) :=
        L.contDiff.contDiffAt.comp _ (hk a b)
      have hev : (fun x => L (blockG (Γ x) a b)) ∘ (A.chart j).symm =ᶠ[nhds v]
          (fun w' => L (blockG (Γ ((B.chart k).symm w')) a b)) ∘ ((B.chart k) ∘ (A.chart j).symm) := by
        filter_upwards [((A.chart j).continuousAt_symm hvt).preimage_mem_nhds
          ((B.chart k).open_source.mem_nhds hxs)] with y hy
        simp only [Function.comp_apply]
        rw [(B.chart k).left_inv hy]
      exact ((hg.comp v hφ).congr_of_eventuallyEq hev).contDiffWithinAt
    exact ⟨gen Complex.reCLM, gen Complex.imCLM⟩
  refine ⟨hsm, ?_⟩
  have hK : ∀ k : Fin B.n, ∃ D : ℝ, ∀ w ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) ∩ (B.chart k).symm ⁻¹' Cl,
      ∀ C ≥ D, (B.chart k).symm w ∉ Z →
      (((((r ((B.chart k).symm w)) ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) -
          blockG (Γ ((B.chart k).symm w))).PosSemidef ∧
        ((((r ((B.chart k).symm w)) ^ C : ℝ) : ℂ) • blockG (Γ ((B.chart k).symm w)) - 1).PosSemidef) ∧
      ∀ a b, ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤
        C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
    intro k
    apply t_c_bm_exists_bounds_lemma
    · refine (isCompact_closedBall (0 : Fin n → ℂ) (3 / 2)).of_isClosed_subset ?_ Set.inter_subset_left
      have hsub : Metric.closedBall (0 : Fin n → ℂ) (3 / 2) ⊆ (B.chart k).target :=
        (Metric.closedBall_subset_closedBall (by norm_num)).trans (hball2 k)
      exact ((B.chart k).continuousOn_symm.mono hsub).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall hCl
    · intro w₀ hw₀
      obtain ⟨ε, c, C, hε, hc, hC, hl⟩ := hloc k w₀ hw₀.1 hw₀.2
      obtain ⟨D, hD⟩ := PositivityTheory.Xgp.c_bm_exists_bounds.point (V := Fin n → ℂ) p q hc hC
      refine ⟨ε, hε, D, fun w hw C' hC' hz => ?_⟩
      obtain ⟨hpd, h1, h2, h3⟩ := hl w (by rw [← dist_eq_norm]; exact hw) hz
      exact (hD _ (hr _ hz) (fun w' => Γ ((B.chart k).symm w')) w hpd h1 h2 h3).2 C' hC'
  choose D hD using hK
  refine ⟨∑ k, |D k|, fun C hC => ?_⟩
  have hDk : ∀ k, D k ≤ C := fun k =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (D i)) (Finset.mem_univ k)).trans hC)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨k, hxs, hxb⟩ := hcov x
    have hx' : (B.chart k).symm (B.chart k x) = x := (B.chart k).left_inv hxs
    have hw : B.chart k x ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) := by
      rw [Metric.mem_ball] at hxb
      rw [Metric.mem_closedBall]
      linarith
    have hm : B.chart k x ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) ∩ (B.chart k).symm ⁻¹' Cl := by
      refine ⟨hw, ?_⟩
      show (B.chart k).symm (B.chart k x) ∈ Cl
      rw [hx']
      exact hx.1
    have := hD k (B.chart k x) hm C (hDk k) (by rw [hx']; exact hx.2)
    rw [hx'] at this
    exact this.1
  · intro a b k w hw hwZ
    have hw' : w ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) := Metric.ball_subset_closedBall hw
    exact (hD k w ⟨hw', hwZ.1⟩ C (hDk k) hwZ.2).2 a b
