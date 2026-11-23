import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RConj

open GlobalTheory.Amp.Rad GlobalTheory.Amp.USplit

variable {k r : ℕ}

theorem mulVec_mp {ι : Type*} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : Complex.normSq g.det = 1) :
    MeasurePreserving (fun v : ι → ℂ => g *ᵥ v) volume volume := by
  set f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' g).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]
  have hfun : (⇑f) = fun v : ι → ℂ => g *ᵥ v := by
    funext v
    simp [hf, Matrix.toLin'_apply]
  rw [← hfun]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]
  simp

theorem mul_star_mp {a : ℂ} (ha : ‖a‖ = 1) : MeasurePreserving (fun z : ℂ => a * star z) volume volume := by
  set f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℝ a).comp Complex.conjAe.toLinearEquiv.toLinearMap with hf
  have hn : Complex.normSq a = 1 := by
    rw [Complex.normSq_eq_norm_sq, ha]; norm_num
  have hm : LinearMap.det (LinearMap.mulLeft ℝ a) = Complex.normSq a := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hdet : LinearMap.det f = -1 := by
    rw [hf, LinearMap.det_comp, hm, Complex.det_conjAe, hn]; norm_num
  have hfun : (⇑f) = fun z : ℂ => a * star z := by
    funext z
    simp [hf]
  rw [← hfun]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; norm_num), hdet]
  simp

theorem normSq_det_of_mem {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k)) :
    Complex.normSq M.det = 1 := by
  have hM' : Mᴴ * Hb k * M = Hb k := hM
  have h := congrArg Matrix.det hM'
  simp only [Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hH : (Hb k).det ≠ 0 := by
    rw [show Hb k = Matrix.diagonal fun j => if j = Fin.last k then (-1 : ℂ) else 1 from rfl,
      Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by split_ifs <;> norm_num
  have h2 : star M.det * M.det = 1 := by
    apply mul_right_cancel₀ hH
    rw [one_mul]
    calc star M.det * M.det * (Hb k).det = star M.det * (Hb k).det * M.det := by ring
      _ = (Hb k).det := h
  have h3 : (Complex.normSq M.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

theorem isUnit_upper (x : UT r → ℂ) : IsUnit (upper x).det := by
  have htri : (upper x).BlockTriangular id := fun a b hab => upper_of_gt x hab
  rw [Matrix.det_of_upperTriangular htri]
  simp [upper_diag]

theorem inv_zero_of {α : Type*} [LinearOrder α] (f : Fin r → α) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det)
    (h : ∀ a b, f b < f a → u a b = 0) {a b : Fin r} (hab : f b < f a) : u⁻¹ a b = 0 := by
  letI := Matrix.invertibleOfIsUnitDet u hu
  have htri : u.BlockTriangular f := fun i j hij => h i j hij
  exact Matrix.blockTriangular_inv_of_blockTriangular htri hab

theorem inv_upper_gt (x : UT r → ℂ) {a b : Fin r} (h : b < a) : (upper x)⁻¹ a b = 0 := by
  refine inv_zero_of (fun c : Fin r => c) (upper x) (isUnit_upper x) ?_ h
  intro a' b' hlt
  exact upper_of_gt x hlt

theorem inv_upper_diag (x : UT r → ℂ) (a : Fin r) : (upper x)⁻¹ a a = 1 := by
  have h1 : ((upper x)⁻¹ * upper x) a a = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_upper x), Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · simpa [upper_diag] using h1
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [inv_upper_gt x hlt, zero_mul]
    · rw [upper_of_gt x hgt, mul_zero]
  · intro hna
    exact absurd (Finset.mem_univ a) hna

theorem inv_upper_lt (x : UT r → ℂ) {a b : Fin r} (h : a < b) :
    -(upper x)⁻¹ a b - upper x a b = ∑ c, if a < c ∧ c < b then upper x a c * (upper x)⁻¹ c b else 0 := by
  have h0 : (upper x * (upper x)⁻¹) a b = 0 := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_upper x)]
    exact Matrix.one_apply_ne (ne_of_lt h)
  rw [Matrix.mul_apply] at h0
  have hterm : ∀ c, upper x a c * (upper x)⁻¹ c b =
      ((if c = a then (upper x)⁻¹ a b else 0) + (if c = b then upper x a b else 0)) +
        (if a < c ∧ c < b then upper x a c * (upper x)⁻¹ c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd (hh.1.trans hca) (lt_irrefl _)
      rw [upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg (ne_of_lt (hca.trans h)), if_neg n1]
      ring
    · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd hh.1 (by rw [hca]; exact lt_irrefl _)
      have n2 : c ≠ b := by rw [hca]; exact ne_of_lt h
      rw [if_pos hca, if_neg n2, if_neg n1, hca, upper_diag, one_mul]
      ring
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]
        ring
      · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd hh.2 (by rw [hcb]; exact lt_irrefl _)
        rw [if_neg (ne_of_gt hac), if_pos hcb, if_neg n1, hcb, inv_upper_diag, mul_one]
        ring
      · have n1 : ¬ (a < c ∧ c < b) := fun hh => absurd (hh.2.trans hbc) (lt_irrefl _)
        rw [inv_upper_gt x hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc), if_neg n1]
        ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)] at h0
  linear_combination -h0

theorem inv_upper_congr (x y : UT r → ℂ) (n : ℕ)
    (hxy : ∀ a b : Fin r, a < b → b.val - a.val < n → upper x a b = upper y a b) :
    ∀ (m : ℕ) (a b : Fin r), a < b → b.val - a.val ≤ m → b.val - a.val ≤ n →
      -(upper x)⁻¹ a b - upper x a b = -(upper y)⁻¹ a b - upper y a b := by
  intro m
  induction m with
  | zero =>
    intro a b hab hm _
    have : a.val < b.val := hab
    omega
  | succ m ih =>
    intro a b hab hm hn
    rw [inv_upper_lt x hab, inv_upper_lt y hab]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : a < c ∧ c < b
    · rw [if_pos hc, if_pos hc]
      have hac' : a.val < c.val := hc.1
      have hcb' : c.val < b.val := hc.2
      have e1 : upper x a c = upper y a c := hxy a c hc.1 (by omega)
      have e2 : upper x c b = upper y c b := hxy c b hc.2 (by omega)
      have e3 := ih c b hc.2 (by omega) (by omega)
      have e4 : (upper x)⁻¹ c b = (upper y)⁻¹ c b := by
        rw [e2] at e3
        linear_combination -e3
      rw [e1, e4]
    · rw [if_neg hc, if_neg hc]

private lemma det_upperIn_eq_one (β : Fin r → ℕ) (x : UTin β → ℂ) : (upperIn β x).det = 1 := by
  unfold upperIn
  have hb : (upper fun p : UT r => if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0).BlockTriangular id :=
    fun a b hab => upper_of_gt _ hab
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => upper_diag _ a

theorem continuous_inv_upperIn (β : Fin r → ℕ) : Continuous fun x : UTin β → ℂ => (upperIn β x)⁻¹ := by
  have hfun : (fun x : UTin β → ℂ => (upperIn β x)⁻¹) = fun x => (upperIn β x).adjugate := by
    funext x
    rw [Matrix.inv_def, det_upperIn_eq_one, Ring.inverse_one, one_smul]
  rw [hfun]
  exact (continuous_upperIn β).matrix_adjugate

theorem upperIn_lt (β : Fin r → ℕ) (x : UTin β → ℂ) (p : UTin β) : upperIn β x p.1.1.1 p.1.1.2 = x p := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ := p
  unfold upperIn
  rw [upper_of_lt _ hab]
  exact dif_pos hβ

theorem upperIn_ne (β : Fin r → ℕ) (x : UTin β → ℂ) {a b : Fin r} (h : β a ≠ β b) : upperIn β x a b = 0 := by
  unfold upperIn
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [upper_of_lt _ hab]
    exact dif_neg h
  · exact absurd (congrArg β hab) h
  · exact upper_of_gt _ hab

theorem inv_upperIn_ne (β : Fin r → ℕ) (x : UTin β → ℂ) {a b : Fin r} (h : β a ≠ β b) : (upperIn β x)⁻¹ a b = 0 := by
  haveI : Invertible (upperIn β x) := Matrix.invertibleOfIsUnitDet _ (isUnit_upper _)
  have h1 : (upperIn β x).BlockTriangular β := fun i j hij => upperIn_ne β x (ne_of_gt hij)
  have h2 : (upperIn β x).BlockTriangular (fun i => OrderDual.toDual (β i)) :=
    fun i j hij => upperIn_ne β x (ne_of_lt (OrderDual.toDual_lt_toDual.mp hij))
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact Matrix.blockTriangular_inv_of_blockTriangular h2 (OrderDual.toDual_lt_toDual.mpr hlt)
  · exact Matrix.blockTriangular_inv_of_blockTriangular h1 hlt

def shearInv (j : ℕ) (β : Fin r → ℕ) (x : UTin β → ℂ) : UTin β → ℂ := fun p =>
  if p.1.1.1.val < j then -(upperIn β x)⁻¹ p.1.1.1 p.1.1.2 else x p

theorem shearInv_mp (j : ℕ) (β : Fin r → ℕ) : MeasurePreserving (shearInv j β) volume volume := by
  refine Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (fun p : UTin β => p.1.1.2.val - p.1.1.1.val) (shearInv j β) ?_ ?_
  · refine Continuous.measurable (continuous_pi fun p => ?_)
    by_cases hp : p.1.1.1.val < j
    · simp only [shearInv, hp, if_true]
      exact ((continuous_apply p.1.1.2).comp ((continuous_apply p.1.1.1).comp
        (continuous_inv_upperIn β))).neg
    · simp only [shearInv, hp, if_false]
      exact continuous_apply p
  · intro q x y hxy
    by_cases hq : q.1.1.1.val < j
    · simp only [shearInv, hq, if_true]
      rw [← upperIn_lt β x q, ← upperIn_lt β y q]
      unfold upperIn
      refine inv_upper_congr _ _ (q.1.1.2.val - q.1.1.1.val) (fun a b hab hlt => ?_) _ _ _ q.1.2 le_rfl le_rfl
      rw [upper_of_lt _ hab, upper_of_lt _ hab]
      by_cases hβ : β a = β b
      · simp only [dif_pos hβ]
        exact hxy ⟨⟨(a, b), hab⟩, hβ⟩ hlt
      · simp only [dif_neg hβ]
    · simp only [shearInv, hq, if_false, sub_self]

def HasBlocks (g : Mat k r) (D Y Z : Matrix (Fin r) (Fin r) ℂ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  (∀ a b, g (eI k r a) (eI k r b) = D a b) ∧ (∀ a n, g (eI k r a) (wI k r n) = 0) ∧
  (∀ a b, g (eI k r a) (esI k r b) = Y a b) ∧ (∀ n b, g (wI k r n) (eI k r b) = 0) ∧
  (∀ m n, g (wI k r m) (wI k r n) = M m n) ∧ (∀ n b, g (wI k r n) (esI k r b) = 0) ∧
  (∀ a b, g (esI k r a) (eI k r b) = Z a b) ∧ (∀ a n, g (esI k r a) (wI k r n) = 0) ∧
  (∀ a b, g (esI k r a) (esI k r b) = D a b)

section
variable (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) (m n : Fin (k + 1))
theorem u_ew : uEmb k r u (eI k r a) (wI k r n) = 0 := by
  have ha := a.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
theorem u_we : uEmb k r u (wI k r m) (eI k r b) = 0 := by
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
theorem u_ww : uEmb k r u (wI k r m) (wI k r n) = if m = n then 1 else 0 := by
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
theorem u_ws : uEmb k r u (wI k r m) (esI k r b) = 0 := by
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
theorem u_sw : uEmb k r u (esI k r a) (wI k r n) = 0 := by
  have ha := a.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
theorem u_ss : uEmb k r u (esI k r a) (esI k r b) = (u⁻¹)ᴴ a b := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs with h1 h2
  · exfalso; simp only [esI] at h1; omega
  · rw [conjTranspose_apply]
    have key : ∀ x y : Fin r, x.val = b.val → y.val = a.val → u⁻¹ x y = u⁻¹ b a := by
      intro x y hx hy
      rw [Fin.ext hx, Fin.ext hy]
    exact congrArg star (key _ _ (by simp only [esI]; omega) (by simp only [esI]; omega))
  · exfalso; apply h2; simp only [esI]; omega
  · exfalso; apply h2; simp only [esI]; omega

private lemma uEmb_eI_eI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (eI k r a) (eI k r b) = u a b := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)

private lemma uEmb_eI_esI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (eI k r a) (esI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)

private lemma uEmb_esI_eI (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    uEmb k r u (esI k r a) (eI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold uEmb
  split_ifs <;> first
    | rfl
    | (exfalso; simp_all [eI, wI, esI, Fin.ext_iff] <;> omega)
end

theorem conj_u {g : Mat k r} {D Y Z : Matrix (Fin r) (Fin r) ℂ} {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : HasBlocks g D Y Z M) {u u' : Matrix (Fin r) (Fin r) ℂ} (h1 : D * u = u' * D) (h2 : Y * (u⁻¹)ᴴ = u' * Y)
    (h3 : Z * u = (u'⁻¹)ᴴ * Z) (h4 : D * (u⁻¹)ᴴ = (u'⁻¹)ᴴ * D) : g * uEmb k r u = uEmb k r u' * g := by
  obtain ⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩ := hg
  ext i j
  induction i using cases3 <;> induction j using cases3 <;>
    simp only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, uEmb_eI_eI, uEmb_eI_esI,
      uEmb_esI_eI, u_ew, u_we, u_ww, u_ws, u_sw, u_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  all_goals first
    | rfl
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h1 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h2 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h3 _) _
    | simpa only [Matrix.mul_apply] using congrFun (congrFun h4 _) _

theorem alg {Y Z F u : Matrix (Fin r) (Fin r) ℂ} (c : ℂ) (hu : IsUnit u.det) (hF : Fᴴ = F) (hFF : F * F = F)
    (hYZ : Yᴴ * Z = 1 - F) (hZY : Y * Zᴴ = 1 - F) (hFY : F * Y = 0) (hYF : Y * F = 0) (hFZ : F * Z = 0) (hZF : Z * F = 0)
    (huF : u * F = F * u) :
    (c • F) * u = (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * (c • F) ∧ Y * (u⁻¹)ᴴ = (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * Y ∧
    Z * u = ((Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹)ᴴ * Z ∧ (c • F) * (u⁻¹)ᴴ = ((Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹)ᴴ * (c • F) := by
  have hui1 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hu
  have hui2 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hu
  have hA1 : (u⁻¹)ᴴ * uᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hui1, Matrix.conjTranspose_one]
  have hZhF : Zᴴ * F = 0 := by
    have h0 := congrArg Matrix.conjTranspose hFZ
    rwa [Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero] at h0
  have hYhF : Yᴴ * F = 0 := by
    have h0 := congrArg Matrix.conjTranspose hFY
    rwa [Matrix.conjTranspose_mul, hF, Matrix.conjTranspose_zero] at h0
  have hZhY : Zᴴ * Y = 1 - F := by
    have h0 := congrArg Matrix.conjTranspose hYZ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hF] at h0
  have huiF : u⁻¹ * F = F * u⁻¹ := by
    calc u⁻¹ * F = u⁻¹ * F * (u * u⁻¹) := by rw [hui1, Matrix.mul_one]
      _ = u⁻¹ * (F * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * F) * u⁻¹ := by rw [huF]
      _ = F * u⁻¹ := by rw [← Matrix.mul_assoc u⁻¹, hui2, Matrix.one_mul]
  have hAF : (u⁻¹)ᴴ * F = F * (u⁻¹)ᴴ := by
    have h0 := congrArg Matrix.conjTranspose huiF
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF] at h0
    exact h0.symm
  have t1 : Y * (u⁻¹)ᴴ * Zᴴ * (Y * uᴴ * Zᴴ) = 1 - F := by
    calc Y * (u⁻¹)ᴴ * Zᴴ * (Y * uᴴ * Zᴴ) = Y * (u⁻¹)ᴴ * (Zᴴ * Y) * uᴴ * Zᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Y * ((u⁻¹)ᴴ * uᴴ) * Zᴴ - Y * (F * (u⁻¹)ᴴ) * uᴴ * Zᴴ := by
          rw [hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, ← hAF]
          simp only [Matrix.mul_assoc]
      _ = Y * Zᴴ := by
          rw [hA1, Matrix.mul_one, ← Matrix.mul_assoc Y F, hYF, Matrix.zero_mul, Matrix.zero_mul,
            Matrix.zero_mul, sub_zero]
      _ = 1 - F := hZY
  have t2 : Y * (u⁻¹)ᴴ * Zᴴ * (F * u⁻¹) = 0 := by
    calc Y * (u⁻¹)ᴴ * Zᴴ * (F * u⁻¹) = Y * (u⁻¹)ᴴ * (Zᴴ * F) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hZhF, Matrix.mul_zero, Matrix.zero_mul]
  have t3 : F * u * (Y * uᴴ * Zᴴ) = 0 := by
    calc F * u * (Y * uᴴ * Zᴴ) = u * (F * Y) * uᴴ * Zᴴ := by rw [← huF]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hFY, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have t4 : F * u * (F * u⁻¹) = F := by
    calc F * u * (F * u⁻¹) = F * (u * F) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = F := by rw [huF, ← Matrix.mul_assoc, hFF, Matrix.mul_assoc, hui1, Matrix.mul_one]
  have hinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u) * (Y * uᴴ * Zᴴ + F * u⁻¹) = 1 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, t4]
    abel
  have hvinv : (Y * (u⁻¹)ᴴ * Zᴴ + F * u)⁻¹ = Y * uᴴ * Zᴴ + F * u⁻¹ := Matrix.inv_eq_right_inv hinv
  have hvH : (Y * uᴴ * Zᴴ + F * u⁻¹)ᴴ = Z * u * Yᴴ + (u⁻¹)ᴴ * F := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hF]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    have e0 : Y * (u⁻¹)ᴴ * Zᴴ * F = 0 := by rw [Matrix.mul_assoc, hZhF, Matrix.mul_zero]
    rw [Matrix.add_mul, e0, zero_add, Matrix.mul_assoc, huF, ← Matrix.mul_assoc, hFF]
  · have e1 : Y * (u⁻¹)ᴴ * Zᴴ * Y = Y * (u⁻¹)ᴴ := by
      rw [Matrix.mul_assoc, hZhY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hAF,
        ← Matrix.mul_assoc, hYF, Matrix.zero_mul, sub_zero]
    have e2 : F * u * Y = 0 := by rw [← huF, Matrix.mul_assoc, hFY, Matrix.mul_zero]
    rw [Matrix.add_mul, e1, e2, add_zero]
  · have e1 : Z * u * Yᴴ * Z = Z * u := by
      rw [Matrix.mul_assoc, hYZ, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, huF,
        ← Matrix.mul_assoc, hZF, Matrix.zero_mul, sub_zero]
    have e2 : (u⁻¹)ᴴ * F * Z = 0 := by rw [Matrix.mul_assoc, hFZ, Matrix.mul_zero]
    rw [hvinv, hvH, Matrix.add_mul, e1, e2, add_zero]
  · rw [hvinv, hvH, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [Matrix.add_mul, Matrix.mul_assoc (Z * u), hYhF, Matrix.mul_zero, zero_add, Matrix.mul_assoc, hFF, hAF]

theorem herm_mulVec {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k)) (v w : Fin (k + 1) → ℂ) :
    herm (Hb k) (M *ᵥ v) (M *ᵥ w) = herm (Hb k) v w := by
  have hM' : Mᴴ * Hb k * M = Hb k := hM
  show star (M *ᵥ w) ⬝ᵥ (Hb k *ᵥ (M *ᵥ v)) = star w ⬝ᵥ (Hb k *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

theorem herm_smul (c d : ℂ) (v w : Fin (k + 1) → ℂ) :
    herm (Hb k) (c • v) (d • w) = c * star d * herm (Hb k) v w := by
  show star (d • w) ⬝ᵥ (Hb k *ᵥ (c • v)) = c * star d * (star w ⬝ᵥ (Hb k *ᵥ v))
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

private lemma sum_star_mulVec_mul_sg_mul_eq {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hM : M ∈ UH (Hb k))
    (v : Fin (k + 1) → ℂ) (n : Fin (k + 1)) :
    ∑ m, star ((M *ᵥ v) m) * sg k m * M m n = star (v n) * sg k n := by
  have hU : ∀ l, ∑ m, star (M m l) * sg k m * M m n = if l = n then sg k l else 0 := by
    intro l
    have h := congrFun (congrFun hM l) n
    rw [← Hb_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Hb_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ∑ m, star ((M *ᵥ v) m) * sg k m * M m n
      = ∑ m, ∑ l, star (v l) * (star (M m l) * sg k m * M m n) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ = ∑ l, star (v l) * ∑ m, star (M m l) * sg k m * M m n := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = star (v n) * sg k n := by
        simp only [hU, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def Fj (r j : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => if j ≤ a.val then 1 else 0

theorem conj_p {j : ℕ} {g : Mat k r} {c : ℂ} {Y Z : Matrix (Fin r) (Fin r) ℂ} {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : HasBlocks g (c • Fj r j) Y Z M) (hc : ‖c‖ = 1) (hM : M ∈ UH (Hb k))
    (hZ : ∀ a b : Fin r, j ≤ a.val ∨ j ≤ b.val → Z a b = 0)
    (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a : Fin r, a.val < j → B a = 0)
    (hS : ∀ a b : Fin r, a.val < j ∨ b.val < j → S a b = 0) :
    g * pEl k r B S = pEl k r (fun a => star c • M *ᵥ B a) S * g := by
  obtain ⟨hee, hew, hes, hwe, hww, hws, hse, hsw, hss⟩ := hg
  have hD : ∀ a b : Fin r, (c • Fj r j) a b = if a = b then (if j ≤ a.val then c else 0) else 0 := by
    intro a b
    simp only [Fj, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcc : star c * c = 1 := by
    have h2 : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h2]; simp
  have hB' : ∀ a : Fin r, a.val < j → star c • M *ᵥ B a = 0 := by
    intro a h
    rw [hB a h, mulVec_zero, smul_zero]
  have hv1 : ∀ a b : Fin r,
      ∑ x, (S a x - herm (Hb k) (star c • M *ᵥ B x) (star c • M *ᵥ B a) / 2) * Z x b = 0 := by
    intro a b
    apply Finset.sum_eq_zero
    intro x _
    by_cases h : j ≤ x.val
    · rw [hZ x b (Or.inl h), mul_zero]
    · push_neg at h
      rw [hS a x (Or.inr h), hB' x h]
      simp [herm]
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [Matrix.mul_apply, sum3, hee, hew, hes, hwe, hww, hws, hse, hsw, hss, hD, pEl_ee, pEl_ew, pEl_es,
      pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  all_goals first
    | rfl
    | (rw [hv1, add_zero]; split_ifs <;> simp_all)
    | (rename_i a n
       by_cases h : j ≤ a.val
       · rw [if_pos h, ← sum_star_mulVec_mul_sg_mul_eq hM (B a) n, ← Finset.sum_neg_distrib, Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro x _
         simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_star]
         ring
       · rw [if_neg h, hB' a (by omega)]
         simp)
    | (rename_i a b
       rw [add_comm]
       congr 1
       by_cases ha : j ≤ a.val <;> by_cases hb : j ≤ b.val
       · simp only [ha, hb, if_true, herm_smul, herm_mulVec hM, star_star, hcc, one_mul]
         ring
       · simp only [ha, hb, if_true, if_false, hS a b (Or.inr (by omega)), hB b (by omega)]
         simp [herm]
       · simp only [ha, hb, if_true, if_false, hS a b (Or.inl (by omega)), hB' a (by omega)]
         simp [herm]
       · simp only [ha, hb, if_false])
    | (rename_i m a
       rw [ite_self, zero_add]
       symm
       apply Finset.sum_eq_zero
       intro x _
       by_cases h : j ≤ x.val
       · rw [hZ x a (Or.inl h), mul_zero]
       · rw [hB' x (by omega)]
         simp)
    | (rename_i m b
       by_cases h : j ≤ b.val
       · rw [if_pos h]
         simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
         linear_combination -(∑ x, M m x * B b x) * hcc
       · rw [if_neg h, hB b (by omega)]
         simp)
    | (rw [ite_self, zero_add])
    | (rename_i a n
       apply Finset.sum_eq_zero
       intro x _
       by_cases h : j ≤ x.val
       · rw [hZ a x (Or.inr h), zero_mul]
       · rw [hB x (by omega)]
         simp)
    | (rename_i a b
       have hz : ∑ x, Z a x * (S x b - herm (Hb k) (B b) (B x) / 2) = 0 := by
         apply Finset.sum_eq_zero
         intro x _
         by_cases h : j ≤ x.val
         · rw [hZ a x (Or.inr h), zero_mul]
         · rw [hS x b (Or.inl (by omega)), hB x (by omega)]
           simp [herm]
       simp only [hz, zero_add, add_zero]
       split_ifs <;> simp_all)
    | (clear hee hew hes hwe hww hws hse hsw hss hD hZ hS hB hc hM hv1; done)

theorem exists_perm {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ)
    (h : BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) (Z.submatrix (Fin.castLE hj) (Fin.castLE hj))) :
    ∃ σ : Equiv.Perm (Fin r), (∀ a, (σ a).val < j ↔ a.val < j) ∧ (∀ a, β (σ a) = β a) ∧
      (∀ a : Fin r, a.val < j → Z a (σ a) ≠ 0 ∧ ∀ b : Fin r, b.val < j → b ≠ σ a → Z a b = 0) ∧
      ∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖Z a (σ a)‖ = ‖Z a' (σ a')‖ ∧ (a < a' → σ a' < σ a) := by
  obtain ⟨-, hdet, hblk, hrow⟩ := h
  have hex : ∀ a : Fin j, ∃ b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0 := by
    intro a
    by_contra hno
    push_neg at hno
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero a fun b => hno b)
  choose τ hτ using hex
  have hβτ : ∀ a, β (Fin.castLE hj a) = β (Fin.castLE hj (τ a)) := fun a => hblk a (τ a) (hτ a)
  have huniq : ∀ a b : Fin j, Z (Fin.castLE hj a) (Fin.castLE hj b) ≠ 0 → b = τ a := fun a b hb =>
    ((hrow a (τ a) a b (hτ a) hb rfl).2.1 rfl).symm
  have hτinj : Function.Injective τ := by
    intro a a' he
    by_contra hne
    have hb : β (Fin.castLE hj a) = β (Fin.castLE hj a') := by rw [hβτ a, hβτ a', he]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hrow a (τ a) a' (τ a') (hτ a) (hτ a') hb).2.2 hlt
      rw [he] at h1
      exact lt_irrefl _ h1
    · have h1 := (hrow a' (τ a') a (τ a) (hτ a') (hτ a) hb.symm).2.2 hlt
      rw [he] at h1
      exact lt_irrefl _ h1
  let f : Fin r → Fin r := fun a => if ha : a.val < j then Fin.castLE hj (τ ⟨a.val, ha⟩) else a
  have hf_c : ∀ a0 : Fin j, f (Fin.castLE hj a0) = Fin.castLE hj (τ a0) := fun a0 => dif_pos a0.isLt
  have hf_ge : ∀ a : Fin r, ¬ a.val < j → f a = a := fun a ha => dif_neg ha
  have hlift : ∀ a : Fin r, a.val < j → ∃ a0 : Fin j, Fin.castLE hj a0 = a := fun a ha =>
    ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  have hfinj : Function.Injective f := by
    intro a a' he
    by_cases ha : a.val < j <;> by_cases ha' : a'.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      obtain ⟨a1, rfl⟩ := hlift a' ha'
      rw [hf_c, hf_c] at he
      rw [hτinj (Fin.castLE_injective hj he)]
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c, hf_ge a' ha'] at he
      exact absurd (he ▸ (τ a0).isLt) ha'
    · obtain ⟨a1, rfl⟩ := hlift a' ha'
      rw [hf_c, hf_ge a ha] at he
      exact absurd (he.symm ▸ (τ a1).isLt) ha
    · rwa [hf_ge a ha, hf_ge a' ha'] at he
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [Equiv.ofBijective_apply]
    by_cases ha : a.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c]
      exact ⟨fun _ => ha, fun _ => (τ a0).isLt⟩
    · rw [hf_ge a ha]
  · intro a
    simp only [Equiv.ofBijective_apply]
    by_cases ha : a.val < j
    · obtain ⟨a0, rfl⟩ := hlift a ha
      rw [hf_c, hβτ a0]
    · rw [hf_ge a ha]
  · intro a ha
    simp only [Equiv.ofBijective_apply]
    obtain ⟨a0, rfl⟩ := hlift a ha
    rw [hf_c]
    refine ⟨hτ a0, fun b hb hne => ?_⟩
    obtain ⟨b0, rfl⟩ := hlift b hb
    by_contra hz
    exact hne (by rw [huniq a0 b0 hz])
  · intro a a' ha ha' hβ
    simp only [Equiv.ofBijective_apply]
    obtain ⟨a0, rfl⟩ := hlift a ha
    obtain ⟨a1, rfl⟩ := hlift a' ha'
    rw [hf_c, hf_c]
    obtain ⟨hn, -, hlt⟩ := hrow a0 (τ a0) a1 (τ a1) (hτ a0) (hτ a1) hβ
    refine ⟨hn, fun hlt' => ?_⟩
    have h2 := hlt (Fin.lt_def.mpr (Fin.lt_def.mp hlt'))
    exact Fin.lt_def.mpr (Fin.lt_def.mp h2)

theorem apply_of_mem_XstJ {j : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ XstJ k r j) {i : Fin (2 * r + k + 1)}
    (hi : ∀ b : Fin r, b.val < j → i ≠ esI k r b) : v i = 0 := by
  have hv' : v ∈ Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact Pi.single_eq_of_ne (hi a.1 a.2) 1
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem mulVec_bvec (g : Mat k r) (x i : Fin (2 * r + k + 1)) : (g *ᵥ bvec x) i = g i x := by
  show (g *ᵥ Pi.single x 1) i = g i x
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem H_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  have h1 : (Hpk k r * Hpk k r) i j = (Hpk k r *ᵥ (Hpk k r *ᵥ Pi.single j 1)) i := by
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp only [Formalism.QuantumDeterminants.gn_Hpk_mulVec, Pi.single_apply, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | norm_num

theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, H_sq, Matrix.det_one]
  have h := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact left_ne_zero_of_mul_eq_one hH h.symm

theorem pairing {g : Mat k r} (hg : g ∈ GG k r) (x i : Fin (2 * r + k + 1)) :
    ∑ a, star (g (esI k r a) x) * g (eI k r a) i + ∑ n, star (g (wI k r n) x) * sg k n * g (wI k r n) i +
      ∑ a, star (g (eI k r a) x) * g (esI k r a) i = Hpk k r x i := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [← congrFun (congrFun hg' x) i]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, sum3, H_ee, H_ew, H_es, H_we,
    H_ww, H_ws, H_se, H_sw, H_ss, mul_zero, zero_mul, mul_ite, ite_mul, mul_one, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]

private theorem apply_eq_ite_of_mulVec_bvec_eq_smul {g : Mat k r} {c : ℂ} {x : Fin (2 * r + k + 1)}
    (h : g *ᵥ bvec x = c • bvec x) (i : Fin (2 * r + k + 1)) : g i x = if i = x then c else 0 := by
  have e := congrFun h i
  rw [mulVec_bvec] at e
  rw [e]
  by_cases hi : i = x
  · subst hi; simp [bvec]
  · simp [bvec, Pi.single_apply, hi]

private theorem inv_eq_Hpk_mul_conjTranspose_mul_Hpk {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, H_sq]

private theorem Hpk_conj_apply_eI_eq_sum (g : Mat k r) (i : Fin (2 * r + k + 1)) (a : Fin r) :
    (Hpk k r * gᴴ * Hpk k r) i (eI k r a) = ∑ p, Hpk k r i p * star (g (esI k r a) p) := by
  rw [Matrix.mul_apply, sum3]
  simp only [H_ee, H_we, H_se, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

private theorem sum_mul_Hpk_eI_eq_apply_esI (f : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    ∑ i, f i * Hpk k r i (eI k r b) = f (esI k r b) := by
  rw [sum3]; simp [H_ee, H_we, H_se]

private theorem sum_Hpk_wI_mul_eq_sg_mul (f : Fin (2 * r + k + 1) → ℂ) (n : Fin (k + 1)) :
    ∑ p, Hpk k r (wI k r n) p * f p = sg k n * f (wI k r n) := by
  rw [sum3]; simp [H_we, H_ww, H_ws]

private theorem sum_Hpk_eI_mul_eq_apply_esI (f : Fin (2 * r + k + 1) → ℂ) (x : Fin r) :
    ∑ p, Hpk k r (eI k r x) p * f p = f (esI k r x) := by
  rw [sum3]; simp [H_ee, H_ew, H_es]

theorem exists_blocks {j : ℕ} (hj : j ≤ r) {β : Fin r → ℕ} {c : ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}
    (h : IsNormal0 k r hj β c z z' g) :
    ∃ (σ : Equiv.Perm (Fin r)) (t : Fin r → ℂ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∀ a, (σ a).val < j ↔ a.val < j) ∧ (∀ a, β (σ a) = β a) ∧ (∀ a : Fin r, a.val < j → t a ≠ 0) ∧
      (∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖t a‖ = ‖t a'‖ ∧ (a < a' → σ a' < σ a)) ∧ M ∈ UH (Hb k) ∧
      HasBlocks g (c • Fj r j) (Matrix.of fun a b => if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0)
        (Matrix.of fun a b => if a.val < j ∧ b = σ a then t a else 0) M := by
  obtain ⟨hgG, hc, -, -, -, hXJ, hfix, hBA⟩ := h
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_perm hj β (Zr k r g) hBA
  set t : Fin r → ℂ := fun a => Zr k r g a (σ a) with ht
  have cE : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (eI k r b) = if i = eI k r b then c else 0 :=
    fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).1 i
  have cS : ∀ b : Fin r, j ≤ b.val → ∀ i, g i (esI k r b) = if i = esI k r b then c else 0 :=
    fun b hb i => apply_eq_ite_of_mulVec_bvec_eq_smul (hfix b hb).2 i
  have cL : ∀ b : Fin r, b.val < j → ∀ i, (∀ a : Fin r, a.val < j → i ≠ esI k r a) → g i (eI k r b) = 0 := by
    intro b hb i hi
    have e := apply_of_mem_XstJ (hXJ b hb).2 hi
    rwa [mulVec_bvec] at e
  have hinv := inv_eq_Hpk_mul_conjTranspose_mul_Hpk hgG
  have rSw : ∀ a : Fin r, a.val < j → ∀ n, g (esI k r a) (wI k r n) = 0 := by
    intro a ha n
    have h0 := apply_of_mem_XstJ (hXJ a ha).1 (i := wI k r n) (fun b _ => wI_ne_esI n b)
    rw [mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_wI_mul_eq_sg_mul] at h0
    have hs : sg k n ≠ 0 := by rw [sg]; split_ifs <;> norm_num
    have h1 := (mul_eq_zero.mp h0).resolve_left hs
    simpa using h1
  have rSs : ∀ a : Fin r, a.val < j → ∀ x, g (esI k r a) (esI k r x) = 0 := by
    intro a ha x
    have h0 := apply_of_mem_XstJ (hXJ a ha).1 (i := eI k r x) (fun b _ => eI_ne_esI x b)
    rw [mulVec_bvec, hinv, Hpk_conj_apply_eI_eq_sum, sum_Hpk_eI_mul_eq_apply_esI] at h0
    simpa using h0
  have rS : ∀ a : Fin r, a.val < j → ∀ p, g (esI k r a) p = if p = eI k r (σ a) then t a else 0 := by
    intro a ha p
    refine cases3 (P := fun p => g (esI k r a) p = if p = eI k r (σ a) then t a else 0) ?_ ?_ ?_ p
    · intro x
      by_cases hx : x = σ a
      · subst hx; simp [ht, Zr]
      · rw [if_neg (by rw [eI_inj]; exact hx)]
        by_cases hxj : x.val < j
        · exact (s3 a ha).2 x hxj hx
        · rw [cE x (by omega) (esI k r a), if_neg (esI_ne_eI a x)]
    · intro n; rw [if_neg (wI_ne_eI n (σ a)), rSw a ha n]
    · intro x; rw [if_neg (esI_ne_eI x (σ a)), rSs a ha x]
  have cLs : ∀ a : Fin r, a.val < j → ∀ i,
      star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0 := by
    intro a ha i
    have hσ : (σ a).val < j := (s1 a).mpr ha
    refine cases3 (P := fun i => star (g i (eI k r (σ a))) = if i = esI k r a then star (t a) else 0)
      ?_ ?_ ?_ i
    · intro x; rw [if_neg (eI_ne_esI x a), cL (σ a) hσ _ (fun a' _ => eI_ne_esI x a'), star_zero]
    · intro n; rw [if_neg (wI_ne_esI n a), cL (σ a) hσ _ (fun a' _ => wI_ne_esI n a'), star_zero]
    · intro x
      by_cases hxj : x.val < j
      · rw [rS x hxj]
        by_cases hxa : x = a
        · subst hxa; simp
        · rw [if_neg (by rw [eI_inj]; exact fun h => hxa (σ.injective h).symm),
            if_neg (by rw [esI_inj]; exact hxa), star_zero]
      · rw [cL (σ a) hσ _ (fun a' ha' h => hxj (by rw [esI_inj] at h; rw [h]; exact ha')),
          if_neg (by rw [esI_inj]; rintro rfl; exact hxj ha), star_zero]
  have rElo : ∀ a : Fin r, a.val < j → ∀ y, star (t a) * g (eI k r a) y = Hpk k r (eI k r (σ a)) y := by
    intro a ha y
    have e := pairing hgG (eI k r (σ a)) y
    simp only [cLs a ha] at e
    rw [← e]
    simp [esI_inj, eI_ne_esI, wI_ne_esI]
  have rEhi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (eI k r a) y = Hpk k r (esI k r a) y := by
    intro a ha y
    have e := pairing hgG (esI k r a) y
    have hs : ∀ i, star (g i (esI k r a)) = if i = esI k r a then star c else 0 := by
      intro i; rw [cS a ha]; split_ifs <;> simp
    simp only [hs] at e
    rw [← e]; simp [esI_inj, wI_ne_esI, eI_ne_esI]
  have rShi : ∀ a : Fin r, j ≤ a.val → ∀ y, star c * g (esI k r a) y = Hpk k r (eI k r a) y := by
    intro a ha y
    have e := pairing hgG (eI k r a) y
    have hs : ∀ i, star (g i (eI k r a)) = if i = eI k r a then star c else 0 := by
      intro i; rw [cE a ha]; split_ifs <;> simp
    simp only [hs] at e
    rw [← e]; simp [eI_inj, wI_ne_eI, esI_ne_eI]
  have hcc : star c * c = 1 := by
    have h1 := Complex.normSq_eq_conj_mul_self (z := c)
    rw [Complex.normSq_eq_norm_sq, hc] at h1
    simpa using h1.symm
  have solC : ∀ X Y : ℂ, star c * X = Y → X = c * Y := fun X Y h => by
    rw [← h, ← mul_assoc, mul_comm c, hcc, one_mul]
  have gEw : ∀ (a : Fin r) n, g (eI k r a) (wI k r n) = 0 := by
    intro a n
    by_cases ha : a.val < j
    · have e := rElo a ha (wI k r n); rw [H_ew] at e
      exact (mul_eq_zero.mp e).resolve_left (star_ne_zero.mpr (s3 a ha).1)
    · rw [solC _ _ (rEhi a (by omega) (wI k r n)), H_sw, mul_zero]
  have gSw : ∀ (a : Fin r) n, g (esI k r a) (wI k r n) = 0 := by
    intro a n
    by_cases ha : a.val < j
    · exact rSw a ha n
    · rw [solC _ _ (rShi a (by omega) (wI k r n)), H_ew, mul_zero]
  have hmul : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
    rw [← hinv]; exact Matrix.mul_nonsing_inv g (isUnit_det_of_mem hgG)
  have gWs : ∀ n (b : Fin r), g (wI k r n) (esI k r b) = 0 := by
    intro n b
    by_cases hb : j ≤ b.val
    · rw [cS b hb, if_neg (wI_ne_esI n b)]
    · obtain ⟨a, rfl⟩ := σ.surjective b
      have ha : a.val < j := (s1 a).mp (by omega)
      have e := congrFun (congrFun hmul (wI k r n)) (eI k r a)
      rw [Matrix.mul_apply, Matrix.one_apply_ne (wI_ne_eI n a)] at e
      have inner : ∀ i, (Hpk k r * gᴴ * Hpk k r) i (eI k r a) = Hpk k r i (eI k r (σ a)) * star (t a) := by
        intro i
        rw [Hpk_conj_apply_eI_eq_sum, Finset.sum_eq_single (eI k r (σ a))]
        · rw [rS a ha, if_pos rfl]
        · intro p _ hp; rw [rS a ha, if_neg hp, star_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [inner, ← mul_assoc] at e
      rw [← Finset.sum_mul, sum_mul_Hpk_eI_eq_apply_esI] at e
      exact (mul_eq_zero.mp e).resolve_right (star_ne_zero.mpr (s3 a ha).1)
  refine ⟨σ, t, Matrix.of fun m n => g (wI k r m) (wI k r n), s1, s2, fun a ha => (s3 a ha).1, s4, ?_, ?_⟩
  · show (_ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᴴ * Hb k * _ = Hb k
    ext m m'
    have e := pairing hgG (wI k r m) (wI k r m')
    simp only [gEw, gSw, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero, H_ww] at e
    rw [Hb_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_eq_single n]
    · simp [Hb_apply, Matrix.conjTranspose_apply, Matrix.of_apply, mul_assoc]
    · intro n' _ hn'; simp [Hb_apply, hn']
    · simp
  · refine ⟨?_, gEw, ?_, ?_, fun m n => rfl, gWs, ?_, gSw, ?_⟩
    · intro a b
      simp only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hb : j ≤ b.val
      · rw [cE b hb]
        by_cases hab : a = b
        · subst hab; simp [hb]
        · simp [eI_inj, hab]
      · rw [cL b (by omega) _ (fun a' _ => eI_ne_esI a a')]
        by_cases hab : a = b
        · subst hab; simp [hb]
        · simp [hab]
    · intro a b
      simp only [Matrix.of_apply]
      by_cases ha : a.val < j
      · have e := rElo a ha (esI k r b)
        rw [H_es] at e
        have hst : star (t a) ≠ 0 := star_ne_zero.mpr (s3 a ha).1
        rw [show g (eI k r a) (esI k r b) = (star (t a))⁻¹ * (if σ a = b then 1 else 0) by
          rw [← e, ← mul_assoc, inv_mul_cancel₀ hst, one_mul]]
        by_cases hb : b = σ a
        · subst hb; simp [ha]
        · rw [if_neg (fun h => hb h.symm), mul_zero, if_neg (fun h => hb h.2)]
      · rw [solC _ _ (rEhi a (by omega) (esI k r b)), H_ss, mul_zero]; simp [ha]
    · intro n b
      by_cases hb : j ≤ b.val
      · rw [cE b hb, if_neg (wI_ne_eI n b)]
      · exact cL b (by omega) _ (fun a' _ => wI_ne_esI n a')
    · intro a b
      simp only [Matrix.of_apply]
      by_cases ha : a.val < j
      · rw [rS a ha]
        by_cases hb : b = σ a
        · subst hb; simp [ha]
        · rw [if_neg (by rw [eI_inj]; exact hb)]; simp [hb]
      · rw [solC _ _ (rShi a (by omega) (eI k r b)), H_ee, mul_zero]; simp [ha]
    · intro a b
      simp only [Matrix.smul_apply, Fj, Matrix.diagonal_apply, smul_eq_mul]
      by_cases ha : a.val < j
      · rw [rSs a ha b]
        by_cases hab : a = b
        · subst hab; simp [show ¬ j ≤ a.val by omega]
        · simp [hab]
      · rw [solC _ _ (rShi a (by omega) (esI k r b)), H_es]
        by_cases hab : a = b
        · subst hab; simp [show j ≤ a.val by omega]
        · simp [hab]

theorem exists_phi {j : ℕ} {β : Fin r → ℕ} (hβ : ∀ a b : Fin r, β a = β b → (a.val < j ↔ b.val < j))
    (σ : Equiv.Perm (Fin r)) (t : Fin r → ℂ) (s1 : ∀ a, (σ a).val < j ↔ a.val < j) (s2 : ∀ a, β (σ a) = β a)
    (s3 : ∀ a : Fin r, a.val < j → t a ≠ 0)
    (s4 : ∀ a a' : Fin r, a.val < j → a'.val < j → β a = β a' → ‖t a‖ = ‖t a'‖ ∧ (a < a' → σ a' < σ a)) :
    ∃ Φ : (UTin β → ℂ) → (UTin β → ℂ), MeasurePreserving Φ volume volume ∧ ∀ x a b, upperIn β (Φ x) a b =
      (if a.val < j ∧ b.val < j then (star (t a))⁻¹ * star ((upperIn β x)⁻¹ (σ b) (σ a)) * star (t b) else 0) +
        (if j ≤ a.val then upperIn β x a b else 0) := by
  have hb_of : ∀ p : UTin β, p.1.1.1.val < j → p.1.1.2.val < j := fun p h => (hβ _ _ p.2).mp h
  have hlt : ∀ p : UTin β, p.1.1.1.val < j → σ p.1.1.2 < σ p.1.1.1 :=
    fun p h => (s4 _ _ h (hb_of p h) p.2).2 p.1.2
  have hbeta : ∀ p : UTin β, β (σ p.1.1.2) = β (σ p.1.1.1) := fun p => by rw [s2, s2]; exact p.2.symm
  let τ : UTin β → UTin β := fun p =>
    if h : p.1.1.1.val < j then ⟨⟨(σ p.1.1.2, σ p.1.1.1), hlt p h⟩, hbeta p⟩ else p
  have hτ : Function.Injective τ := by
    intro p q hpq
    by_cases hp : p.1.1.1.val < j
    · by_cases hq : q.1.1.1.val < j
      · simp only [τ, dif_pos hp, dif_pos hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1) hpq
        simp only [Prod.mk.injEq] at h1
        apply Subtype.ext; apply Subtype.ext
        exact Prod.ext (σ.injective h1.2) (σ.injective h1.1)
      · simp only [τ, dif_pos hp, dif_neg hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1.1.val) hpq
        simp only at h1
        exact absurd (by rw [← h1]; exact (s1 _).mpr (hb_of p hp)) hq
    · by_cases hq : q.1.1.1.val < j
      · simp only [τ, dif_neg hp, dif_pos hq] at hpq
        have h1 := congrArg (fun u : UTin β => u.1.1.1.val) hpq
        simp only at h1
        exact absurd (by rw [h1]; exact (s1 _).mpr (hb_of q hq)) hp
      · simp only [τ, dif_neg hp, dif_neg hq] at hpq
        exact hpq
  let e : UTin β ≃ UTin β := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτ)
  let A : UTin β → ℂ := fun p => -((star (t p.1.1.1))⁻¹ * star (t p.1.1.2))
  let F : UTin β → ℂ → ℂ := fun p z => if p.1.1.1.val < j then A p * star z else z
  have hF : ∀ p, MeasurePreserving (F p) volume volume := by
    intro p
    by_cases hp : p.1.1.1.val < j
    · have hb := hb_of p hp
      have hA : ‖A p‖ = 1 := by
        simp only [A, norm_neg, norm_mul, norm_inv, norm_star]
        rw [(s4 _ _ hp hb p.2).1]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (s3 _ hb))
      have hFp : F p = fun z => A p * star z := by funext z; simp only [F, if_pos hp]
      rw [hFp]; exact mul_star_mp hA
    · have hFp : F p = id := by funext z; simp only [F, if_neg hp, id]
      rw [hFp]; exact MeasurePreserving.id volume
  have hP : MeasurePreserving (fun y : UTin β → ℂ => fun p => y (e p)) volume volume := by
    have h0 := volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)
    exact h0
  have hC : MeasurePreserving (fun w : UTin β → ℂ => fun p => F p (w p)) volume volume :=
    volume_preserving_pi hF
  have key : ∀ (w : UTin β → ℂ) (a b : Fin r), upperIn β w a b =
      if h : a < b then (if h' : β a = β b then w ⟨⟨(a, b), h⟩, h'⟩ else 0) else if a = b then 1 else 0 := by
    intro w a b; rfl
  refine ⟨fun x => fun p => F p (shearInv j β x (e p)), (hC.comp hP).comp (shearInv_mp j β), ?_⟩
  intro x a b
  have hdiag : ∀ c, (upperIn β x)⁻¹ c c = 1 := fun c => inv_upper_diag _ c
  have hgt : ∀ c d, d < c → (upperIn β x)⁻¹ c d = 0 := fun c d h => inv_upper_gt _ h
  beta_reduce
  rw [key]
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [dif_pos hab]
    by_cases hβab : β a = β b
    · rw [dif_pos hβab]
      by_cases ha : a.val < j
      · have hb : b.val < j := (hβ a b hβab).mp ha
        have hσ : (σ b).val < j := (s1 b).mpr hb
        simp only [F, e, Equiv.ofBijective_apply, τ, A, dif_pos ha, if_pos ha, shearInv, dif_pos hσ,
          if_pos hσ, if_pos (And.intro ha hb), if_neg (show ¬ j ≤ a.val by omega), star_neg, add_zero]
        ring
      · have hja : j ≤ a.val := by omega
        simp only [F, e, Equiv.ofBijective_apply, τ, dif_neg ha, if_neg ha, shearInv,
          if_neg (show ¬ (a.val < j ∧ b.val < j) from fun h => ha h.1), if_pos hja, zero_add]
        rw [key, dif_pos hab, dif_pos hβab]
    · rw [dif_neg hβab]
      have h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0 :=
        inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)
      rw [h1, key, dif_pos hab, dif_neg hβab]; simp
  · rw [dif_neg (lt_irrefl _), if_pos rfl, hdiag]
    by_cases ha : a.val < j
    · rw [if_pos ⟨ha, ha⟩, if_neg (show ¬ j ≤ a.val by omega), star_one, mul_one,
        inv_mul_cancel₀ (star_ne_zero.mpr (s3 a ha)), add_zero]
    · rw [if_neg (fun h : a.val < j ∧ a.val < j => ha h.1), if_pos (show j ≤ a.val by omega), key,
        dif_neg (lt_irrefl _), if_pos rfl, zero_add]
  · rw [dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]
    have h2 : upperIn β x a b = 0 := by rw [key, dif_neg (not_lt.mpr hab.le), if_neg (ne_of_gt hab)]
    by_cases hj2 : a.val < j ∧ b.val < j
    · have h1 : (upperIn β x)⁻¹ (σ b) (σ a) = 0 := by
        by_cases hβab : β a = β b
        · exact hgt _ _ ((s4 b a hj2.2 hj2.1 hβab.symm).2 hab)
        · exact inv_upperIn_ne β x (by rw [s2, s2]; exact fun h => hβab h.symm)
      rw [h1, h2]; simp
    · rw [if_neg hj2, h2]; simp

theorem continuous_rEl (j : ℕ) (β : Fin r → ℕ) : Continuous (rEl k r j β) := by
  unfold rEl
  refine Continuous.matrix_mul ?_ ?_
  · refine continuous_pi fun i => continuous_pi fun i' => ?_
    have hU : Continuous fun q : (UTin β → ℂ) × PTop k r j => upperIn β q.1 := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [upperIn, upper]
      split_ifs <;> first | exact (continuous_apply _).comp continuous_fst | exact continuous_const
    have hI : Continuous fun q : (UTin β → ℂ) × PTop k r j => (upperIn β q.1)⁻¹ :=
      (continuous_inv_upperIn β).comp continuous_fst
    simp only [uEmb]
    split_ifs
    · exact (continuous_apply _).comp ((continuous_apply _).comp hU)
    · exact continuous_star.comp ((continuous_apply _).comp ((continuous_apply _).comp hI))
    · exact continuous_const
    · exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun i' => ?_
    simp only [pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]
    split_ifs <;> fun_prop

private lemma perm_weighted_mul_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (P * A) a b = if a.val < j then f a * A (σ a) b else 0 := by
  rw [Matrix.mul_apply]
  by_cases ha : a.val < j
  · simp [hP, ha]
  · simp [hP, ha]

private lemma mul_perm_weighted_conjTranspose_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (A * Pᴴ) a b = if b.val < j then A a (σ b) * star (f b) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hb : b.val < j
  · rw [if_pos hb, Finset.sum_eq_single (σ b)]
    · simp [Matrix.conjTranspose_apply, hP, hb]
    · intro d _ hd
      simp [Matrix.conjTranspose_apply, hP, hd]
    · simp
  · simp [Matrix.conjTranspose_apply, hP, hb]

private lemma perm_weighted_conjTranspose_mul_apply {r j : ℕ} (σ : Equiv.Perm (Fin r)) (s1 : ∀ a, (σ a).val < j ↔ a.val < j)
    (P A : Matrix (Fin r) (Fin r) ℂ) (f : Fin r → ℂ)
    (hP : ∀ a b, P a b = if a.val < j ∧ b = σ a then f a else 0) (a b : Fin r) :
    (Pᴴ * A) a b = if a.val < j then star (f (σ.symm a)) * A (σ.symm a) b else 0 := by
  have h' : (σ.symm a).val < j ↔ a.val < j := by simpa using (s1 (σ.symm a)).symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
  · by_cases ha : a.val < j
    · simp [Matrix.conjTranspose_apply, hP, ha, h']
    · simp [Matrix.conjTranspose_apply, hP, ha, h']
  · intro c _ hc
    have hne : a ≠ σ c := fun h => hc (by rw [h, Equiv.symm_apply_apply])
    simp [Matrix.conjTranspose_apply, hP, hne]
  · simp

theorem lebR0_map_conjM_eq_of_isNormalZero : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → (lebR0 k r j β).map (conjM g₀) = lebR0 k r j β := by
  intro k r j hj z z' g₀ β c _ _ _ hN
  obtain ⟨σ, t, M, s1, s2, s3, s4, hM, hB⟩ := exists_blocks hj hN
  set Ym : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0 with hYm
  set Zm : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a.val < j ∧ b = σ a then t a else 0 with hZm
  have hYP : ∀ a b, Ym a b = if a.val < j ∧ b = σ a then (star (t a))⁻¹ else 0 := fun _ _ => rfl
  have hZP : ∀ a b, Zm a b = if a.val < j ∧ b = σ a then t a else 0 := fun _ _ => rfl
  have hc : ‖c‖ = 1 := hN.2.1
  have hβ : ∀ a b : Fin r, β a = β b → (a.val < j ↔ b.val < j) := by
    intro a b hab
    have h5 := hN.2.2.2.2.1
    constructor
    · intro ha
      by_contra hb
      have := (h5 a b (not_lt.mp hb)).1 hab
      omega
    · intro hb
      by_contra ha
      have := (h5 b a (not_lt.mp ha)).1 hab.symm
      omega
  obtain ⟨Φ, hΦ, hΦu⟩ := exists_phi hβ σ t s1 s2 s3 s4
  have hF : (Fj r j)ᴴ = Fj r j := by
    ext a b
    simp only [Fj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; split_ifs <;> simp
    · simp [hab, Ne.symm hab]
  have hFF : Fj r j * Fj r j = Fj r j := by
    simp only [Fj, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    split_ifs <;> simp
  have hFY : Fj r j * Ym = 0 := by
    ext a b
    simp only [Fj, Matrix.diagonal_mul, hYP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · have : ¬ j ≤ a.val := by omega
      simp [this]
    · simp [ha]
  have hFZ : Fj r j * Zm = 0 := by
    ext a b
    simp only [Fj, Matrix.diagonal_mul, hZP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · have : ¬ j ≤ a.val := by omega
      simp [this]
    · simp [ha]
  have hYF : Ym * Fj r j = 0 := by
    ext a b
    simp only [Fj, Matrix.mul_diagonal, hYP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · by_cases hb : b = σ a
      · subst hb
        have : ¬ j ≤ (σ a).val := by have := (s1 a).2 ha; omega
        simp [this]
      · simp [hb]
    · simp [ha]
  have hZF : Zm * Fj r j = 0 := by
    ext a b
    simp only [Fj, Matrix.mul_diagonal, hZP, Matrix.zero_apply]
    by_cases ha : a.val < j
    · by_cases hb : b = σ a
      · subst hb
        have : ¬ j ≤ (σ a).val := by have := (s1 a).2 ha; omega
        simp [this]
      · simp [hb]
    · simp [ha]
  have hYZ : Ymᴴ * Zm = 1 - Fj r j := by
    ext a b
    rw [perm_weighted_conjTranspose_mul_apply σ s1 Ym Zm _ hYP, hZP]
    have h' : (σ.symm a).val < j ↔ a.val < j := by simpa using (s1 (σ.symm a)).symm
    simp only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply, Equiv.apply_symm_apply, h']
    by_cases ha : a.val < j
    · have ht := s3 _ ((h').2 ha)
      by_cases hab : b = a
      · subst hab; simp [ha, ht, not_le.mpr ha]
      · simp [ha, hab, Ne.symm hab]
    · have hja : j ≤ a.val := by omega
      by_cases hab : a = b
      · subst hab; simp [ha, hja]
      · simp [ha, hab]
  have hZY : Ym * Zmᴴ = 1 - Fj r j := by
    ext a b
    rw [mul_perm_weighted_conjTranspose_apply σ Zm Ym _ hZP, hYP]
    simp only [Matrix.sub_apply, Matrix.one_apply, Fj, Matrix.diagonal_apply]
    by_cases hb : b.val < j
    · have ht := s3 _ hb
      by_cases hab : a = b
      · subst hab; simp [hb, ht, not_le.mpr hb]
      · have : ¬ (σ b = σ a) := fun h => hab (σ.injective h).symm
        simp [hb, hab, this]
    · have hjb : j ≤ b.val := by omega
      by_cases hab : a = b
      · subst hab; simp [hb, hjb]
      · simp [hb, hab]
  have huF : ∀ x : UTin β → ℂ, upperIn β x * Fj r j = Fj r j * upperIn β x := by
    intro x
    ext a b
    simp only [Fj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : β a = β b
    · have hiff := hβ a b hab
      by_cases ha : j ≤ a.val
      · have hb : j ≤ b.val := by
          by_contra h
          exact absurd (hiff.2 (by omega)) (by omega)
        simp [ha, hb]
      · have hb : ¬ j ≤ b.val := by
          intro h
          exact absurd (hiff.1 (by omega)) (by omega)
        simp [ha, hb]
    · rw [upperIn_ne β x hab]; simp
  have hU : ∀ x : UTin β → ℂ, g₀ * uEmb k r (upperIn β x) = uEmb k r (upperIn β (Φ x)) * g₀ := by
    intro x
    have hu : IsUnit (upperIn β x).det := isUnit_upper _
    obtain ⟨h1, h2, h3, h4⟩ := alg c hu hF hFF hYZ hZY hFY hYF hFZ hZF (huF x)
    have key : Ym * ((upperIn β x)⁻¹)ᴴ * Zmᴴ + Fj r j * upperIn β x = upperIn β (Φ x) := by
      ext a b
      rw [hΦu, Matrix.add_apply, Matrix.mul_assoc, perm_weighted_mul_apply σ Ym _ _ hYP,
        mul_perm_weighted_conjTranspose_apply σ Zm _ _ hZP]
      simp only [Fj, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
      by_cases ha : a.val < j <;> by_cases hb : b.val < j <;> simp [ha, hb] <;> ring_nf <;> omega
    rw [← key]
    exact conj_u hB h1 h2 h3 h4
  have hZ0 : ∀ a b : Fin r, j ≤ a.val ∨ j ≤ b.val → Zm a b = 0 := by
    intro a b hab
    rw [hZP]
    split_ifs with h
    · obtain ⟨ha, rfl⟩ := h
      have := (s1 a).2 ha
      omega
    · rfl
  let L : PTop k r j → PTop k r j := fun q => (fun a => star c • M *ᵥ q.1 a, q.2)
  have hP : ∀ q : PTop k r j, g₀ * pTop k r j q = pTop k r j (L q) * g₀ := by
    intro q
    have e1 : pTop k r j q = pEl k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0)
        (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) := rfl
    have e2 : pTop k r j (L q) = pEl k r (fun a => star c • M *ᵥ (if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0))
        (skewM (fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0) (fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)) := by
      simp only [pTop, pOf, L]
      congr 1
      funext a
      split_ifs <;> simp
    rw [e1, e2]
    refine conj_p hB hc hM hZ0 _ _ ?_ ?_
    · intro a ha
      rw [dif_neg (by omega)]
    · intro a b hab
      simp only [skewM]
      by_cases h1 : a < b
      · have ha : ¬ j ≤ a.val := by
          have := Fin.lt_iff_val_lt_val.mp h1
          omega
        simp [h1, ha]
      · by_cases h2 : b < a
        · have hb : ¬ j ≤ b.val := by
            have := Fin.lt_iff_val_lt_val.mp h2
            omega
          simp [h1, h2, hb]
        · have hab' : a = b := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
          subst hab'
          have ha : ¬ j ≤ a.val := by omega
          simp [ha]
  have hLmp : MeasurePreserving L volume volume := by
    have hdet : Complex.normSq (star c • M).det = 1 := by
      have hs : Complex.normSq (star c) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_star, hc]
        norm_num
      rw [Matrix.det_smul, map_mul, map_pow, hs, one_pow, one_mul, normSq_det_of_mem hM]
    have h0 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) volume volume := mulVec_mp hdet
    have e : (fun v : Fin (k + 1) → ℂ => (star c • M) *ᵥ v) = fun v => star c • M *ᵥ v := by
      funext v i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have h1 : MeasurePreserving (fun v : Fin (k + 1) → ℂ => star c • M *ᵥ v) volume volume := e ▸ h0
    have h2 : MeasurePreserving (fun B : {a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ => fun a => star c • M *ᵥ B a)
        volume volume := by
      simpa [volume_pi] using measurePreserving_pi (fun _ => (volume : Measure (Fin (k + 1) → ℂ)))
        (fun _ => (volume : Measure (Fin (k + 1) → ℂ))) (fun _ => h1)
    have h3 := h2.prod (MeasurePreserving.id (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    exact h3
  haveI : SFinite (volume : Measure (PTop k r j)) := by
    haveI : SFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod
      (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ))) := inferInstance
    haveI : SFinite (volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)) := inferInstance
    exact (inferInstance : SFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod
      ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))))
  haveI : OpensMeasurableSpace ((UTin β → ℂ) × PTop k r j) := by
    haveI : OpensMeasurableSpace (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)) := inferInstance
    haveI : OpensMeasurableSpace (PTop k r j) := inferInstance
    infer_instance
  let Ψ : (UTin β → ℂ) × PTop k r j → (UTin β → ℂ) × PTop k r j := fun q => (Φ q.1, L q.2)
  have hΨ : MeasurePreserving Ψ (volume.prod volume) (volume.prod volume) := hΦ.prod hLmp
  have hg : IsUnit g₀.det := isUnit_det_of_mem hN.1
  have hcomp : (conjM g₀) ∘ (fun q => Matrix.of.symm (rEl k r j β q)) = (fun q => Matrix.of.symm (rEl k r j β q)) ∘ Ψ := by
    funext q
    simp only [Function.comp, conjM, rEl, Equiv.apply_symm_apply]
    show g₀ * (uEmb k r (upperIn β q.1) * pTop k r j q.2) * g₀⁻¹ = uEmb k r (upperIn β (Φ q.1)) * pTop k r j (L q.2)
    rw [← Matrix.mul_assoc, hU, Matrix.mul_assoc (uEmb k r (upperIn β (Φ q.1))) g₀, hP, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
  have hmR : Measurable fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q) :=
    have hcR : Continuous fun q : (UTin β → ℂ) × PTop k r j => Matrix.of.symm (rEl k r j β q) := continuous_rEl j β
    hcR.measurable
  have hmC : Measurable (conjM (k := k) (r := r) g₀) := by
    have hc2 : Continuous fun x : Mt k r => Matrix.of x := continuous_id
    have hc3 : Continuous (conjM (k := k) (r := r) g₀) := by
      unfold conjM
      exact (continuous_const.matrix_mul hc2).matrix_mul continuous_const
    exact hc3.measurable
  unfold lebR0
  rw [Measure.volume_eq_prod, Measure.map_map hmC hmR, hcomp, ← Measure.map_map hmR hΨ.measurable, hΨ.map_eq]

end GlobalTheory.Amp.RConj
