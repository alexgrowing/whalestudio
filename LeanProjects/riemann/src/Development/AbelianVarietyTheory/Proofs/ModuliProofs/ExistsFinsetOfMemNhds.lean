import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits

open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodCoord

noncomputable section

variable {g : ℕ}

theorem herm_add_left (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm M (z + z') w = hermForm M z w + hermForm M z' w := by
  simp [hermForm]

theorem herm_add_right (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm M z (w + w') = hermForm M z w + hermForm M z w' := by
  simp [hermForm, mulVec_add]

theorem herm_smul_left (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm M (c • z) w = c * hermForm M z w := by
  simp [hermForm]

theorem herm_smul_right (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm M z (c • w) = conj c * hermForm M z w := by
  simp [hermForm, mulVec_smul]

theorem herm_conj {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (z w : Fin g → ℂ) :
    hermForm M z w = conj (hermForm M w z) := by
  simp only [hermForm, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM.apply j i]
  simp only [RCLike.star_def, Complex.conj_conj]
  ring

def imForm (M : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm M z w).im)
    (fun z z' w => by rw [herm_add_left, Complex.add_im])
    (fun c z w => by
      rw [show c • z = (c : ℂ) • z from rfl, herm_smul_left]; simp)
    (fun z w w' => by rw [herm_add_right, Complex.add_im])
    (fun c z w => by
      rw [show c • w = (c : ℂ) • w from rfl, herm_smul_right]; simp)

theorem imForm_apply (M : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm M z w = (hermForm M z w).im := rfl

def realMap (A B : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z := A *ᵥ z + B *ᵥ star z
  map_add' z w := by simp only [star_add, mulVec_add]; abel
  map_smul' c z := by
    change A *ᵥ ((c : ℂ) • z) + B *ᵥ star ((c : ℂ) • z) = (c : ℂ) • _
    simp only [star_smul, mulVec_smul, smul_add, RCLike.star_def, Complex.conj_ofReal]

theorem realMap_apply (A B : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    realMap A B z = A *ᵥ z + B *ᵥ star z := rfl

theorem realMap_inj {A B A' B' : Matrix (Fin g) (Fin g) ℂ} (h : realMap A B = realMap A' B') :
    A = A' ∧ B = B' := by
  have key : ∀ i j, A i j = A' i j ∧ B i j = B' i j := fun i j => by
    have h1 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    have h2 := congrFun (LinearMap.congr_fun h (Pi.single j Complex.I)) i
    simp only [realMap_apply, ← Pi.single_star, star_one, mulVec_single, Pi.add_apply,
      RCLike.star_def, Complex.conj_I] at h1 h2
    simp at h1 h2
    have hI := Complex.I_mul_I
    constructor
    · linear_combination h1 / 2 - Complex.I / 2 * h2 + (A i j - B i j - A' i j + B' i j) / 2 * hI
    · linear_combination h1 / 2 + Complex.I / 2 * h2 - (A i j - B i j - A' i j + B' i j) / 2 * hI
  exact ⟨Matrix.ext fun i j => (key i j).1, Matrix.ext fun i j => (key i j).2⟩

theorem riemann_symm {M M₀ C : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (h : ∀ z w, (hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im) (i j : Fin g) :
    (Cᵀ * M₀) i j = (Cᵀ * M₀) j i := by
  set c : (Fin g → ℂ) → (Fin g → ℂ) := fun z => C *ᵥ star z with hc
  have hcI : ∀ z, c (Complex.I • z) = (-Complex.I) • c z := fun z => by
    simp [hc, mulVec_smul, mulVec_neg]
  have key : ∀ z w, hermForm M (c w) z = hermForm M (c z) w ∧
      hermForm M₀ z w = hermForm M z w - hermForm M (c w) (c z) := fun z w => by
    have h1 : (hermForm M (z + c z) (w + c w)).im = _ := h z w
    have h2 : (hermForm M (_ + c _) (_ + c _)).im = _ := h (Complex.I • z) (Complex.I • w)
    have h3 : (hermForm M (_ + c _) (_ + c _)).im = _ := h (Complex.I • z) w
    have h4 : (hermForm M (_ + c _) (_ + c _)).im = _ := h z (Complex.I • w)
    simp only [hcI, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right] at h1 h2 h3 h4
    simp at h1 h2 h3 h4
    rw [herm_conj hM (c w) z, herm_conj hM (c w) (c z)]
    refine ⟨Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩ <;> simp <;> linarith
  have key2 : ∀ z w, hermForm M₀ (c z) w = hermForm M₀ (c w) z := fun z w => by
    rw [(key _ _).2, (key _ _).2, (key z w).1, herm_conj hM (c w) (c (c z)), (key (c w) (c z)).1,
      ← herm_conj hM]
  have := key2 (Pi.single i 1) (Pi.single j 1)
  simpa [hc, hermForm, ← Pi.single_star, mul_apply, dotProduct] using this

theorem eq_zero_of_imForm {M : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) {u : Fin g → ℂ} (h : imForm M u = 0) : u = 0 := by
  by_contra hu
  have h1 := LinearMap.congr_fun h (Complex.I • u)
  have h2 := hpos u hu
  rw [imForm_apply, herm_smul_right] at h1
  simp at h1
  linarith

theorem det_ne_zero_of_pos {M : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) : M.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := exists_vecMul_eq_zero_iff.2 h
  have := hpos v hv
  rw [hermForm, dotProduct_mulVec, h0] at this
  simp at this

theorem exists_finset_of_mem_nhds {L : Type} {f₀ : L → Fin g → ℂ} {U : Set (L → Fin g → ℂ)} (hU : U ∈ nhds f₀) :
    ∃ (s : Finset L) (ε : ℝ), 0 < ε ∧ ∀ f, (∀ x ∈ s, ‖f x - f₀ x‖ < ε) → f ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, t, ht, hs⟩ := hU
  have : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ x ∈ s, Metric.ball (f₀ x) ε ⊆ t x := by
    rw [Filter.eventually_all_finset]
    intro x _
    exact (eventually_ball_subset (ht x)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨s, ε, h2, fun f hf => hs fun x hx => h1 x hx (by simpa [dist_eq_norm] using hf x hx)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}

theorem ext_period {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_period hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

def colMat {L : Type} (α : Fin g → (L →₀ ℂ)) (f : L → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => ∑ x ∈ (α j).support, α j x * f x i

theorem colMat_apply {L : Type} (α : Fin g → (L →₀ ℂ)) (f : L → Fin g → ℂ) (i j : Fin g) :
    colMat α f i j = Finsupp.linearCombination ℂ f (α j) i := by
  simp [colMat, Finsupp.linearCombination_apply, Finsupp.sum]

theorem exists_colMat {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ty P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by
    simp only [map_sub, map_sum, map_add, map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])
  simp only [map_sub, map_sum, map_add, map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add, map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

def actMat (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Matrix (Fin g) (Fin g) ℂ := diagonal fun i => ty i (a : E)

theorem period_smul {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (a : 𝓞 E) (x : D.La) :
    P (a • x) = actMat ty a *ᵥ P x := by
  funext i
  rw [hP.1, actMat, mulVec_diagonal]

theorem star_actMat (a : 𝓞 E) (z : Fin g → ℂ) : star (actMat ty a *ᵥ z) = actMat ty (H.bar a) *ᵥ star z := by
  funext i
  simp [actMat, mulVec_diagonal, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem comm_of_realMap {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : 𝓞 E) :
    actMat ty a * A = A * actMat ty a ∧ actMat ty a * B = B * actMat ty (H.bar a) := by
  refine realMap_inj (ext_period hP₀ fun x => ?_)
  have := h (a • x)
  rw [period_smul hP, period_smul hP₀, h] at this
  simp only [realMap_apply, star_actMat (H := H), mulVec_add, mulVec_mulVec] at this ⊢
  exact this

theorem comm_herm {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : 𝓞 E) :
    actMat ty a * M = M * actMat ty a := by
  have key : (imForm M).compl₁₂ (realMap (actMat ty a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (actMat ty (H.bar a)) 0) := by
    refine ext_period hP₀ fun x => ext_period hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← period_smul hP₀, imForm_apply, hM, D.adj]
  ext i j
  have h1 := LinearMap.congr_fun₂ key (Pi.single i 1) (Pi.single j 1)
  have h2 := LinearMap.congr_fun₂ key (Pi.single i Complex.I) (Pi.single j 1)
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply, actMat, diagonal_mulVec_single, hermForm, ← Pi.single_star, H.bar_eq,
    IsCMField.complexEmbedding_complexConj] at h1 h2
  simp only [actMat, diagonal_mul, mul_diagonal]
  simp at h1 h2
  apply Complex.ext <;> simp <;> linarith

theorem symm_and_support {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) (i j : Fin g) :
    ((A⁻¹ * B)ᵀ * M₀) i j = ((A⁻¹ * B)ᵀ * M₀) j i ∧
      (ty j ≠ ComplexEmbedding.conjugate (ty i) → ((A⁻¹ * B)ᵀ * M₀) i j = 0) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_period hP₀ fun x => ext_period hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) i j
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · intro hij
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, ty j (a : E) ≠ ComplexEmbedding.conjugate (ty i) (a : E) := by
      by_contra hc
      push Not at hc
      exact hij (IsFractionRing.ringHom_ext (A := 𝓞 E) hc)
    obtain ⟨h1, h2⟩ := comm_of_realMap hP₀ hP h a
    have h3 : actMat ty a * (A⁻¹ * B) = A⁻¹ * B * actMat ty (H.bar a) := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (actMat ty a * A) * A⁻¹ = A⁻¹ * (A * actMat ty a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    have h4 : (A⁻¹ * B)ᵀ * M₀ * actMat ty a = actMat ty (H.bar a) * ((A⁻¹ * B)ᵀ * M₀) := by
      have := congrArg transpose h3
      rw [transpose_mul, transpose_mul (A⁻¹ * B), actMat, actMat, diagonal_transpose, diagonal_transpose] at this
      rw [Matrix.mul_assoc, ← comm_herm hP₀ hM₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, actMat, actMat, this]
    have h5 := congrFun (congrFun h4 i) j
    rw [actMat, actMat, mul_diagonal, diagonal_mul, H.bar_eq, IsCMField.complexEmbedding_complexConj] at h5
    rw [ComplexEmbedding.conjugate_coe_eq] at ha
    have h6 : ((A⁻¹ * B)ᵀ * M₀) i j * (ty j (a : E) - conj (ty i (a : E))) = 0 := by linear_combination h5
    exact (mul_eq_zero.1 h6).resolve_right (sub_ne_zero.2 ha)

theorem conjugate_mem_iff (H : Host E) (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h1 h2
    by_contra h0
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : conj H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ -H.rt0 := fun h => by
    have h1 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h1] at this
    simp at this
    simp [this] at hd
  have hsq : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simp at this
    rw [H.sqrt_neg_disc_sq, ← this]
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases hsq with h | h <;> rw [h]
  · rw [hc]; exact ⟨fun h' => (hne h'.symm).elim, fun h' => (h' rfl).elim⟩
  · rw [map_neg, hc, neg_neg]; exact ⟨fun _ h' => hne h'.symm, fun _ => rfl⟩

theorem card_cmType (H : Host E) :
    Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  have h2 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card =
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card := by
    have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    refine Finset.card_bij' (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ComplexEmbedding.conjugate τ)
      ?_ ?_ (fun τ _ => hinv τ) (fun τ _ => hinv τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [conjugate_mem_iff]; exact fun h => h hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [conjugate_mem_iff]; exact hτ
  rw [Finset.card_univ, Embeddings.card] at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem exists_index (hty : IsTypeFn H D.p D.q ty) : ∃ e : Fin D.dim → Fin g × Fin g,
    ∀ i j, ty i (H.rt : E) = H.rt0 → ty j = ComplexEmbedding.conjugate (ty i) → ∃ k, e k = (i, j) := by
  classical
  let I := Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
    {i // ty i = τ.1} × {j // ty j = ComplexEmbedding.conjugate τ.1}
  have hI : Nat.card I = D.dim := by
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => D.p * D.q), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_cmType, Datum.dim, smul_eq_mul, mul_assoc]
    intro τ _
    rw [Nat.card_prod, (hty _).1 τ.2, (hty _).2 fun h => (conjugate_mem_iff H _).1 h τ.2]
  let e : I ≃ Fin D.dim := Finite.equivFinOfCardEq hI
  refine ⟨fun k => ((e.symm k).2.1.1, (e.symm k).2.2.1), fun i j hi hj =>
    ⟨e ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, hj⟩⟩, ?_⟩⟩
  simp only []
  rw [e.symm_apply_apply]

theorem exists_period_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P₀ → ∃ (Z : (D.La →+ (Fin g → ℂ)) → (Fin D.dim → ℂ)) (s : Finset D.La) (ε : ℝ), 0 < ε ∧ (∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods D ty B P → (∀ b ∈ B, ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P b)) B) ∧ ∀ P P' : D.La →+ (Fin g → ℂ), IsPeriod D ty P → IsPeriod D ty P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) → Z P = Z P' → ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, P' a = h (P a)) ∧ ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := by
  intro E _ _ _ H D g ty P₀ hty hP₀
  obtain ⟨α, β, hαβ⟩ := exists_colMat hP₀
  obtain ⟨e, he⟩ := exists_index hty
  obtain ⟨M₀, -, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hA₀ : colMat α P₀ = 1 := by
    refine (realMap_inj (B := colMat β P₀) (B' := 0) (ext_period hP₀ fun x => ?_)).1
    rw [← hαβ P₀ hP₀]
    simp [realMap_apply]
  have hcont : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := by
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [colMat, of_apply]
    fun_prop
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hcont.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀]))
  refine ⟨fun P k => (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀) (e k).1 (e k).2, s, ε, hε, ?_, ?_⟩
  · intro m B P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb))))
    refine differentiableOn_pi.2 fun k => ?_
    simp only [mul_apply, transpose_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (DifferentiableOn.fun_sum fun n _ => (hinv _ _).mul (hc β _ _)).mul_const _
  · intro P P' hP hP' hn hn' hZ
    have hA : (colMat α P).det ≠ 0 := hs _ hn
    have hA' : (colMat α P').det ≠ 0 := hs _ hn'
    have h1 := hαβ P hP
    have h1' := hαβ P' hP'
    have h2 := symm_and_support hP₀ hP hM₀ h1 hA
    have h2' := symm_and_support hP₀ hP' hM₀ h1' hA'
    beta_reduce at hZ
    clear hs hαβ
    generalize colMat α P = A, colMat β P = B, colMat α P' = A', colMat β P' = B' at *
    have hu := isUnit_iff_ne_zero.2 hA
    have hu' := isUnit_iff_ne_zero.2 hA'
    have h3 : ∀ i j, ty i (H.rt : E) = H.rt0 → ((A⁻¹ * B)ᵀ * M₀) i j = ((A'⁻¹ * B')ᵀ * M₀) i j := by
      intro i j hi
      by_cases hj : ty j = ComplexEmbedding.conjugate (ty i)
      · obtain ⟨k, hk⟩ := he i j hi hj
        simpa only [hk] using congrFun hZ k
      · rw [(h2 i j).2 hj, (h2' i j).2 hj]
    have h4 : (A⁻¹ * B)ᵀ * M₀ = (A'⁻¹ * B')ᵀ * M₀ := by
      ext i j
      by_cases hi : ty i (H.rt : E) = H.rt0
      · exact h3 i j hi
      by_cases hj : ty j = ComplexEmbedding.conjugate (ty i)
      · rw [(h2 i j).1, (h2' i j).1]
        exact h3 j i (by rw [hj, conjugate_mem_iff]; exact hi)
      · rw [(h2 i j).2 hj, (h2' i j).2 hj]
    have h5 : A⁻¹ * B = A'⁻¹ * B' := by
      have hM := isUnit_iff_ne_zero.2 (det_ne_zero_of_pos hpos₀)
      have := congrArg (· * M₀⁻¹) h4
      simp only [mul_nonsing_inv_cancel_right _ _ hM] at this
      exact transpose_injective this
    have hN : IsUnit (A' * A⁻¹).det := by
      rw [det_mul]; exact hu'.mul (isUnit_nonsing_inv_det _ hu)
    have h6 : ∀ x, P' x = (A' * A⁻¹) *ᵥ P x := fun x => by
      rw [h1, h1', realMap_apply, realMap_apply, mulVec_add, mulVec_mulVec, mulVec_mulVec,
        nonsing_inv_mul_cancel_right _ _ hu, Matrix.mul_assoc, h5, mul_nonsing_inv_cancel_left _ _ hu']
    refine ⟨Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hN), h6, fun a z => ?_⟩
    have h7 := (comm_of_realMap hP hP' (A := A' * A⁻¹) (B := 0) (fun x => by simp [realMap_apply, h6]) a).1
    have h8 : ∀ z : Fin g → ℂ, (fun k => ty k (a : E) * z k) = actMat ty a *ᵥ z := fun z => by
      funext k; rw [actMat, mulVec_diagonal]
    rw [h8, h8]
    change (A' * A⁻¹) *ᵥ _ = _ *ᵥ ((A' * A⁻¹) *ᵥ z)
    rw [mulVec_mulVec, mulVec_mulVec, h7]

end

end GlobalTheory.PeriodCoord
