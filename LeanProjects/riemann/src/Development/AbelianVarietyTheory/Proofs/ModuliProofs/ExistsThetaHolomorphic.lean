import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HolTheta

open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel

variable {g : ℕ}

theorem pull_eq_imInv (M τ : Matrix (Fin g) (Fin g) ℂ) (hM : ∀ j k, (M j k).im = 0)
    (hN : ∀ j k, ((M * τ.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    M = imInv τ := by
  have hRY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have := hN j k
    simp only [Matrix.mul_apply, Complex.im_sum, map_apply, Complex.mul_im, hM, Complex.conj_im, zero_mul, add_zero,
      mul_neg, Finset.sum_neg_distrib, neg_inj] at this
    rw [← this]
    simp [Matrix.mul_apply]
  rw [imInv, inv_eq_left_inv hRY]
  ext j k
  apply Complex.ext
  · simp
  · simp [hM]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.HolTheta.normal_form (G : Matrix (Fin g) (Fin g) ℂ) (e f : Fin g → Fin g → ℂ) (hG : G.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hee : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (e k)).im = 0) (hff : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (f j) (f k)).im = 0)
    (hef : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (f k)).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    {A τ : Matrix (Fin g) (Fin g) ℂ} (hA : A = Matrix.of fun i j => e j i)
    (hτ : τ = A⁻¹ * Matrix.of fun i j => f j i) :
    IsUnit A.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv τ) (A⁻¹ *ᵥ z) (A⁻¹ *ᵥ w) := by
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => f j i with hF
  have hAe : ∀ k, A *ᵥ Pi.single k 1 = e k := fun k => by
    rw [hA]; exact _root_.GlobalTheory.RiemannRel.of_cols_mulVec e k
  have hFf : ∀ k, F *ᵥ Pi.single k 1 = f k := fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec f k
  have h1 : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hAe]; exact hee j k
  have h2 : ∀ j k, ((Aᵀ * G * F.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k :=
    fun j k => by rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAe, hFf]; exact hef j k
  have h3 : ∀ j k, ((Fᵀ * G * F.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hFf, hFf]; exact hff j k
  have hdet : A.det ≠ 0 := _root_.GlobalTheory.RiemannRel.det_ne_zero G A F hpos h1 h2
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAτ : A * τ = F := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hunit, Matrix.one_mul]
  obtain ⟨hsymm, hpd⟩ := _root_.GlobalTheory.RiemannRel.symm_posDef G A τ hG hdet hpos h1
    (by rw [hAτ]; exact h2) (by rw [hAτ]; exact h3)
  refine ⟨hunit, hsymm, hpd, ?_⟩
  set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef
  have hMreal : (M.map Complex.re).map Complex.ofReal = M := by
    ext j k
    apply Complex.ext
    · simp
    · simp [h1 j k]
  have hinv : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have h := h2 j k
    rw [← hAτ, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Complex.im_sum] at h
    rw [Matrix.mul_apply]
    have hsum : ∀ l, ((M j l) * (starRingEnd ℂ) (τ l k)).im = -((M j l).re * (τ l k).im) := by
      intro l
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1 j l]
      ring
    simp only [Matrix.map_apply] at h ⊢
    rw [Finset.sum_congr rfl (fun l _ => hsum l), Finset.sum_neg_distrib] at h
    linarith
  have hM : M = _root_.GlobalTheory.CanTh.imInv τ := by
    unfold _root_.GlobalTheory.CanTh.imInv
    rw [Matrix.inv_eq_left_inv hinv, hMreal]
  intro z w
  have hz : ∀ v : Fin g → ℂ, v = A *ᵥ (A⁻¹ *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  conv_lhs => rw [hz z, hz w]
  rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec, ← hMdef, hM]
  rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.HolTheta.canMult_add (a c : Fin g → ℝ) (m n m' n' : Fin g → ℤ) :
    _root_.GlobalTheory.CanTh.canMult a c (m + m') (n + n') = _root_.GlobalTheory.CanTh.canMult a c m n * _root_.GlobalTheory.CanTh.canMult a c m' n' * (-1) ^ (n ⬝ᵥ m' - m ⬝ᵥ n') := by
  have hneg : ∀ k : ℤ, ((-1 : ℂ)) ^ k = Complex.exp (k * (Real.pi * Complex.I)) := by
    intro k; rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold _root_.GlobalTheory.CanTh.canMult
  rw [hneg, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m ⬝ᵥ n', ?_⟩
  have h1 : (fun i => ((m + m') i : ℝ)) = (fun i => (m i : ℝ)) + fun i => (m' i : ℝ) := by
    ext i; simp
  have h2 : (fun i => ((n + n') i : ℝ)) = (fun i => (n i : ℝ)) + fun i => (n' i : ℝ) := by
    ext i; simp
  simp only [h1, h2, dotProduct_add, add_dotProduct, dotProduct_comm n m']
  push_cast
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.HolTheta.eq_of_cocycle {La κ : Type*} [AddCommGroup La] (bs : Module.Basis κ ℤ La) (E : La → La → ℂ)
    {χ ψ : La → ℂ} (hE : ∀ x y, E x y ≠ 0) (hχ0 : ∀ x, χ x ≠ 0) (hψ0 : ∀ x, ψ x ≠ 0)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y * E x y) (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y * E x y)
    (hb : ∀ i, χ (bs i) = ψ (bs i)) (x : La) : χ x = ψ x := by
  have h0 : χ 0 = ψ 0 := by
    have h1 := hχ 0 0
    have h2 := hψ 0 0
    simp only [add_zero] at h1 h2
    have e1 : χ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hχ0 0)
      linear_combination -h1
    have e2 : ψ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hψ0 0)
      linear_combination -h2
    linear_combination ψ 0 * e1 - χ 0 * e2
  let S : AddSubgroup La :=
    { carrier := {x | χ x = ψ x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hχ, hψ, hx, hy]
      zero_mem' := h0
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h1 := hχ x (-x)
        have h2 := hψ x (-x)
        rw [add_neg_cancel] at h1 h2
        have hne : ψ x * E x (-x) ≠ 0 := mul_ne_zero (hψ0 x) (hE x (-x))
        apply mul_left_cancel₀ hne
        linear_combination -(E x (-x)) * χ (-x) * hx - h1 + h2 + h0 }
  have hspan : Submodule.span ℤ (Set.range bs) ≤ S.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [bs.span_eq] at hspan
  exact hspan Submodule.mem_top

theorem exists_canMult {La : Type*} [AddCommGroup La] (bs : Module.Basis (Fin g ⊕ Fin g) ℤ La)
    (EF : LinearMap.BilinForm ℤ La) (halt : EF.IsAlt) (hbs : IsSymplecticBasis (-EF) bs) {χ : La → ℂ}
    (h1 : ∀ x, χ x = 1 ∨ χ x = -1) (hχ : ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) :
    ∃ a c : Fin g → ℝ, ∀ x, χ x =
      canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  classical
  have key : ∀ x, ∃ t : ℝ, Complex.exp (2 * Real.pi * Complex.I * t) = χ x := fun x => by
    rcases h1 x with h | h
    · exact ⟨0, by simp [h]⟩
    · refine ⟨1 / 2, ?_⟩
      rw [h, ← Complex.exp_pi_mul_I]
      congr 1
      push_cast
      ring
  choose t ht using key
  refine ⟨fun i => t (bs (Sum.inl i)), fun i => -t (bs (Sum.inr i)),
    eq_of_cocycle bs (fun x y => (-1) ^ EF x y) (fun x y => zpow_ne_zero _ (by norm_num))
      (fun x => by rcases h1 x with h | h <;> simp [h]) (fun x => Complex.exp_ne_zero _) hχ (fun x y => ?_) ?_⟩
  · have h := hbs.apply_eq_sum halt.neg x y
    have e : EF x y = (fun i => bs.repr x (Sum.inr i)) ⬝ᵥ (fun i => bs.repr y (Sum.inl i)) -
        (fun i => bs.repr x (Sum.inl i)) ⬝ᵥ (fun i => bs.repr y (Sum.inr i)) := by
      simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h
      rw [h]
      simp [dotProduct]
    rw [e, ← canMult_add, map_add]
    rfl
  · rintro (i | i)
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]

theorem exp_mul_canTh {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ)
    (m n : Fin g → ℤ) {y : Fin g → ℂ} (hy : y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (s : ℂ) :
    Complex.exp (-(Real.pi / 2 / s ^ 2) * hermForm (imInv τ) y y) * canTh τ a c (s⁻¹ • y) =
      Complex.exp (Real.pi / 2 / s ^ 2 * (2 * Complex.I * (y ⬝ᵥ fun i => (n i : ℂ)))) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) (s⁻¹ • y) := by
  have h := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) y
  simp only [Complex.ofReal_intCast] at h
  rw [← hy] at h
  rw [canTh, ← _root_.mul_assoc, ← Complex.exp_add, mulVec_smul, smul_dotProduct, dotProduct_smul, h]
  congr 2
  simp only [smul_eq_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
private theorem finrank_eq_two_mul_of_discrete_spanning_embedding {La : Type} [AddCommGroup La] [Module.Free ℤ La]
    [Module.Finite ℤ La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.finrank ℤ La = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by simpa [L, LinearMap.coe_range] using hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 := (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq
  rw [h2, h1, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
private theorem exists_characteristics_eq_canMult_of_semicharacter {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ La)
    (hbs : _root_.GlobalTheory.IsSymplecticBasis EF bs) (halt : EF.IsAlt) (χ : La → ℂ)
    (hpm : ∀ x, χ x = 1 ∨ χ x = -1) (hχ : ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) :
    ∃ a c : Fin g → ℝ, ∀ x, χ x = _root_.GlobalTheory.CanTh.canMult a c
      (fun j => bs.repr x (Sum.inr j)) (fun j => bs.repr x (Sum.inl j)) := by
  classical
  let a : Fin g → ℝ := fun j => if χ (bs (Sum.inr j)) = 1 then 0 else 1 / 2
  let c : Fin g → ℝ := fun j => if χ (bs (Sum.inl j)) = 1 then 0 else 1 / 2
  refine ⟨a, c, fun x => ?_⟩
  have hhalf : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
  have hhalf' : Complex.exp (2 * Real.pi * Complex.I * (-((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [mul_neg, Complex.exp_neg, hhalf]; norm_num
  refine _root_.GlobalTheory.HolTheta.eq_of_cocycle (ψ := fun x => _root_.GlobalTheory.CanTh.canMult a c
      (fun j => bs.repr x (Sum.inr j)) (fun j => bs.repr x (Sum.inl j))) bs
    (fun x y => (-1 : ℂ) ^ EF x y)
    (fun x y => zpow_ne_zero _ (by norm_num))
    (fun x => by rcases hpm x with h | h <;> rw [h] <;> norm_num)
    (fun x => by unfold _root_.GlobalTheory.CanTh.canMult; exact Complex.exp_ne_zero _)
    hχ (fun x y => ?_) (fun i => ?_) x
  · have hm : (fun j => bs.repr (x + y) (Sum.inr j)) =
        (fun j => bs.repr x (Sum.inr j)) + fun j => bs.repr y (Sum.inr j) := by ext j; simp
    have hn : (fun j => bs.repr (x + y) (Sum.inl j)) =
        (fun j => bs.repr x (Sum.inl j)) + fun j => bs.repr y (Sum.inl j) := by ext j; simp
    rw [hm, hn, _root_.GlobalTheory.HolTheta.canMult_add, hbs.apply_eq_sum halt]
    congr 2
    simp only [dotProduct, Finset.sum_sub_distrib]
  · rcases i with j | j
    · have hm : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inr k)) = 0 := by
        ext k; simp [Finsupp.single_apply]
      have hn : (fun k => bs.repr (bs (Sum.inl j)) (Sum.inl k)) = Pi.single j 1 := by
        ext k; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
      rw [hm, hn]
      have key : _root_.GlobalTheory.CanTh.canMult a c 0 (Pi.single j 1) =
          Complex.exp (2 * Real.pi * Complex.I * (-((c j : ℝ) : ℂ))) := by
        unfold _root_.GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [key]
      rcases hpm (bs (Sum.inl j)) with h | h
      · simp [c, h]
      · simp only [c, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]
        exact hhalf'.symm
    · have hm : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inr k)) = Pi.single j 1 := by
        ext k; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
      have hn : (fun k => bs.repr (bs (Sum.inr j)) (Sum.inl k)) = 0 := by
        ext k; simp [Finsupp.single_apply]
      rw [hm, hn]
      have key : _root_.GlobalTheory.CanTh.canMult a c (Pi.single j 1) 0 =
          Complex.exp (2 * Real.pi * Complex.I * ((a j : ℝ) : ℂ)) := by
        unfold _root_.GlobalTheory.CanTh.canMult
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [key]
      rcases hpm (bs (Sum.inr j)) with h | h
      · simp [a, h]
      · simp only [a, h, if_neg (show (-1 : ℂ) ≠ 1 by norm_num)]
        exact hhalf.symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in
private theorem differentiable_matrix_mulVec (M : Matrix (Fin g) (Fin g) ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => M *ᵥ z) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).differentiable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
open Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.HolTheta.exists_theta_holomorphic : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (χ : La → ℂ) (g m N' : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < N' → Function.Bijective EF → (∀ x, χ x = 1 ∨ χ x = -1) → (∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) → IsOpen B → (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ DiscreteTopology (P b).range ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ (Hm b).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z z).re) ∧ ∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b y)).im = EF x y) → ∃ θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ, (∀ b ∈ B, θ b ≠ 0 ∧ Differentiable ℂ (θ b) ∧ ∀ x z, θ b (z + P b x) = χ x * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z (P b x) + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) * θ b z) ∧ ∀ x, DifferentiableOn ℂ (fun b => Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) * θ b ((N' : ℂ)⁻¹ • P b x)) B := by
  intro La _ _ _ EF χ g m N' B P Hm hN hbij hpm hχ hB hPd hlat
  classical
  by_cases hne : B.Nonempty
  swap
  · refine ⟨fun _ _ => 0, fun b hb => (hne ⟨b, hb⟩).elim, fun x => ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact differentiableOn_empty
  obtain ⟨b0, hb0⟩ := hne
  obtain ⟨hinj0, hdisc0, hspan0, hH0, -, hEF0⟩ := hlat b0 hb0
  have halt : EF.IsAlt := fun x => by
    have h := hEF0 x x
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b0) (P b0 x) (P b0 x)).im = 0 := by
      have hs := _root_.GlobalTheory.SiegelNormalForm.form_conj hH0 (P b0 x) (P b0 x)
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
      exact Complex.conj_eq_iff_im.mp hs
    rw [him] at h
    exact_mod_cast h.symm
  have hrank := finrank_eq_two_mul_of_discrete_spanning_embedding (P b0) hinj0 hdisc0 hspan0
  obtain ⟨bs, hbs⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt hbij hrank
  obtain ⟨a, c, hac⟩ := exists_characteristics_eq_canMult_of_semicharacter EF bs hbs halt χ hpm hχ
  set A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => P b (bs (Sum.inr j)) i with hAdef
  set F : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => P b (bs (Sum.inl j)) i with hFdef
  set τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (A b)⁻¹ * F b with hτdef
  have hnf : ∀ b ∈ B, IsUnit (A b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) z w =
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv (τ b)) ((A b)⁻¹ *ᵥ z) ((A b)⁻¹ *ᵥ w) := by
    intro b hb
    obtain ⟨-, -, -, hH, hpos, hEF⟩ := hlat b hb
    refine _root_.GlobalTheory.HolTheta.normal_form (Hm b) (fun j => P b (bs (Sum.inr j)))
      (fun j => P b (bs (Sum.inl j))) hH hpos ?_ ?_ ?_ rfl rfl
    · intro j k; rw [hEF, hbs.right_right]; simp
    · intro j k; rw [hEF, hbs.left_left]; simp
    · intro j k
      rw [hEF, hbs.right_left halt, Matrix.one_apply]
      split_ifs <;> simp
  have hsumP : ∀ b x, P b x = A b *ᵥ (fun i => (bs.repr x (Sum.inr i) : ℂ)) +
      F b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ)) := by
    intro b x
    conv_lhs => rw [← bs.sum_repr x]
    rw [map_sum, Fintype.sum_sum_type, add_comm]
    ext i
    simp [Matrix.mulVec, dotProduct, A, F, Finset.sum_apply, mul_comm]
  have hlat_pt : ∀ b ∈ B, ∀ x, (A b)⁻¹ *ᵥ P b x = (fun i => (bs.repr x (Sum.inr i) : ℂ)) +
      τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ)) := by
    intro b hb x
    have hu := (hnf b hb).1
    rw [hsumP, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  refine ⟨fun b z => _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ z), ?_, ?_⟩
  · intro b hb
    obtain ⟨hu, hs, hpd, hform⟩ := hnf b hb
    refine ⟨?_, (_root_.GlobalTheory.CanTh.differentiable_canTh hpd a c).comp
      (differentiable_matrix_mulVec _), fun x z => ?_⟩
    · intro h
      apply _root_.GlobalTheory.CanTh.canTh_ne_zero hs hpd a c
      funext ζ
      have := congrFun h (A b *ᵥ ζ)
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
    · show _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ (z + P b x)) = _
      rw [Matrix.mulVec_add, hlat_pt b hb x, _root_.GlobalTheory.CanTh.canTh_add_period hs hpd a c
        _ _ rfl, hac x, hform z, hform (P b x), hlat_pt b hb x]
  · intro x
    set a' : Fin g → ℝ := fun i => (bs.repr x (Sum.inl i) : ℝ) / N' with ha'
    set b' : Fin g → ℝ := fun i => (bs.repr x (Sum.inr i) : ℝ) / N' with hb'
    have hNc : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := fun i j =>
      differentiableOn_pi.1 (hPd (bs (Sum.inr j))) i
    have hFd : ∀ i j, DifferentiableOn ℂ (fun b => F b i j) B := fun i j =>
      differentiableOn_pi.1 (hPd (bs (Sum.inl j))) i
    have hinvd := _root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹) hAd
      (fun b hb => Matrix.nonsing_inv_mul _ (hnf b hb).1)
    have hτd : ∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B := by
      intro i j
      simp only [hτdef, Matrix.mul_apply]
      exact DifferentiableOn.fun_sum fun l _ => (hinvd i l).mul (hFd l j)
    have hdom : ∀ b ∈ B, τ b ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain (Fin g) := fun b hb =>
      _root_.GlobalTheory.CanTh.mem_thetaDomain (hnf b hb).2.2.1
    refine (DifferentiableOn.const_mul (_root_.GlobalTheory.CanTh.differentiableOn_thetaChar hτd
      (differentiableOn_const 0) hdom (a + a') (c + b'))
      (_root_.GlobalTheory.CanTh.translConst c a' b')).congr fun b hb => ?_
    obtain ⟨hu, hs, hpd, hform⟩ := hnf b hb
    set l := (fun i => (bs.repr x (Sum.inr i) : ℂ)) + τ b *ᵥ (fun i => (bs.repr x (Sum.inl i) : ℂ))
      with hldef
    have hl : (A b)⁻¹ *ᵥ P b x = l := hlat_pt b hb x
    have e1 : (fun i => ((a' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inl i) : ℂ) := by
      ext i; simp [ha', div_eq_inv_mul]
    have e2 : (fun i => ((b' i : ℝ) : ℂ)) = (N' : ℂ)⁻¹ • fun i => (bs.repr x (Sum.inr i) : ℂ) := by
      ext i; simp [hb', div_eq_inv_mul]
    have hy : (N' : ℂ)⁻¹ • l = (fun i => ((b' i : ℝ) : ℂ)) + τ b *ᵥ fun i => ((a' i : ℝ) : ℂ) := by
      rw [e1, e2, Matrix.mulVec_smul, hldef, smul_add]
    have ht := _root_.GlobalTheory.CanTh.canTh_translate hs hpd a c a' b' hy 0
    set M := _root_.GlobalTheory.CanTh.imInv (τ b)
    have hzero : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M 0 ((N' : ℂ)⁻¹ • l) = 0 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm; simp
    have hscal : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M ((N' : ℂ)⁻¹ • l) ((N' : ℂ)⁻¹ • l) = ((N' : ℂ)⁻¹) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm M l l := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
      simp [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
      ring
    have htheta0 : _root_.GlobalTheory.CanTh.canTh (τ b) (a + a') (c + b') 0 =
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (τ b) (fun i => ((a + a') i : ℂ)) (fun i => ((c + b') i : ℂ)) 0 := by
      unfold _root_.GlobalTheory.CanTh.canTh; simp
    rw [zero_add, hzero, hscal] at ht
    show Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm b) (P b x) (P b x)) *
      _root_.GlobalTheory.CanTh.canTh (τ b) a c ((A b)⁻¹ *ᵥ ((N' : ℂ)⁻¹ • P b x)) = _
    rw [Matrix.mulVec_smul, hl, hform, hl, ← htheta0, ← ht]
    congr 2
    field_simp
    ring

end GlobalTheory.HolTheta
