import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def HodgeForm (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * hermForm Hm a b

def HodgeIP (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * (b ⬝ᵥ Hm.mulVec (star a))

def LieModel.GramAt (M : LieModel G ξ E) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) {r : ℕ}
    (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ v : Fin r → (epsAt z ⟶ G), (∀ i, M.ValAt z (b i) (v i)) ∧ ∀ p q, HodgeIP G L z (v p) (v q) (Γ p q)

def LieModel.FormGramAt (M : LieModel G ξ E) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) {r : ℕ}
    (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ v : Fin r → (epsAt z ⟶ G), (∀ i, M.ValAt z (b i) (v i)) ∧ ∀ p q, HodgeForm G L z (v p) (v q) (Γ p q)

def leadMinor {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) : ℝ :=
  if h : s ≤ r then (Γ.submatrix (Fin.castLE h) (Fin.castLE h)).det.re else 0

def LieModel.IsGrNorm (M : LieModel G ξ E) (L : LB G.left) (V : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (t : Ω) (ν : ℝ) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
    (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
      M.GramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)

def SecNorm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (A : HermLine J) (e₀ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ)
    (t : Ω) (ν : ℝ) : Prop :=
  e₀ ≠ 0 ∧ CoordsAt ξ y z w ∧
  ∀ c : (k : K) → J k, (∀ k, w ⟨k, c k⟩ ≠ 0) → ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
    ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k

section Form

variable {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {v w : epsAt z ⟶ G} {c : ℂ}

theorem hodgeInnerProduct_iff_hodgeForm : HodgeIP G L z v w c ↔ HodgeForm G L z w v c := by
  constructor
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩

theorem conj_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (a b : Fin g → ℂ) :
    (starRingEnd ℂ) (hermForm Hm a b) = hermForm Hm b a := by
  have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => h.apply j i
  simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, hH]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem HodgeForm.conj (h : HodgeForm G L z v w c) : HodgeForm G L z w v ((starRingEnd ℂ) c) := by
  obtain ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  refine ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, ?_⟩
  rw [map_mul, Complex.conj_ofReal, conj_hermForm h2.1]

theorem HodgeIP.conj (h : HodgeIP G L z v w c) : HodgeIP G L z w v ((starRingEnd ℂ) c) :=
  hodgeInnerProduct_iff_hodgeForm.2 (hodgeInnerProduct_iff_hodgeForm.1 h).conj

theorem hodgeInnerProduct_iff_hodgeForm_conj : HodgeIP G L z v w c ↔ HodgeForm G L z v w ((starRingEnd ℂ) c) :=
  ⟨fun h => (hodgeInnerProduct_iff_hodgeForm.1 h).conj, fun h => hodgeInnerProduct_iff_hodgeForm.2 (by simpa using h.conj)⟩

theorem HodgeIP.isLB (h : HodgeIP G L z v w c) : L.IsLB := h.1

theorem HodgeIP.isTanAt_left (h : HodgeIP G L z v w c) : IsTanAt G z v := h.2.1

theorem HodgeIP.isTanAt_right (h : HodgeIP G L z v w c) : IsTanAt G z w := h.2.2.1

theorem LieModel.gramAt_iff_formGramAt (M : LieModel G ξ E) {r : ℕ} {b : Fin r → E} {Γ : Matrix (Fin r) (Fin r) ℂ} :
    M.GramAt L z b Γ ↔ M.FormGramAt L z b Γ.transpose :=
  ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, fun p q => hodgeInnerProduct_iff_hodgeForm.1 (h q p)⟩,
    fun ⟨v, hv, h⟩ => ⟨v, hv, fun p q => hodgeInnerProduct_iff_hodgeForm.2 (h q p)⟩⟩

end Form

section Minor

variable {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ}

theorem leadMinor_size_zero (Γ : Matrix (Fin r) (Fin r) ℂ) : leadMinor Γ 0 = 1 := by simp [leadMinor]

theorem leadMinor_size_one (Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : leadMinor Γ 1 = (Γ 0 0).re := by
  simp [leadMinor]

theorem leadMinor_size_self (Γ : Matrix (Fin r) (Fin r) ℂ) : leadMinor Γ r = Γ.det.re := by
  simp [leadMinor]

theorem leadMinor_transpose (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) : leadMinor Γ.transpose s = leadMinor Γ s := by
  unfold leadMinor
  split_ifs with h
  · rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  · rfl

theorem leadMinor_pos_of_posDef (hΓ : Γ.PosDef) {s : ℕ} (h : s ≤ r) : 0 < leadMinor Γ s := by
  unfold leadMinor
  rw [dif_pos h]
  exact (Complex.pos_iff.1 (hΓ.submatrix (Fin.castLE_injective h)).det_pos).1

example (a d : ℝ) (ha : a ≠ 0) (b : ℂ) :
    leadMinor !![(a : ℂ), b; (starRingEnd ℂ) b, d] 2 / leadMinor !![(a : ℂ), b; (starRingEnd ℂ) b, d] 1 =
      d - Complex.normSq b / a := by
  rw [leadMinor_size_one]
  simp [leadMinor, Matrix.det_fin_two, Complex.normSq_apply]
  field_simp

example {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    hermForm Hm (Pi.single p 1) (Pi.single q 1) = Hm p q := by
  simp [hermForm, ← Pi.single_star]

end Minor

section Gr

variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}

theorem LieModel.IsGrNorm.pos (h : M.IsGrNorm L V b₀ i z t ν) : 0 < ν := by
  obtain ⟨_, _, Γ, -, -, -, -, hΓ, rfl⟩ := h
  exact Real.sqrt_pos.2 (div_pos (leadMinor_pos_of_posDef hΓ i.2) (leadMinor_pos_of_posDef hΓ i.2.le))

theorem LieModel.isGrNorm_iff_formGramAt : M.IsGrNorm L V b₀ i z t ν ↔
    ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
        M.FormGramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i) := by
  constructor
  · rintro ⟨h, b, Γ, h1, h2, h3, h4, h5, rfl⟩
    exact ⟨h, b, Γ.transpose, h1, h2, h3, M.gramAt_iff_formGramAt.1 h4, h5.transpose, by
      rw [leadMinor_transpose, leadMinor_transpose]⟩
  · rintro ⟨h, b, Γ, h1, h2, h3, h4, h5, rfl⟩
    exact ⟨h, b, Γ.transpose, h1, h2, h3, M.gramAt_iff_formGramAt.2 h4, h5.transpose, by
      rw [leadMinor_transpose, leadMinor_transpose]⟩

end Gr

section Sec

variable {z : Spec (CommRingCat.of ℂ) ⟶ X}

namespace CxVal

theorem mul {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem isUnit (x : X.presheaf.stalk (centre z)) (h : (Scheme.stalkClosedPointTo z).hom x ≠ 0) : IsUnit x :=
  (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ h)

theorem inv {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x := isUnit x hr
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem zpow {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  have hn : ∀ n : ℕ, ValAt ξ z (a ^ n) (r ^ n) := fun n => by
    induction n with
    | zero => simpa using one h.1
    | succ n ih => rw [pow_succ, pow_succ]; exact mul ih h
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using hn n
  · simpa using inv (hn n) (pow_ne_zero _ hr)

theorem aeval {σ : Type} {a : σ → Ω} {r : σ → ℂ} (hz : genPt ξ ⤳ centre z) (h : ∀ p, ValAt ξ z (a p) (r p))
    (s : MvPolynomial σ ℤ) : ValAt ξ z (MvPolynomial.aeval a s) (MvPolynomial.aeval r s) := by
  induction s using MvPolynomial.induction_on with
  | C n => exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩
  | add p q hp hq =>
    obtain ⟨_, x, hx, hx'⟩ := hp
    obtain ⟨_, y, hy, hy'⟩ := hq
    exact ⟨hz, x + y, by rw [map_add, map_add, hx, hy],
      (map_add (Scheme.stalkClosedPointTo z).hom x y).trans (by rw [map_add, ← hx', ← hy']; rfl)⟩
  | mul_X p i hp => simpa using mul hp (h i)

theorem unique {a : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z a s) : r = s := by
  obtain ⟨h, x, hx, rfl⟩ := h
  obtain ⟨_, y, hy, rfl⟩ := h'
  by_contra hne
  have hu : IsUnit (x - y) := isUnit _ fun h0 =>
    hne (sub_eq_zero.1 ((map_sub (Scheme.stalkClosedPointTo z).hom x y).symm.trans h0))
  have := hu.map (genMap ξ ⟨centre z, h⟩)
  rw [map_sub, hx, hy, sub_self] at this
  exact not_isUnit_zero this

end CxVal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}

theorem secNorm_iff_chart (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w t ν ↔ ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
      ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k := by
  refine ⟨fun h => h.2.2 c hc, ?_⟩
  rintro ⟨u, hu, hν⟩
  refine ⟨he, hw, fun c' hc' => ?_⟩
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (hc' k))).2 (c k)
  have hr0 : ∀ k, r k ≠ 0 := fun k h => hc k (by rw [hr', h, zero_mul])
  have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ A.a k) (∏ k ∈ s, r k ^ A.a k) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hu.1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (hr k) (hr0 k) _) ih
  have hy : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine ⟨u * ∏ k, r k ^ A.a k, ?_, ?_⟩
  · convert CxVal.mul hu (hp Finset.univ) using 1
    simp only [div_zpow, Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_inv]
    field_simp
  · rw [hν, norm_mul, norm_prod, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hr' k, norm_mul, mul_zpow, norm_zpow]

theorem SecNorm.exists_chart (h : SecNorm ξ y A e₀ z w t ν) : ∃ c : (k : K) → J k, ∀ k, w ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h.2.1.1
  exact ⟨c, fun k => (hc k).ne_zero⟩

theorem SecNorm.unique (h : SecNorm ξ y A e₀ z w t ν) (h' : SecNorm ξ y A e₀ z w t ν') : ν = ν' := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, hu, e⟩ := h.2.2 c hc
  obtain ⟨u', hu', e'⟩ := h'.2.2 c hc
  rw [CxVal.unique hu hu', ← e'] at e
  exact mul_right_cancel₀ (A.pos w fun k => ⟨c k, hc k⟩).ne' e

theorem SecNorm.nonneg (h : SecNorm ξ y A e₀ z w t ν) : 0 ≤ ν := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, -, e⟩ := h.2.2 c hc
  refine nonneg_of_mul_nonneg_left ?_ (A.pos w fun k => ⟨c k, hc k⟩)
  rw [e]
  positivity

theorem SecNorm.specializes (h : SecNorm ξ y A e₀ z w t ν) : genPt ξ ⤳ centre z := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, hu, -⟩ := h.2.2 c hc
  exact hu.1

theorem SecNorm.mul (h : SecNorm ξ y A e₀ z w t ν) {f : Ω} {s : ℂ} (hf : ValAt ξ z f s) :
    SecNorm ξ y A e₀ z w (f * t) (‖s‖ * ν) := by
  refine ⟨h.1, h.2.1, fun c hc => ?_⟩
  obtain ⟨u, hu, e⟩ := h.2.2 c hc
  refine ⟨s * u, ?_, ?_⟩
  · rw [mul_div_assoc]
    exact CxVal.mul hf hu
  · rw [_root_.mul_assoc, e, norm_mul, _root_.mul_assoc]

theorem secNorm_chartMonomial (hz : genPt ξ ⤳ centre z) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) ((∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k) / A.h w) := by
  have hy : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine (secNorm_iff_chart he hw c hc).2 ⟨1, ?_, ?_⟩
  · rw [div_self (mul_ne_zero hy he)]
    exact CxVal.one hz
  · rw [div_mul_cancel₀ _ (A.pos w fun k => ⟨c k, hc k⟩).ne']
    simp

theorem aeval_blockScale {R : Type} [CommRing R] {s : MRing J} {b : K → ℕ} (hs : IsMultiHomog s b) (κ : K → R)
    (x : (Σ k, J k) → R) :
    MvPolynomial.aeval (fun p => κ p.1 * x p) s = (∏ k, κ k ^ b k) * MvPolynomial.aeval x s := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_sigma (fun p : Σ k, J k => κ p.1 ^ m p)]
  simp only [Finset.prod_pow_eq_pow_sum, hs m hm]
  ring

theorem secNorm_form (hz : genPt ξ ⤳ centre z) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) {s : MRing J} {b : K → ℕ}
    (hs : IsMultiHomog s b) (hb : ∀ k, A.a k = b k) :
    SecNorm ξ y A e₀ z w (MvPolynomial.aeval y s * e₀) (‖MvPolynomial.aeval w s‖ / A.h w) := by
  choose c hc using hw.1
  have hy := fun k => (hw.2 k (c k) (hc k)).1
  choose r hr hr' using fun p : Σ k, J k => (hw.2 p.1 (c p.1) (hc p.1)).2 p.2
  refine (secNorm_iff_chart he hw c fun k => (hc k).ne_zero).2 ⟨MvPolynomial.aeval r s, ?_, ?_⟩
  · convert CxVal.aeval hz hr s using 1
    have e : y = fun p => y ⟨p.1, c p.1⟩ * (y ⟨p.1, p.2⟩ / y ⟨p.1, c p.1⟩) :=
      funext fun p => (mul_div_cancel₀ _ (hy p.1)).symm
    have e' := aeval_blockScale hs (fun k => y ⟨k, c k⟩) fun p => y ⟨p.1, p.2⟩ / y ⟨p.1, c p.1⟩
    rw [← e] at e'
    have h0 : (∏ k, y ⟨k, c k⟩ ^ b k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    simp only [hb, zpow_natCast]
    rw [e']
    field_simp
  · have e : w = fun p => w ⟨p.1, c p.1⟩ * r p := funext fun p => (hr' p).trans (mul_comm _ _)
    have e' := aeval_blockScale hs (fun k => w ⟨k, c k⟩) r
    rw [← e] at e'
    rw [div_mul_cancel₀ _ (A.pos w fun k => ⟨c k, (hc k).ne_zero⟩).ne', e']
    simp only [hb, zpow_natCast, norm_mul, norm_prod, norm_pow]
    ring

example (k : K) (hk : ∀ i, w ⟨k, i⟩ = 0) : ¬ SecNorm ξ y A e₀ z w t ν ∧ ¬ SecNorm ξ y A 0 z w t ν :=
  ⟨fun h => let ⟨c, hc⟩ := h.exists_chart; hc k (hk (c k)), fun h => h.1 rfl⟩

end Sec

end GlobalTheory.CompanionTheory.Ar
