import Mathlib
import ReciprocityTheory.ReducedBases.LatDefs
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

noncomputable section

namespace GlobalTheory.ClassMin

open QuadraticMap Matrix Filter
open scoped TensorProduct

section Unique

variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}

theorem eq_polar_div_two (Q : QuadraticMap ℤ X ℝ) (x : X) : Q x = polar Q x x / 2 := by
  rw [polar_self, two_smul]; ring

theorem map_add_zsmul (Q : QuadraticMap ℤ X ℝ) (a m : X) (n : ℤ) :
    Q (a + n • m) = Q a + n * polar Q a m + n ^ 2 * Q m := by
  rw [QuadraticMap.map_add Q, polar_smul_right, QuadraticMap.map_smul]
  simp only [zsmul_eq_mul]
  push_cast
  ring

theorem eq_zero_of_zsmul_eq_zero (hQ : Q.PosDef) {n : ℤ} (hn : n ≠ 0) {x : X} (h : n • x = 0) :
    x = 0 := by
  have h1 : Q (n • x) = 0 := by rw [h, map_zero]
  rw [QuadraticMap.map_smul, zsmul_eq_mul] at h1
  have h2 : ((n * n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero hn hn
  exact hQ.anisotropic x ((mul_eq_zero.mp h1).resolve_left h2)

theorem lt_add_zsmul_of_le_add (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {a m : X} {n : ℤ}
    (hn : 2 ≤ n) (h : t * Q a + ν a ≤ t * Q (a + m) + ν (a + m)) (hm : m ≠ 0) :
    t * Q a + ν a < t * Q (a + n • m) + ν (a + n • m) := by
  have h1 := map_add_zsmul Q a m 1
  rw [one_smul] at h1
  rw [h1, map_add] at h
  rw [map_add_zsmul, map_add, map_zsmul, zsmul_eq_mul]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < t * Q m := mul_pos ht (hQ m hm)
  have h2 : 0 ≤ t * polar Q a m + t * Q m + ν m := by push_cast at h; linarith
  have h3 : 0 ≤ (n : ℝ) * (t * polar Q a m + t * Q m + ν m) := mul_nonneg (by linarith) h2
  have h4 : 0 < (n : ℝ) * (n - 1) * (t * Q m) := mul_pos (mul_pos (by linarith) (by linarith)) hp
  nlinarith

theorem affine_lt_of_min_class (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {N n : ℤ}
    (hn : 2 ≤ n) {a : X} (ha : ∀ w, t * Q a + ν a ≤ t * Q (a + N • w) + ν (a + N • w)) {w : X}
    (hw : (n * N) • w ≠ 0) :
    t * Q a + ν a < t * Q (a + (n * N) • w) + ν (a + (n * N) • w) := by
  rw [mul_smul] at hw ⊢
  exact lt_add_zsmul_of_le_add hQ ht ν hn (ha w) fun h => hw (by rw [h, smul_zero])

theorem lt_of_min_class (hQ : Q.PosDef) {N n : ℤ} (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : (n * N) • w ≠ 0) :
    Q a < Q (a + (n * N) • w) := by
  simpa using affine_lt_of_min_class hQ one_pos 0 hn (by simpa using ha) hw

theorem lt_of_min_class_of_ne_zero (hQ : Q.PosDef) {N n : ℤ} (hN : N ≠ 0) (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : w ≠ 0) : Q a < Q (a + (n * N) • w) :=
  lt_of_min_class hQ hn ha fun h =>
    hw (eq_zero_of_zsmul_eq_zero hQ (mul_ne_zero (by omega) hN) h)

theorem affine_lt_of_global_min (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {N : ℤ}
    (hN : 2 ≤ N) {a : X} (ha : ∀ x, t * Q a + ν a ≤ t * Q x + ν x) {w : X} (hw : w ≠ 0) :
    t * Q a + ν a < t * Q (a + N • w) + ν (a + N • w) :=
  lt_add_zsmul_of_le_add hQ ht ν hN (ha _) hw

theorem lt_of_global_min (hQ : Q.PosDef) (ν : X →+ ℝ) {N : ℤ} (hN : 2 ≤ N) {a : X}
    (ha : ∀ x, Q a / N + ν a ≤ Q x / N + ν x) {w : X} (hw : w ≠ 0) :
    Q a / N + ν a < Q (a + N • w) / N + ν (a + N • w) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : (0 : ℤ) < N)
  simp only [div_eq_inv_mul] at ha ⊢
  exact affine_lt_of_global_min hQ (inv_pos.mpr hN') ν hN ha hw

theorem mul_map_add_le (hQ : ∀ x, 0 ≤ Q x) (j : ℤ) (a b : X) :
    j * Q (a + b) ≤ (j + 1) * Q a + j * (j + 1) * Q b := by
  have h1 := map_add_zsmul Q a b 1
  have h2 := hQ (a + (-j) • b)
  rw [one_smul] at h1
  rw [map_add_zsmul] at h2
  rw [h1]
  push_cast at h2 ⊢
  nlinarith

theorem map_add_le (hQ : ∀ x, 0 ≤ Q x) {j : ℤ} (hj : 1 ≤ j) (a b : X) :
    Q (a + b) ≤ (1 + 1 / j) * Q a + (1 + j) * Q b := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast (by omega : (0 : ℤ) < j)
  refine le_of_mul_le_mul_left ((mul_map_add_le hQ j a b).trans_eq ?_) hj'
  field_simp
  ring

theorem map_sum_le (hQ : ∀ x, 0 ≤ Q x) {ι : Type*} (s : Finset ι) (v : ι → X) :
    Q (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, Q (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, add_comm (v i)]
    have h1 := mul_map_add_le hQ s.card (∑ i ∈ s, v i) (v i)
    push_cast at h1 ⊢
    refine le_of_mul_le_mul_left (h1.trans ?_) hc
    nlinarith [mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ s.card + 1 by positivity)]

end Unique

section Gram

variable {X : Type*} [AddCommGroup X] {ι : Type*}

def gram {R : Type*} [CommRing R] [Module R X] [Module R ℝ] (Q : QuadraticMap R X ℝ) (e : ι → X) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j => polar Q (e i) (e j)

@[simp] theorem gram_apply {R : Type*} [CommRing R] [Module R X] [Module R ℝ]
    (Q : QuadraticMap R X ℝ) (e : ι → X) (i j : ι) : gram Q e i j = polar Q (e i) (e j) := rfl

theorem gram_isHermitian {R : Type*} [CommRing R] [Module R X] [Module R ℝ]
    (Q : QuadraticMap R X ℝ) (e : ι → X) : (gram Q e).IsHermitian := by
  ext i j
  simp [polar_comm Q (e j)]

theorem polar_sum_smul {R : Type*} [CommRing R] [Module R X] [Algebra R ℝ] [Fintype ι]
    (Q : QuadraticMap R X ℝ) (e : ι → X) (x y : ι → R) :
    polar Q (∑ i, x i • e i) (∑ i, y i • e i) =
      (fun i => algebraMap R ℝ (x i)) ⬝ᵥ (gram Q e *ᵥ fun i => algebraMap R ℝ (y i)) := by
  rw [← polarBilin_apply_apply, LinearMap.map_sum₂]
  simp only [map_sum, map_smul, LinearMap.smul_apply, polarBilin_apply_apply, dotProduct, mulVec,
    gram_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def realExtension (Q : QuadraticMap ℤ X ℝ) : QuadraticForm ℝ (ℝ ⊗[ℤ] X) :=
  (1 / 2 : ℝ) • LinearMap.BilinMap.toQuadraticMap (LinearMap.liftBaseChangeEquiv ℝ
    ((LinearMap.liftBaseChangeEquiv ℝ (R := ℤ) (M := X) (N := ℝ)).toLinearMap.restrictScalars ℤ ∘ₗ
      Q.polarBilin))

@[simp] theorem realExtension_one_tmul (Q : QuadraticMap ℤ X ℝ) (x : X) :
    realExtension Q (1 ⊗ₜ x) = Q x := by
  rw [eq_polar_div_two Q]
  simp [realExtension]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem gram_eq_of_comp {Q : QuadraticMap ℤ X ℝ} {P : QuadraticForm ℝ V} (φ : X →+ V)
    (h : ∀ x, P (φ x) = Q x) (e : ι → X) : gram Q e = gram P (fun i => φ (e i)) := by
  ext i j
  simp only [gram_apply, polar, ← map_add φ, h]

theorem dotProduct_gram_mulVec [Fintype ι] (P : QuadraticForm ℝ V) (v : ι → V) (x : ι → ℝ) :
    x ⬝ᵥ (gram P v *ᵥ x) = 2 * P (∑ i, x i • v i) := by
  have := polar_sum_smul P v x x
  rw [polar_self, two_smul] at this
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [← this, two_mul]

theorem gram_posDef_of_linearIndependent [Finite ι] {P : QuadraticForm ℝ V} (hP : P.PosDef)
    {v : ι → V} (hv : LinearIndependent ℝ v) : (gram P v).PosDef := by
  have := Fintype.ofFinite ι
  refine posDef_iff_dotProduct_mulVec.mpr ⟨gram_isHermitian P v, fun x hx => ?_⟩
  rw [star_trivial, dotProduct_gram_mulVec]
  refine mul_pos two_pos (hP _ fun h => hx ?_)
  exact funext (Fintype.linearIndependent_iff.mp hv x h)

theorem gram_posDef_iff [Finite ι] (P : QuadraticForm ℝ V) (v : Module.Basis ι ℝ V) :
    (gram P v).PosDef ↔ P.PosDef := by
  have := Fintype.ofFinite ι
  refine ⟨fun h y hy => ?_, fun h => gram_posDef_of_linearIndependent h v.linearIndependent⟩
  have h1 := h.dotProduct_mulVec_pos (x := v.equivFun y) (by simpa using hy)
  rw [star_trivial, dotProduct_gram_mulVec, v.sum_equivFun] at h1
  linarith

theorem realExtension_posDef_iff [Finite ι] (Q : QuadraticMap ℤ X ℝ) (e : Module.Basis ι ℤ X) :
    (realExtension Q).PosDef ↔ (gram Q e).PosDef := by
  rw [← gram_posDef_iff _ (Algebra.TensorProduct.basis ℝ e),
    gram_eq_of_comp (TensorProduct.mk ℤ ℝ X 1).toAddMonoidHom (realExtension_one_tmul Q) e]
  have : ⇑(Algebra.TensorProduct.basis ℝ e) = fun i => (1 : ℝ) ⊗ₜ[ℤ] e i :=
    funext fun i => Algebra.TensorProduct.basis_apply e i
  rw [this]
  rfl

theorem two_mul_eq_dotProduct [Fintype ι] (Q : QuadraticMap ℤ X ℝ) (e : Module.Basis ι ℤ X) (a : X) :
    2 * Q a = (fun i => (e.repr a i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (e.repr a i : ℝ)) := by
  have := polar_sum_smul Q e (e.repr a) (e.repr a)
  rw [e.sum_repr, polar_self, two_smul] at this
  rw [two_mul, this]
  simp

end Gram

section Rational

variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}

theorem dotProduct_gram_pos_of_rat [Fintype ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) {x : ι → ℚ}
    (hx : x ≠ 0) : 0 < (fun i => (x i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (x i : ℝ)) := by
  obtain ⟨⟨D, hD⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  choose y hy using h
  have hD0 : D ≠ 0 := nonZeroDivisors.ne_zero hD
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
  have hy' : ∀ i, (y i : ℚ) = D * x i := fun i => by simpa using hy i
  have hyx : (fun i => (e.repr (e.equivFun.symm y) i : ℝ)) = (D : ℝ) • fun i => (x i : ℝ) := by
    funext i
    have h1 : e.repr (e.equivFun.symm y) i = y i := congrFun (e.equivFun.apply_symm_apply y) i
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hy' i
  have hy0 : e.equivFun.symm y ≠ 0 := by
    intro h0
    have h1 : y = 0 := by simpa using (LinearEquiv.map_eq_zero_iff _).mp h0
    refine hx (funext fun i => ?_)
    have := hy' i
    rw [h1] at this
    simpa [hD0] using this.symm
  have h2 := two_mul_eq_dotProduct Q e (e.equivFun.symm y)
  rw [hyx, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h2
  have h3 := hQ _ hy0
  exact (pos_iff_pos_of_mul_pos (h2 ▸ mul_pos two_pos h3)).mp (mul_self_pos.mpr hD')

theorem gram_posSemidef [Finite ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) :
    (gram Q e).PosSemidef := by
  have := Fintype.ofFinite ι
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨gram_isHermitian Q e, fun x => ?_⟩
  rw [star_trivial]
  have hd : DenseRange (Pi.map fun (_ : ι) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on x (isClosed_le continuous_const ?_) fun y => ?_
  · simp only [dotProduct, mulVec]
    fun_prop
  · rcases eq_or_ne y 0 with rfl | hy
    · have : (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ)) 0) = 0 := by funext i; simp
      rw [this, zero_dotProduct]
    · exact (dotProduct_gram_pos_of_rat hQ e hy).le

theorem realExtension_posDef_of_rat [Module.Free ℤ X] [Module.Finite ℤ X] (hQ : Q.PosDef)
    (hr : ∀ x y, ∃ q : ℚ, polar Q x y = q) : (realExtension Q).PosDef := by
  classical
  let e := Module.Free.chooseBasis ℤ X
  choose M hM using fun i j => hr (e i) (e j)
  have hG : gram Q e = (Matrix.of M).map (Rat.castHom ℝ) := by
    ext i j
    simp [hM]
  rw [realExtension_posDef_iff Q e, (gram_posSemidef hQ e).posDef_iff_det_ne_zero]
  intro h0
  rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_eq_zero] at h0
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := dotProduct_gram_pos_of_rat hQ e hv
  have h2 : (gram Q e *ᵥ fun i => (v i : ℝ)) = 0 := by
    funext i
    have := congrArg (Rat.castHom ℝ) (congrFun hMv i)
    rw [RingHom.map_mulVec] at this
    rw [hG]
    simpa [Function.comp_def] using this
  rw [h2, dotProduct_zero] at h1
  exact lt_irrefl _ h1

def ofIntBilin (β : LinearMap.BilinForm ℤ X) : QuadraticMap ℤ X ℝ :=
  (1 / 2 : ℝ) • (Int.castAddHom ℝ).toIntLinearMap.compQuadraticMap β.toQuadraticMap

@[simp] theorem ofIntBilin_apply (β : LinearMap.BilinForm ℤ X) (x : X) :
    ofIntBilin β x = (β x x : ℝ) / 2 := by
  simp [ofIntBilin]
  ring

theorem polar_ofIntBilin {β : LinearMap.BilinForm ℤ X} (hβ : ∀ x y, β x y = β y x) (x y : X) :
    polar (ofIntBilin β) x y = β x y := by
  simp only [polar, ofIntBilin_apply, map_add, LinearMap.add_apply, hβ y x]
  push_cast
  ring

theorem realExtension_ofIntBilin_posDef [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hβ : ∀ x y, β x y = β y x) (hpos : ∀ x, x ≠ 0 → 0 < β x x) :
    (realExtension (ofIntBilin β)).PosDef :=
  realExtension_posDef_of_rat
    (fun x hx => by
      rw [ofIntBilin_apply]
      exact div_pos (by exact_mod_cast hpos x hx) two_pos)
    fun x y => ⟨β x y, by rw [polar_ofIntBilin hβ]; simp⟩

end Rational

section Exists

variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem exists_mul_sum_sq_le {ι : Type*} [Fintype ι] (hQ : (realExtension Q).PosDef)
    (e : Module.Basis ι ℤ X) : ∃ c > 0, ∀ a, c * ∑ i, (e.repr a i : ℝ) ^ 2 ≤ Q a := by
  obtain ⟨c, hc, h⟩ := posDef_exists_mul_dotProduct_le ((realExtension_posDef_iff Q e).mp hQ)
  refine ⟨c / 2, by positivity, fun a => ?_⟩
  have := h fun i => (e.repr a i : ℝ)
  rw [← two_mul_eq_dotProduct] at this
  simp only [dotProduct, ← pow_two] at this
  linarith

theorem finite_affine_sublevel (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    (r : ℝ) : {x | t * Q x + ν x ≤ r}.Finite := by
  let e := Module.Free.chooseBasis ℤ X
  obtain ⟨c, hc, h⟩ := exists_mul_sum_sq_le hQ e
  have hs : 0 < t * c := mul_pos ht hc
  set s := t * c with hsdef
  obtain ⟨K, hK⟩ := exists_int_gt ((r + ∑ i, ν (e i) ^ 2 / (2 * s)) / (s / 2))
  rw [div_lt_iff₀ (by positivity)] at hK
  refine Set.Finite.of_injOn (f := e.equivFun) (t := Set.pi Set.univ fun _ => Set.Icc (-K) K) ?_
    e.equivFun.injective.injOn (Set.Finite.pi fun _ => Set.finite_Icc _ _)
  intro a ha i _
  have hν : ν a = ∑ i, (e.repr a i : ℝ) * ν (e i) := by
    conv_lhs => rw [← e.sum_repr a, map_sum]
    simp only [map_zsmul, zsmul_eq_mul]
  have h1 : s / 2 * ∑ i, (e.repr a i : ℝ) ^ 2 ≤
      s * ∑ i, (e.repr a i : ℝ) ^ 2 + ν a + ∑ i, ν (e i) ^ 2 / (2 * s) := by
    rw [hν, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have : s * (e.repr a j : ℝ) ^ 2 + (e.repr a j : ℝ) * ν (e j) + ν (e j) ^ 2 / (2 * s)
        - s / 2 * (e.repr a j : ℝ) ^ 2 = (s * e.repr a j + ν (e j)) ^ 2 / (2 * s) := by
      field_simp
      ring
    have h0 : 0 ≤ (s * e.repr a j + ν (e j)) ^ 2 / (2 * s) := by positivity
    linarith
  have h2 : s * ∑ i, (e.repr a i : ℝ) ^ 2 ≤ t * Q a := by
    rw [hsdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h a) ht.le
  have h3 : (e.repr a i : ℝ) ^ 2 ≤ ∑ i, (e.repr a i : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => (e.repr a i : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have ha' : t * Q a + ν a ≤ r := ha
  have h4 : (e.repr a i : ℝ) ^ 2 < K := by
    refine lt_of_mul_lt_mul_left (a := s / 2) ?_ (by positivity)
    nlinarith
  have h5 : (e.repr a i) ^ 2 < K := by exact_mod_cast h4
  rw [Module.Basis.equivFun_apply]
  constructor <;> nlinarith [Int.le_self_sq (e.repr a i), Int.le_self_sq (-e.repr a i)]

theorem finite_sublevel (hQ : (realExtension Q).PosDef) (r : ℝ) : {x | Q x ≤ r}.Finite := by
  simpa using finite_affine_sublevel hQ one_pos 0 r

theorem tendsto_affine_cofinite (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t)
    (ν : X →+ ℝ) : Tendsto (fun x => t * Q x + ν x) cofinite atTop :=
  tendsto_atTop.mpr fun r => (finite_affine_sublevel hQ ht ν r).subset fun x hx =>
    le_of_not_ge (show ¬ r ≤ t * Q x + ν x from hx)

theorem exists_affine_min_on (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    {S : Set X} (hS : S.Nonempty) : ∃ a ∈ S, ∀ x ∈ S, t * Q a + ν a ≤ t * Q x + ν x :=
  (tendsto_affine_cofinite hQ ht ν).exists_within_forall_le hS

theorem exists_global_min (hQ : (realExtension Q).PosDef) (ν : X →+ ℝ) {N : ℝ} (hN : 0 < N) :
    ∃ a, ∀ x, Q a / N + ν a ≤ Q x / N + ν x := by
  simpa [div_eq_inv_mul] using exists_affine_min_on hQ (inv_pos.mpr hN) ν Set.univ_nonempty

end Exists

section Matrix

open ReciprocityTheory.ReducedBases (toReal SameClass IsMinInClass IsUniqueMinInClass)

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}

def ofMatrix (A : Matrix (Fin d) (Fin d) ℝ) : QuadraticMap ℤ (Fin d → ℤ) ℝ :=
  (1 / 2 : ℝ) • LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℤ (ReciprocityTheory.ReducedBases.polar A)
    (fun x y z => by simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, add_mul, Finset.sum_add_distrib])
    (fun n x y => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, Finset.mul_sum, mul_assoc])
    (fun x y z => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, mul_add, Finset.sum_add_distrib])
    (fun n x y => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, Finset.mul_sum, mul_left_comm]))

@[simp] theorem ofMatrix_apply (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) :
    ofMatrix A x = ReciprocityTheory.ReducedBases.Q A x := by
  change (1 / 2 : ℝ) * ReciprocityTheory.ReducedBases.polar A x x = ReciprocityTheory.ReducedBases.polar A x x / 2
  ring

theorem polar_ofMatrix (hA : A.IsHermitian) (x y : Fin d → ℤ) :
    polar (ofMatrix A) x y = ReciprocityTheory.ReducedBases.polar A x y := by
  have hs : ReciprocityTheory.ReducedBases.polar A y x = ReciprocityTheory.ReducedBases.polar A x y := by
    have hT : Aᵀ = A := by simpa using hA.eq
    rw [ReciprocityTheory.ReducedBases.polar, ReciprocityTheory.ReducedBases.polar, dotProduct_mulVec, ← mulVec_transpose, hT,
      dotProduct_comm]
  have ha : toReal (x + y) = toReal x + toReal y := by funext i; simp [toReal]
  simp only [polar, ofMatrix_apply, ReciprocityTheory.ReducedBases.Q]
  simp only [ReciprocityTheory.ReducedBases.polar, ha, mulVec_add, dotProduct_add, add_dotProduct] at hs ⊢
  linarith

theorem gram_ofMatrix (hA : A.IsHermitian) : gram (ofMatrix A) (Pi.basisFun ℤ (Fin d)) = A := by
  ext i j
  rw [gram_apply, polar_ofMatrix hA]
  simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, Pi.single_apply]

theorem realExtension_ofMatrix_posDef (hA : A.PosDef) : (realExtension (ofMatrix A)).PosDef := by
  rwa [realExtension_posDef_iff _ (Pi.basisFun ℤ (Fin d)), gram_ofMatrix hA.isHermitian]

example : (realExtension (ofMatrix !![2, 1; 1, 2])).PosDef := by
  refine realExtension_ofMatrix_posDef (posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    rcases this with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]

end Matrix

end GlobalTheory.ClassMin

end
