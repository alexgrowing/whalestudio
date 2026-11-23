import Mathlib

noncomputable section

open scoped Matrix

namespace GlobalTheory.IndLine.Iwasawa

section Exp

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped Matrix in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.IndLine.Iwasawa.exp_mul_eq {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    {B : Matrix m n ℂ} (h : A * B = B * D) :
    NormedSpace.exp A * B = B * NormedSpace.exp D := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hk : ∀ k : ℕ, A ^ k * B = B * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hD := NormedSpace.expSeries_summable' (𝕂 := ℂ) D
  let L : Matrix m m ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => X * B, map_add' := fun X Y => Matrix.add_mul X Y B,
      map_smul' := fun c X => Matrix.smul_mul c X B }
  let L' : Matrix n n ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => B * X, map_add' := fun X Y => Matrix.mul_add B X Y,
      map_smul' := fun c X => Matrix.mul_smul B c X }
  have e1 := L.map_tsum hA
  have e2 := L'.map_tsum hD
  simp only [L, L', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] at e1 e2
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  show (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k)) * B = B * ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • D ^ k)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext k
  rw [Matrix.smul_mul, Matrix.mul_smul, hk]

end Exp

section Ring

variable {R : Type} [Ring R]

def up (p r q Z : R) : R := p * Z * r + p * Z * q + r * Z * q

def low (p r q Z : R) : R := r * Z * p + q * Z * p + q * Z * r

def mid (p r q Z : R) : R := p * Z * p + r * Z * r + q * Z * q

structure Grading (p r q θ : R) : Prop where
  pp : p * p = p
  qq : q * q = q
  pq : p * q = 0
  qp : q * p = 0
  sum : r = 1 - p - q
  θθ : θ * θ = 1
  θp : θ * p = q * θ

example : Grading (R := Matrix (Fin 3) (Fin 3) ℤ) !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    !![0, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  constructor <;> decide

namespace Grading

variable {p r q θ : R} (h : Grading p r q θ)
include h

theorem pr : p * r = 0 := by rw [h.sum, mul_sub, mul_sub, mul_one, h.pp, h.pq, sub_self, sub_zero]
theorem rp : r * p = 0 := by rw [h.sum, sub_mul, sub_mul, one_mul, h.pp, h.qp, sub_self, sub_zero]
theorem qr : q * r = 0 := by rw [h.sum, mul_sub, mul_sub, mul_one, h.qq, h.qp, sub_zero, sub_self]
theorem rq : r * q = 0 := by rw [h.sum, sub_mul, sub_mul, one_mul, h.qq, h.pq, sub_zero, sub_self]
theorem rr : r * r = r := by
  conv_lhs => enter [1]; rw [h.sum]
  rw [sub_mul, sub_mul, one_mul, h.pr, h.qr, sub_zero, sub_zero]
theorem θq : θ * q = p * θ := by
  calc θ * q = θ * (q * θ) * θ := by rw [mul_assoc, mul_assoc, h.θθ, mul_one]
    _ = p * θ := by rw [← h.θp, ← mul_assoc, h.θθ, one_mul]
theorem θr : θ * r = r * θ := by
  rw [h.sum, mul_sub, mul_sub, sub_mul, sub_mul, h.θp, h.θq, mul_one, one_mul]; abel

theorem conj_low (Z : R) : θ * low p r q Z * θ = up p r q (θ * Z * θ) := by
  have a : ∀ u v u' v' : R, θ * u = u' * θ → θ * v' = v * θ → θ * (u * Z * v) * θ = u' * (θ * Z * θ) * v' := by
    intro u v u' v' h1 h2
    calc θ * (u * Z * v) * θ = (θ * u) * Z * (v * θ) := by simp only [mul_assoc]
      _ = _ := by rw [h1, ← h2]; simp only [mul_assoc]
  rw [low, up, mul_add, mul_add, add_mul, add_mul, a r p r q h.θr h.θq, a q p p q h.θq h.θq, a q r p r h.θq h.θr]
  abel

theorem dec (Z : R) : Z = up p r q (Z - θ * Z * θ) + mid p r q Z + (low p r q Z + θ * low p r q Z * θ) := by
  rw [h.conj_low]
  have e : p + r + q = 1 := by rw [h.sum]; abel
  calc Z = (p + r + q) * Z * (p + r + q) := by rw [e, one_mul, mul_one]
    _ = _ := by simp only [up, mid, low]; noncomm_ring

theorem comm_cpt (Z : R) : Commute (low p r q Z + θ * low p r q Z * θ) θ := by
  change _ * _ = _ * _
  rw [add_mul, mul_add, mul_assoc _ θ θ, h.θθ, mul_one, ← mul_assoc θ, ← mul_assoc θ, h.θθ, one_mul, add_comm]

theorem up_p (Z : R) : up p r q Z * p = 0 := by
  simp only [up, add_mul, mul_assoc, h.rp, h.qp, mul_zero, add_zero]

theorem up_r (Z : R) : up p r q Z * r = p * Z * r := by
  simp only [up, add_mul, mul_assoc, h.rr, h.qr, mul_zero, add_zero]

theorem mid_p (Z : R) : mid p r q Z * p = p * mid p r q Z := by
  simp only [mid, add_mul, mul_add, mul_assoc, h.pp, h.rp, h.qp, mul_zero, add_zero]
  simp only [← mul_assoc, h.pp, h.pr, h.pq, zero_mul, add_zero]

theorem mid_q (Z : R) : mid p r q Z * q = q * mid p r q Z := by
  simp only [mid, add_mul, mul_add, mul_assoc, h.qq, h.rq, h.pq, mul_zero, zero_add]
  simp only [← mul_assoc, h.qq, h.qr, h.qp, zero_mul, zero_add]

end Grading

end Ring

section Adj

variable {m : Type} [Fintype m] [DecidableEq m]

def Adj (N A B : Matrix m m ℂ) : Prop := Aᵀ * N = N * B.map star

theorem map_star_mul' {m n p : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

variable {N A B A' B' : Matrix m m ℂ}

theorem Adj.mul (h : Adj N A B) (h' : Adj N A' B') : Adj N (A * A') (B' * B) := by
  rw [Adj, Matrix.transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', map_star_mul',
    Matrix.mul_assoc]

theorem Adj.add (h : Adj N A B) (h' : Adj N A' B') : Adj N (A + A') (B + B') := by
  rw [Adj, Matrix.transpose_add, Matrix.add_mul, h, h', Matrix.map_add _ star_add, Matrix.mul_add]

theorem Adj.sub (h : Adj N A B) (h' : Adj N A' B') : Adj N (A - A') (B - B') := by
  rw [Adj, Matrix.transpose_sub, Matrix.sub_mul, h, h', Matrix.map_sub _ star_sub, Matrix.mul_sub]

theorem Adj.one : Adj N 1 1 := by
  rw [Adj, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]

variable {p r q θ Z : Matrix m m ℂ}

theorem adj_parts (h : Grading p r q θ) (hp : Adj N p q) (hq : Adj N q p) (hθ : Adj N θ θ) (hZ : Adj N Z (-Z)) :
    Adj N (up p r q (Z - θ * Z * θ)) (-up p r q (Z - θ * Z * θ)) ∧ Adj N (mid p r q Z) (-mid p r q Z) ∧
      Adj N (low p r q Z + θ * low p r q Z * θ) (-(low p r q Z + θ * low p r q Z * θ)) := by
  have hr : Adj N r r := by
    have := (Adj.one.sub hp).sub hq
    rwa [sub_sub 1 q p, add_comm q p, ← sub_sub, ← h.sum] at this
  have hl : Adj N (low p r q Z) (-low p r q Z) := by
    have := (((hr.mul hZ).mul hp).add ((hq.mul hZ).mul hp)).add ((hq.mul hZ).mul hr)
    convert this using 1 <;> (simp only [low]; try noncomm_ring)
  refine ⟨?_, ?_, ?_⟩
  · have hZ' := hZ.sub ((hθ.mul hZ).mul hθ)
    have := (((hp.mul hZ').mul hr).add ((hp.mul hZ').mul hq)).add ((hr.mul hZ').mul hq)
    convert this using 1 <;> (simp only [up]; try noncomm_ring)
  · have := (((hp.mul hZ).mul hp).add ((hr.mul hZ).mul hr)).add ((hq.mul hZ).mul hq)
    convert this using 1 <;> (simp only [mid]; try noncomm_ring)
  · have := hl.add ((hθ.mul hl).mul hθ)
    convert this using 1
    noncomm_ring

theorem exp_up (h : Grading p r q θ) (Z : Matrix m m ℂ) (t : ℝ) :
    NormedSpace.exp (t • up p r q Z) * p = p ∧ (1 - p) * NormedSpace.exp (t • up p r q Z) * r = r := by
  set A := t • up p r q Z with hA
  have a1 : A * p = 0 := by rw [hA, Matrix.smul_mul, h.up_p, smul_zero]
  have a2 : A * r = p * (t • Z) * r := by rw [hA, Matrix.smul_mul, h.up_r, Matrix.mul_smul, Matrix.smul_mul]
  have e1 : NormedSpace.exp A * p = p := by
    rw [exp_mul_eq (D := 0) (by rw [a1, Matrix.mul_zero]), NormedSpace.exp_zero, Matrix.mul_one]
  refine ⟨e1, ?_⟩
  have e2 : NormedSpace.exp A * (p + r) = (p + r) * NormedSpace.exp (A * r) := by
    refine exp_mul_eq ?_
    rw [Matrix.mul_add, a1, zero_add, a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_mul, h.pp, h.rp, add_zero]
  have e3 : r * NormedSpace.exp (A * r) = r := by
    rw [← exp_mul_eq (A := 0) (by rw [a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.rp]; simp), NormedSpace.exp_zero,
      Matrix.one_mul]
  have e4 : (1 - p) * (p + r) = r := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, h.pp, h.pr]; abel
  have e5 : (1 - p) * p = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h.pp, sub_self]
  calc (1 - p) * NormedSpace.exp A * r = (1 - p) * (NormedSpace.exp A * (p + r)) - (1 - p) * (NormedSpace.exp A * p) := by
        noncomm_ring
    _ = r := by rw [e1, e2, e5, sub_zero, ← Matrix.mul_assoc, e4, e3]

end Adj

section Plane

variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def prX (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := Matrix.vecMulVec x (J *ᵥ (c ∘ y))

def prY (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := -Matrix.vecMulVec y (J *ᵥ (c ∘ x))

structure Hyp (c : A →+* A) (J : Matrix m m A) (x y : m → A) (ι : Matrix m n A) (ι' : Matrix n m A) : Prop where
  cc : ∀ a, c (c a) = a
  skew : J.map c = -Jᵀ
  xx : x ⬝ᵥ J *ᵥ (c ∘ x) = 0
  yy : y ⬝ᵥ J *ᵥ (c ∘ y) = 0
  xy : x ⬝ᵥ J *ᵥ (c ∘ y) = 1
  yx : y ⬝ᵥ J *ᵥ (c ∘ x) = -1
  ιx : (J *ᵥ (c ∘ x)) ᵥ* ι = 0
  ιy : (J *ᵥ (c ∘ y)) ᵥ* ι = 0
  left : ι' * ι = 1
  right : ι * ι' = 1 - prX c J x y - prY c J x y

variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}

example : Hyp (RingHom.id ℤ) !![0, 1; -1, 0] ![1, 0] ![0, 1] (0 : Matrix (Fin 2) (Fin 0) ℤ) 0 := by
  constructor <;> first | decide | (intro a; rfl)

theorem map_mulVec' (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (J : Matrix m m A) (x : m → A) :
    f ∘ (J *ᵥ (c ∘ x)) = J.map f *ᵥ (c' ∘ (f ∘ x)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, hf]

theorem prX_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prX c J x y).map f = prX c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prX, Matrix.vecMulVec_apply, ← map_mulVec' f hf]

theorem prY_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prY c J x y).map f = prY c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prY, Matrix.vecMulVec_apply, ← map_mulVec' f hf]

theorem Hyp.map (h : Hyp c J x y ι ι') (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) :
    Hyp c' (J.map f) (f ∘ x) (f ∘ y) (ι.map f) (ι'.map f) := by
  have d : ∀ u v : m → A, (f ∘ u) ⬝ᵥ J.map f *ᵥ (c' ∘ (f ∘ v)) = f (u ⬝ᵥ J *ᵥ (c ∘ v)) := fun u v => by
    rw [← map_mulVec' f hf, RingHom.map_dotProduct]
  have e : ∀ v : m → A, (J *ᵥ (c ∘ v)) ᵥ* ι = 0 → (J.map f *ᵥ (c' ∘ (f ∘ v))) ᵥ* ι.map f = 0 := fun v hv => by
    funext j
    rw [← map_mulVec' f hf, ← RingHom.map_vecMul, hv, Pi.zero_apply, map_zero, Pi.zero_apply]
  refine ⟨hc, ?_, by rw [d, h.xx, map_zero], by rw [d, h.yy, map_zero], by rw [d, h.xy, map_one],
    by rw [d, h.yx, map_neg, map_one], e x h.ιx, e y h.ιy, ?_, ?_⟩
  · ext i j
    have := congrArg f (congrFun (congrFun h.skew i) j)
    simpa [hf] using this
  · rw [← Matrix.map_mul, h.left, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, h.right, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), prX_map f hf, prY_map f hf]

theorem prX_mulVec (v : m → A) : prX c J x y *ᵥ v = (v ⬝ᵥ J *ᵥ (c ∘ y)) • x := by
  rw [prX, Matrix.vecMulVec_mulVec, dotProduct_comm, op_smul_eq_smul]

theorem prY_mulVec (v : m → A) : prY c J x y *ᵥ v = -(v ⬝ᵥ J *ᵥ (c ∘ x)) • y := by
  rw [prY, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm, neg_smul, op_smul_eq_smul]

theorem c_mulVec (cc : ∀ a, c (c a) = a) (skew : J.map c = -Jᵀ) (v : m → A) : c ∘ (J *ᵥ (c ∘ v)) = -(v ᵥ* J) := by
  rw [map_mulVec' (c' := c) c (fun _ => rfl), skew, Matrix.neg_mulVec, Matrix.mulVec_transpose]
  congr 2
  funext i
  exact cc _

namespace Hyp

variable (h : Hyp c J x y ι ι')
include h

theorem px : prX c J x y *ᵥ x = x := by rw [prX_mulVec, h.xy, one_smul]
theorem py : prX c J x y *ᵥ y = 0 := by rw [prX_mulVec, h.yy, zero_smul]
theorem qx : prY c J x y *ᵥ x = 0 := by rw [prY_mulVec, h.xx, neg_zero, zero_smul]
theorem qy : prY c J x y *ᵥ y = y := by rw [prY_mulVec, h.yx, neg_neg, one_smul]
theorem pι : prX c J x y * ι = 0 := by rw [prX, Matrix.vecMulVec_mul, h.ιy]; ext; simp [Matrix.vecMulVec_apply]
theorem qι : prY c J x y * ι = 0 := by rw [prY, Matrix.neg_mul, Matrix.vecMulVec_mul, h.ιx, neg_eq_zero]; ext; simp [Matrix.vecMulVec_apply]

omit h in
theorem mul_p (g : Matrix m m A) : g * prX c J x y = Matrix.vecMulVec (g *ᵥ x) (J *ᵥ (c ∘ y)) := by
  rw [prX, Matrix.mul_vecMulVec]

omit h in
theorem mul_q (g : Matrix m m A) : g * prY c J x y = -Matrix.vecMulVec (g *ᵥ y) (J *ᵥ (c ∘ x)) := by
  rw [prY, Matrix.mul_neg, Matrix.mul_vecMulVec]

theorem pp : prX c J x y * prX c J x y = prX c J x y := by rw [mul_p, h.px]; rfl
theorem qq : prY c J x y * prY c J x y = prY c J x y := by rw [mul_q, h.qy]; rfl
theorem pq : prX c J x y * prY c J x y = 0 := by rw [mul_q, h.py, Matrix.zero_vecMulVec, neg_zero]
theorem qp : prY c J x y * prX c J x y = 0 := by rw [mul_p, h.qx, Matrix.zero_vecMulVec]

theorem ext' {g g' : Matrix m m A} (hx : g *ᵥ x = g' *ᵥ x) (hy : g *ᵥ y = g' *ᵥ y) (hι : g * ι = g' * ι) : g = g' := by
  have e : (1 : Matrix m m A) = ι * ι' + prX c J x y + prY c J x y := by rw [h.right]; abel
  rw [← Matrix.mul_one g, ← Matrix.mul_one g', e]
  simp only [Matrix.mul_add, mul_p, mul_q, ← Matrix.mul_assoc, hx, hy, hι]

theorem adj_pq : (prX c J x y)ᵀ * J = J * (prY c J x y).map c := by
  have e : (prY c J x y).map c = Matrix.vecMulVec (c ∘ y) (x ᵥ* J) := by
    ext i j
    have := congrFun (c_mulVec h.cc h.skew x) j
    simp only [Function.comp_apply, Pi.neg_apply] at this
    simp [prY, Matrix.vecMulVec_apply, this]
  rw [e, prX, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec]

theorem adj_qp : (prY c J x y)ᵀ * J = J * (prX c J x y).map c := by
  have e : (prX c J x y).map c = -Matrix.vecMulVec (c ∘ x) (y ᵥ* J) := by
    ext i j
    have := congrFun (c_mulVec h.cc h.skew y) j
    simp only [Function.comp_apply, Pi.neg_apply] at this
    simp [prX, Matrix.vecMulVec_apply, this]
  rw [e, prY, Matrix.transpose_neg, Matrix.transpose_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul, Matrix.mul_neg,
    Matrix.mul_vecMulVec]

theorem rι : (1 - prX c J x y - prY c J x y) * ι = ι := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, h.pι, h.qι, sub_zero, sub_zero]

theorem mulVec_eq_self_of_mul_prX_eq_prX {g : Matrix m m A} (hg : g * prX c J x y = prX c J x y) : g *ᵥ x = x := by
  rw [← h.px, Matrix.mulVec_mulVec, hg]

theorem unip_ι {g : Matrix m m A}
    (hg : (1 - prX c J x y) * g * (1 - prX c J x y - prY c J x y) = 1 - prX c J x y - prY c J x y) (z : n → A) :
    ∃ a : A, g *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have e : g * ι = ι + prX c J x y * (g * ι) := by
    have := congrArg (· * ι) hg
    simp only [Matrix.mul_assoc, h.rι] at this
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    exact sub_eq_iff_eq_add.1 this
  refine ⟨((g * ι) *ᵥ z) ⬝ᵥ J *ᵥ (c ∘ y), ?_⟩
  rw [← prX_mulVec (x := x), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]

theorem mulVec_eq_smul_of_commute_prX {g : Matrix m m A} (hg : g * prX c J x y = prX c J x y * g) :
    g *ᵥ x = ((g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ y)) • x := by
  rw [← prX_mulVec (x := x), Matrix.mulVec_mulVec, ← hg, ← Matrix.mulVec_mulVec, h.px]

theorem levi_y {g : Matrix m m A} (hq : g * prY c J x y = prY c J x y * g)
    (hu : gᵀ * J * g.map c = J) {t : Aˣ} (ht : (t : A) = (g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ y)) : g *ᵥ y = c (t⁻¹).1 • y := by
  have e : g *ᵥ y = -((g *ᵥ y) ⬝ᵥ J *ᵥ (c ∘ x)) • y := by
    rw [← prY_mulVec (y := y), Matrix.mulVec_mulVec, ← hq, ← Matrix.mulVec_mulVec, h.qy]
  set μ := -((g *ᵥ y) ⬝ᵥ J *ᵥ (c ∘ x))
  have e1 : (g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ (g *ᵥ y)) = 1 := by
    have : c ∘ (g *ᵥ y) = g.map c *ᵥ (c ∘ y) := by
      funext i; exact RingHom.map_mulVec c g y i
    rw [this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hu, h.xy]
  have e2 : c ∘ (μ • y) = c μ • (c ∘ y) := by
    funext i; simp
  rw [e, e2, Matrix.mulVec_smul, dotProduct_smul, ← ht, smul_eq_mul, mul_comm] at e1
  rw [Units.inv_eq_of_mul_eq_one_right e1, h.cc]
  exact e

theorem levi_ι {g : Matrix m m A} (hp : g * prX c J x y = prX c J x y * g) (hq : g * prY c J x y = prY c J x y * g) :
    g * ι = ι * (ι' * g * ι) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.right, Matrix.sub_mul _ _ g, Matrix.sub_mul _ _ g, ← hp, ← hq,
    Matrix.one_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc g, Matrix.mul_assoc g, h.pι, h.qι]
  simp

end Hyp

end Plane

end GlobalTheory.IndLine.Iwasawa

end
