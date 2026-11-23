import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective

set_option linter.unusedSectionVars false

noncomputable section

open Matrix
open Formalism.UG (cT cT_mul cT_one UJ bc)

namespace GlobalTheory.CompanionTheory.RedCov.Levi

section Ring

variable {R : Type} [CommRing R] {n m : ℕ}

structure Fr (s : R →+* R) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R)
    (P : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin n) R) (x y : Matrix (Fin n) (Fin 1) R) : Prop where
  ss : ∀ a, s (s a) = a
  herm : cT s J = J
  gram : cT s P * J * P = J'
  QP : Q * P = 1
  Qx : Q * x = 0
  Qy : Q * y = 0
  res : P * Q + x * (cT s y * J) + y * (cT s x * J) = 1
  xx : cT s x * J * x = 0
  yy : cT s y * J * y = 0
  xy : cT s x * J * y = 1
  xP : cT s x * J * P = 0
  yP : cT s y * J * P = 0

variable {s : R →+* R} {J : Matrix (Fin n) (Fin n) R} {J' : Matrix (Fin m) (Fin m) R}
  {P : Matrix (Fin n) (Fin m) R} {Q : Matrix (Fin m) (Fin n) R} {x y : Matrix (Fin n) (Fin 1) R}

theorem Fr.cc (h : Fr s J J' P Q x y) {a b : Type} (M : Matrix a b R) : cT s (cT s M) = M :=
  Matrix.ext fun _ _ => h.ss _

theorem cT_smul (s : R →+* R) {a b : Type} (c : R) (M : Matrix a b R) : cT s (c • M) = s c • cT s M :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_zero (s : R →+* R) {a b : Type} : cT s (0 : Matrix a b R) = 0 :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_sub (s : R →+* R) {a b : Type} (M N : Matrix a b R) : cT s (M - N) = cT s M - cT s N :=
  Matrix.ext fun _ _ => by simp [cT]

theorem Fr.adj (h : Fr s J J' P Q x y) {a b : ℕ} {U : Matrix (Fin n) (Fin a) R} {V : Matrix (Fin n) (Fin b) R}
    (e : cT s U * J * V = 0) : cT s V * J * U = 0 := by
  have := congrArg (cT s) e
  rwa [cT_mul, cT_mul, h.cc, h.herm, cT_zero, ← Matrix.mul_assoc] at this

theorem Fr.yx (h : Fr s J J' P Q x y) : cT s y * J * x = 1 := by
  have := congrArg (cT s) h.xy
  rwa [cT_mul, cT_mul, h.cc, h.herm, cT_one, ← Matrix.mul_assoc] at this

theorem Fr.Px (h : Fr s J J' P Q x y) : cT s P * J * x = 0 := h.adj h.xP
theorem Fr.Py (h : Fr s J J' P Q x y) : cT s P * J * y = 0 := h.adj h.yP

theorem Fr.ext_right (h : Fr s J J' P Q x y) {k : Type} {M N : Matrix k (Fin n) R} (e1 : M * P = N * P)
    (e2 : M * x = N * x) (e3 : M * y = N * y) : M = N := by
  have key : ∀ L : Matrix k (Fin n) R, L = L * P * Q + L * x * (cT s y * J) + L * y * (cT s x * J) := fun L => by
    conv_lhs => rw [← Matrix.mul_one L, ← h.res]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  rw [key M, key N, e1, e2, e3]

theorem Fr.gramQ (h : Fr s J J' P Q x y) : J' * Q = cT s P * J := by
  have e : cT s P * J * (P * Q + x * (cT s y * J) + y * (cT s x * J)) = cT s P * J := by rw [h.res, Matrix.mul_one]
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ x, ← Matrix.mul_assoc _ y, h.Px, h.Py, ← Matrix.mul_assoc _ P, h.gram] at e
  simpa using e

theorem Fr.herm' (h : Fr s J J' P Q x y) : cT s J' = J' := by
  rw [← h.gram, cT_mul, cT_mul, h.cc, h.herm, Matrix.mul_assoc]

theorem Fr.Qgram (h : Fr s J J' P Q x y) : cT s Q * J' = J * P := by
  have := congrArg (cT s) h.gramQ
  rwa [cT_mul, cT_mul, h.herm', h.cc, h.herm] at this

def iM (P : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin n) R) (g : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin n) (Fin n) R := 1 - P * Q + P * g * Q

theorem Fr.iM_P (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) : iM P Q g * P = P * g := by
  simp [iM, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, h.QP]

theorem Fr.levi_embedding_fixes_vector (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) : iM P Q g * x = x := by
  simp [iM, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, h.Qx]

theorem Fr.iM_y (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) : iM P Q g * y = y := by
  simp [iM, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, h.Qy]

theorem iM_one (P : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin n) R) : iM P Q 1 = 1 := by simp [iM]

theorem Fr.iM_mul (h : Fr s J J' P Q x y) (g g' : Matrix (Fin m) (Fin m) R) :
    iM P Q g * iM P Q g' = iM P Q (g * g') := by
  refine h.ext_right ?_ ?_ ?_
  · rw [Matrix.mul_assoc, h.iM_P, ← Matrix.mul_assoc, h.iM_P, h.iM_P, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, h.levi_embedding_fixes_vector, h.levi_embedding_fixes_vector, h.levi_embedding_fixes_vector]
  · rw [Matrix.mul_assoc, h.iM_y, h.iM_y, h.iM_y]

theorem Fr.xJ_iM (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) : cT s x * J * iM P Q g = cT s x * J := by
  simp only [iM, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, h.xP]
  simp

theorem Fr.yJ_iM (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) : cT s y * J * iM P Q g = cT s y * J := by
  simp only [iM, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, h.yP]
  simp

theorem Fr.PJ_iM (h : Fr s J J' P Q x y) (g : Matrix (Fin m) (Fin m) R) :
    cT s P * J * iM P Q g = J' * g * Q := by
  simp only [iM, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, h.gram, Matrix.mul_one]
  rw [h.gramQ]
  simp

theorem Fr.iM_unitary (h : Fr s J J' P Q x y) {g : Matrix (Fin m) (Fin m) R} (hg : cT s g * J' * g = J') :
    cT s (iM P Q g) * J * iM P Q g = J := by
  have hx : cT s (iM P Q g) * J * x = J * x := by
    have := congrArg (cT s) (h.xJ_iM g)
    rw [cT_mul, cT_mul, h.cc, h.herm] at this
    rw [Matrix.mul_assoc]; exact this
  have hy : cT s (iM P Q g) * J * y = J * y := by
    have := congrArg (cT s) (h.yJ_iM g)
    rw [cT_mul, cT_mul, h.cc, h.herm] at this
    rw [Matrix.mul_assoc]; exact this
  have hP : cT s (iM P Q g) * J * P = cT s Q * (cT s g * J') := by
    have := congrArg (cT s) (h.PJ_iM g)
    rw [cT_mul, cT_mul, h.cc, h.herm, cT_mul, cT_mul, h.herm'] at this
    rw [Matrix.mul_assoc]; exact this
  refine h.ext_right ?_ ?_ ?_
  · rw [Matrix.mul_assoc, h.iM_P, ← Matrix.mul_assoc, hP, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J' g, hg,
      h.Qgram]
  · rw [Matrix.mul_assoc, h.levi_embedding_fixes_vector, hx]
  · rw [Matrix.mul_assoc, h.iM_y, hy]

def Fr.iU (h : Fr s J J' P Q x y) : UJ s J' →* UJ s J where
  toFun g := ⟨⟨iM P Q g.1.1, iM P Q (g.1⁻¹).1, by rw [h.iM_mul, Units.mul_inv, iM_one], by
    rw [h.iM_mul, Units.inv_mul, iM_one]⟩, h.iM_unitary g.2⟩
  map_one' := Subtype.ext (Units.ext (iM_one P Q))
  map_mul' g g' := Subtype.ext (Units.ext (by
    change iM P Q (g.1.1 * g'.1.1) = iM P Q g.1.1 * iM P Q g'.1.1
    rw [h.iM_mul]))

section Line

variable {M M' : Matrix (Fin n) (Fin n) R} {β β' : R}

theorem Fr.xJ_M (h : Fr s J J' P Q x y) (h1 : M * M' = 1) (hU : cT s M * J * M = J) (hx' : M' * x = β' • x) :
    cT s x * J * M = s β' • (cT s x * J) := by
  have e : cT s M * J = J * M' := by
    have := congrArg (· * M') hU
    simpa [Matrix.mul_assoc, h1] using this
  have e2 : cT s M * J * x = β' • (J * x) := by rw [e, Matrix.mul_assoc, hx', Matrix.mul_smul]
  have := congrArg (cT s) e2
  rw [cT_mul, cT_mul, h.cc, h.herm, cT_smul, cT_mul, h.herm, ← Matrix.mul_assoc] at this
  exact this

theorem Fr.MP (h : Fr s J J' P Q x y) (h1 : M * M' = 1) (hU : cT s M * J * M = J) (hx' : M' * x = β' • x) :
    M * P = P * (Q * M * P) + x * (cT s y * J * (M * P)) := by
  have e0 : cT s x * J * (M * P) = 0 := by
    rw [← Matrix.mul_assoc, h.xJ_M h1 hU hx', Matrix.smul_mul, h.xP, smul_zero]
  have e := congrArg (· * (M * P)) h.res
  simp only [Matrix.add_mul, Matrix.one_mul] at e
  calc M * P = P * Q * (M * P) + x * (cT s y * J) * (M * P) + y * (cT s x * J) * (M * P) := e.symm
    _ = _ := by
      rw [Matrix.mul_assoc y, e0, Matrix.mul_zero, add_zero]
      simp only [Matrix.mul_assoc]

theorem Fr.gg (h : Fr s J J' P Q x y) (h1 : M * M' = 1) (h2 : M' * M = 1) (hU' : cT s M' * J * M' = J)
    (hx : M * x = β • x) : (Q * M * P) * (Q * M' * P) = 1 := by
  have e0 : cT s x * J * (M' * P) = 0 := by
    rw [← Matrix.mul_assoc, h.xJ_M h2 hU' hx, Matrix.smul_mul, h.xP, smul_zero]
  have e1 : Q * (M * x) = 0 := by rw [hx, Matrix.mul_smul, h.Qx, smul_zero]
  have e := congrArg (fun L => Q * M * L * (M' * P)) h.res
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] at e
  have e2 : Q * M * (x * (cT s y * J)) * (M' * P) = 0 := by
    rw [Matrix.mul_assoc Q M, ← Matrix.mul_assoc M, ← Matrix.mul_assoc Q, e1]; simp
  have e3 : Q * M * (y * (cT s x * J)) * (M' * P) = 0 := by
    rw [Matrix.mul_assoc _ _ (M' * P), Matrix.mul_assoc y, e0]; simp
  rw [e2, e3, add_zero, add_zero] at e
  calc (Q * M * P) * (Q * M' * P) = Q * M * (P * Q) * (M' * P) := by simp only [Matrix.mul_assoc]
    _ = Q * M * (M' * P) := e
    _ = 1 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, h1, Matrix.one_mul, h.QP]

theorem Fr.g_unitary (h : Fr s J J' P Q x y) (h1 : M * M' = 1) (hU : cT s M * J * M = J) (hx' : M' * x = β' • x) :
    cT s (Q * M * P) * J' * (Q * M * P) = J' := by
  set g := Q * M * P with hg
  set c := cT s y * J * (M * P) with hc
  have e1 : J' * g = cT s P * J * (M * P) := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.gramQ]; simp only [Matrix.mul_assoc]
  have e2 : P * g = M * P - x * c := by rw [h.MP h1 hU hx']; simp [hg, hc]
  have e0 : cT s x * J * (M * P) = 0 := by
    rw [← Matrix.mul_assoc, h.xJ_M h1 hU hx', Matrix.smul_mul, h.xP, smul_zero]
  calc cT s g * J' * g = cT s (P * g) * J * (M * P) := by
        rw [Matrix.mul_assoc, e1, cT_mul s P g]; simp only [Matrix.mul_assoc]
    _ = cT s (M * P) * J * (M * P) - cT s c * (cT s x * J * (M * P)) := by
        rw [e2, cT_sub, cT_mul, cT_mul, Matrix.sub_mul, Matrix.sub_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by
        rw [e0, Matrix.mul_zero, sub_zero, ← h.gram, cT_mul]
        conv_rhs => rw [← hU]
        simp only [Matrix.mul_assoc]

theorem Fr.nice_conj (h : Fr s J J' P Q x y) {N : Matrix (Fin n) (Fin n) R} {u : R} {c : Matrix (Fin 1) (Fin m) R}
    (hx : N * x = u • x) (hP : N * P = P + x * c) {g g' : Matrix (Fin m) (Fin m) R} (hg : g' * g = 1) :
    iM P Q g' * N * iM P Q g * x = u • x ∧ iM P Q g' * N * iM P Q g * P = P + x * (c * g) := by
  constructor
  · rw [Matrix.mul_assoc, h.levi_embedding_fixes_vector, Matrix.mul_assoc, hx, Matrix.mul_smul, h.levi_embedding_fixes_vector]
  · rw [Matrix.mul_assoc, h.iM_P, Matrix.mul_assoc, ← Matrix.mul_assoc N, hP, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_assoc _ P, h.iM_P, Matrix.mul_assoc P, hg, Matrix.mul_one, Matrix.mul_assoc x, ← Matrix.mul_assoc _ x, h.levi_embedding_fixes_vector]

end Line

theorem Fr.iM_tor (h : Fr s J J' P Q x y) {r : ℕ} {X' Y' : Matrix (Fin m) (Fin r) R} {Xp Yp : Matrix (Fin n) (Fin r) R}
    (hX : P * X' = Xp) (hY : P * Y' = Yp) (D D' : Matrix (Fin r) (Fin r) R) :
    iM P Q (1 + X' * D * (cT s Y' * J') + Y' * D' * (cT s X' * J')) =
      1 + Xp * D * (cT s Yp * J) + Yp * D' * (cT s Xp * J) := by
  have e1 : cT s Y' * J' * Q = cT s Yp * J := by
    rw [Matrix.mul_assoc, h.gramQ, ← hY, cT_mul]; simp only [Matrix.mul_assoc]
  have e2 : cT s X' * J' * Q = cT s Xp * J := by
    rw [Matrix.mul_assoc, h.gramQ, ← hX, cT_mul]; simp only [Matrix.mul_assoc]
  have e3 : P * (X' * D * (cT s Y' * J')) * Q = Xp * D * (cT s Yp * J) := by
    rw [← e1, ← hX]; simp only [Matrix.mul_assoc]
  have e4 : P * (Y' * D' * (cT s X' * J')) * Q = Yp * D' * (cT s Xp * J) := by
    rw [← e2, ← hY]; simp only [Matrix.mul_assoc]
  simp only [iM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [e3, e4]
  abel

theorem Fr.tor_comm (h : Fr s J J' P Q x y) (a b : Matrix (Fin 1) (Fin 1) R) (g : Matrix (Fin m) (Fin m) R) :
    (1 + x * a * (cT s y * J) + y * b * (cT s x * J)) * iM P Q g =
      iM P Q g * (1 + x * a * (cT s y * J) + y * b * (cT s x * J)) := by
  have e1 : x * a * (cT s y * J) * iM P Q g = x * a * (cT s y * J) := by rw [Matrix.mul_assoc, h.yJ_iM]
  have e2 : y * b * (cT s x * J) * iM P Q g = y * b * (cT s x * J) := by rw [Matrix.mul_assoc, h.xJ_iM]
  have e3 : iM P Q g * (x * a * (cT s y * J)) = x * a * (cT s y * J) := by
    rw [Matrix.mul_assoc x, ← Matrix.mul_assoc _ x, h.levi_embedding_fixes_vector]
  have e4 : iM P Q g * (y * b * (cT s x * J)) = y * b * (cT s x * J) := by
    rw [Matrix.mul_assoc y, ← Matrix.mul_assoc _ y, h.iM_y]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4, Matrix.one_mul, Matrix.mul_one]

theorem Fr.tor_P (h : Fr s J J' P Q x y) (a b : Matrix (Fin 1) (Fin 1) R) :
    (1 + x * a * (cT s y * J) + y * b * (cT s x * J)) * P = P := by
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc _ (cT s y * J), Matrix.mul_assoc _ (cT s x * J), h.xP, h.yP]
  simp

section Cols

variable {r : ℕ}

abbrev hd {k : Type} (X : Matrix k (Fin (r + 1)) R) : Matrix k (Fin 1) R := X.submatrix id fun _ => 0

abbrev tl {k : Type} (X : Matrix k (Fin (r + 1)) R) : Matrix k (Fin r) R := X.submatrix id Fin.succ

def blk (d : R) (c : Matrix (Fin 1) (Fin r) R) (B : Matrix (Fin r) (Fin r) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  fun i j => Fin.cases (Fin.cases d (fun j => c 0 j) j) (fun i => Fin.cases 0 (fun j => B i j) j) i

theorem blk_bt {d : R} {c : Matrix (Fin 1) (Fin r) R} {B : Matrix (Fin r) (Fin r) R} (hB : B.BlockTriangular id) :
    (blk d c B).BlockTriangular id := by
  intro i j hij
  induction i using Fin.cases with
  | zero => exact absurd hij (by simp)
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [blk]
    | succ j => simpa [blk] using hB (by simpa using hij)

theorem ext_cols {k : Type} {M N : Matrix k (Fin (r + 1)) R} (h1 : hd M = hd N) (h2 : tl M = tl N) : M = N := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact congrFun (congrFun h1 i) 0
  · exact congrFun (congrFun h2 i) j

theorem mul_blk {k : Type} (X : Matrix k (Fin (r + 1)) R) (d : R) (c : Matrix (Fin 1) (Fin r) R) (B : Matrix (Fin r) (Fin r) R) :
    hd (X * blk d c B) = d • hd X ∧ tl (X * blk d c B) = hd X * c + tl X * B := by
  constructor
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_succ, blk, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_succ, blk]

theorem mul_hd {k l : Type} [Fintype k] (N : Matrix l k R) (X : Matrix k (Fin (r + 1)) R) : hd (N * X) = N * hd X := by
  ext i j; simp [Matrix.mul_apply]

theorem mul_tl {k l : Type} [Fintype k] (N : Matrix l k R) (X : Matrix k (Fin (r + 1)) R) : tl (N * X) = N * tl X := by
  ext i j; simp [Matrix.mul_apply]

theorem mul_diag_mul {k l : Type} (X : Matrix k (Fin (r + 1)) R) (d : Fin (r + 1) → R) (Z : Matrix (Fin (r + 1)) l R) :
    X * diagonal d * Z = hd X * (diagonal fun _ : Fin 1 => d 0) * Z.submatrix (fun _ : Fin 1 => 0) id +
      tl X * diagonal (fun i : Fin r => d i.succ) * Z.submatrix Fin.succ id := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply, Finset.sum_ite_eq]

theorem cT_sub_row {a b : ℕ} (X : Matrix (Fin n) (Fin b) R) (f : Fin a → Fin b) :
    (cT s X * J).submatrix f id = cT s (X.submatrix id f) * J := by
  ext i j; simp [cT, Matrix.mul_apply]

end Cols

end Ring

section Fld

open GlobalTheory.SiegelSet Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {K : Type} [Field K] {n m : ℕ}

theorem exists_split (A : Matrix (Fin n) (Fin n) K) (hA : A * A = A) :
    ∃ (m : ℕ) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K), P * Q = A ∧ Q * P = 1 := by
  let f := Matrix.toLin' A
  let e := (Module.finBasis K (LinearMap.range f)).equivFun
  let p := (LinearMap.range f).subtype ∘ₗ e.symm.toLinearMap
  let q := e.toLinearMap ∘ₗ f.rangeRestrict
  have hf : ∀ w : LinearMap.range f, f w = w := by
    rintro ⟨_, v, rfl⟩
    change A *ᵥ (A *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, hA]
  refine ⟨_, LinearMap.toMatrix' p, LinearMap.toMatrix' q, ?_, ?_⟩
  · have : p ∘ₗ q = f := by
      apply LinearMap.ext
      intro v
      simp [p, q, f]
    rw [← LinearMap.toMatrix'_comp, this, LinearMap.toMatrix'_toLin']
  · have : q ∘ₗ p = LinearMap.id := by
      apply LinearMap.ext
      intro v
      have e1 : f.rangeRestrict (p v) = e.symm v := Subtype.ext (hf (e.symm v))
      simp only [q, LinearMap.comp_apply, e1]
      simp
    rw [← LinearMap.toMatrix'_comp, this, LinearMap.toMatrix'_id]

theorem exists_fr {s : K →+* K} (ss : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) K} (herm : cT s J = J)
    {x y : Matrix (Fin n) (Fin 1) K} (xx : cT s x * J * x = 0) (yy : cT s y * J * y = 0) (xy : cT s x * J * y = 1) :
    ∃ (m : ℕ) (J' : Matrix (Fin m) (Fin m) K) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K),
      Fr s J J' P Q x y := by
  have yx : cT s y * J * x = 1 := by
    have := congrArg (cT s) xy
    have cc : ∀ {a b : Type} (M : Matrix a b K), cT s (cT s M) = M := fun M => Matrix.ext fun _ _ => ss _
    rwa [cT_mul, cT_mul, cc, herm, cT_one, ← Matrix.mul_assoc] at this
  set a := cT s y * J with ha
  set b := cT s x * J with hb
  set A : Matrix (Fin n) (Fin n) K := 1 - x * a - y * b with hA
  have Ax : A * x = 0 := by
    simp only [hA, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc x a, Matrix.mul_assoc y b, yx, xx, Matrix.mul_one]
    simp
  have Ay : A * y = 0 := by
    simp only [hA, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc x a, Matrix.mul_assoc y b, yy, xy, Matrix.mul_one]
    simp
  have aA : a * A = 0 := by
    simp only [hA, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc a, yx, yy, Matrix.one_mul]
    simp
  have bA : b * A = 0 := by
    simp only [hA, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc b, xx, xy, Matrix.one_mul]
    simp
  have AA : A * A = A := by
    have e1 : A * (x * a) = 0 := by rw [← Matrix.mul_assoc, Ax, Matrix.zero_mul]
    have e2 : A * (y * b) = 0 := by rw [← Matrix.mul_assoc, Ay, Matrix.zero_mul]
    calc A * A = A * (1 - x * a - y * b) := rfl
      _ = A := by rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, e1, e2]; simp
  obtain ⟨m, P, Q, hPQ, hQP⟩ := exists_split A AA
  have hQ : Q * A = Q := by rw [← hPQ, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hP : A * P = P := by rw [← hPQ, Matrix.mul_assoc, hQP, Matrix.mul_one]
  refine ⟨m, cT s P * J * P, P, Q, ss, herm, rfl, hQP, ?_, ?_, ?_, xx, yy, xy, ?_, ?_⟩
  · rw [← hQ, Matrix.mul_assoc, Ax, Matrix.mul_zero]
  · rw [← hQ, Matrix.mul_assoc, Ay, Matrix.mul_zero]
  · rw [hPQ, hA]; abel
  · rw [← hP, ← Matrix.mul_assoc, bA, Matrix.zero_mul]
  · rw [← hP, ← Matrix.mul_assoc, aA, Matrix.zero_mul]

variable {s : K →+* K} {J : Matrix (Fin n) (Fin n) K} {J' : Matrix (Fin m) (Fin m) K}
  {P : Matrix (Fin n) (Fin m) K} {Q : Matrix (Fin m) (Fin n) K} {x y : Matrix (Fin n) (Fin 1) K}

theorem Fr.det_ne (h : Fr s J J' P Q x y) (hJ : J.det ≠ 0) : J'.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e1 : J *ᵥ (P *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← h.Qgram, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]
  have e2 : P *ᵥ v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ e1
  apply hv
  have e3 := congrArg (Q *ᵥ ·) e2
  simpa [Matrix.mulVec_mulVec, h.QP] using e3

theorem hform_eq (s : K →+* K) (J : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    Formalism.UG.hform s J u v = (fun i => s (u i)) ⬝ᵥ (J *ᵥ v) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem Fr.hform_P (h : Fr s J J' P Q x y) (z : Fin m → K) :
    Formalism.UG.hform s J (P *ᵥ z) (P *ᵥ z) = Formalism.UG.hform s J' z z := by
  have e : (fun i => s ((P *ᵥ z) i)) = P.map s *ᵥ (fun i => s (z i)) := funext fun i => RingHom.map_mulVec s P z i
  have e2 : J' *ᵥ z = cT s P *ᵥ ((J * P) *ᵥ z) := by rw [Matrix.mulVec_mulVec, ← h.gram, Matrix.mul_assoc]
  rw [hform_eq, hform_eq, e, Matrix.mulVec_mulVec, e2, Matrix.dotProduct_mulVec (fun i => s (z i))]
  change _ = ((fun i => s (z i)) ᵥ* (P.map s)ᵀ) ⬝ᵥ _
  rw [Matrix.vecMul_transpose]

end Fld

section Witt

open NumberField GlobalTheory.SiegelSet Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem gram_sub {K : Type} [CommRing K] {n a b c d : ℕ} (s : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (U : Matrix (Fin n) (Fin a) K) (V : Matrix (Fin n) (Fin b) K) (f : Fin c → Fin a) (g : Fin d → Fin b) :
    cT s (U.submatrix id f) * J * V.submatrix id g = (cT s U * J * V).submatrix f g := by
  ext i j; simp [cT, Matrix.mul_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E} {P : Matrix (Fin n) (Fin m) E}
  {Q : Matrix (Fin m) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem exists_fr_witt (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ (m : ℕ) (J' : Matrix (Fin m) (Fin m) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin n) E),
      Fr (σ : E →+* E) J J' P Q (hd X) (hd Y) := by
  refine exists_fr (s := (σ : E →+* E)) (fun a => sigma_sigma h a) (Matrix.ext fun i j => hJ.1 i j) ?_ ?_ ?_
  · rw [gram_sub, hW.xx]; rfl
  · rw [gram_sub, hW.yy]; rfl
  · rw [gram_sub, hW.xy]; ext i j; rw [Subsingleton.elim i j]; simp

variable (h : Fr (σ : E →+* E) J J' P Q (hd X) (hd Y)) (hW : IsWittFrame σ J X Y)
include h hW

theorem Fr.yxW : cT (σ : E →+* E) Y * J * X = 1 := by
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rwa [cT_mul, cT_mul, h.cc, h.herm, cT_one, ← Matrix.mul_assoc] at this

theorem Fr.orth : cT (σ : E →+* E) (hd X) * J * tl X = 0 ∧ cT (σ : E →+* E) (hd X) * J * tl Y = 0 ∧
    cT (σ : E →+* E) (hd Y) * J * tl X = 0 ∧ cT (σ : E →+* E) (hd Y) * J * tl Y = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gram_sub, hW.xx]; rfl
  · rw [gram_sub, hW.xy]; ext i j; simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  · rw [gram_sub, h.yxW hW]; ext i j; simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  · rw [gram_sub, hW.yy]; rfl

theorem Fr.P_tlX : P * (Q * tl X) = tl X := by
  obtain ⟨o1, -, o3, -⟩ := h.orth hW
  have e := congrArg (· * tl X) h.res
  simp only [Matrix.add_mul, Matrix.one_mul] at e
  rw [Matrix.mul_assoc (hd X), o3, Matrix.mul_assoc (hd Y), o1, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero] at e
  rwa [Matrix.mul_assoc] at e

theorem Fr.P_tlY : P * (Q * tl Y) = tl Y := by
  obtain ⟨-, o2, -, o4⟩ := h.orth hW
  have e := congrArg (· * tl Y) h.res
  simp only [Matrix.add_mul, Matrix.one_mul] at e
  rw [Matrix.mul_assoc (hd X), o4, Matrix.mul_assoc (hd Y), o2, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero] at e
  rwa [Matrix.mul_assoc] at e

theorem Fr.gram_P {a b : ℕ} (U : Matrix (Fin m) (Fin a) E) (V : Matrix (Fin m) (Fin b) E) :
    cT (σ : E →+* E) U * J' * V = cT (σ : E →+* E) (P * U) * J * (P * V) := by
  rw [← h.gram, cT_mul]; simp only [Matrix.mul_assoc]

theorem Fr.witt : IsWittFrame σ J' (Q * tl X) (Q * tl Y) := by
  have pX := h.P_tlX hW
  have pY := h.P_tlY hW
  have row : ∀ {U : Matrix (Fin n) (Fin (r + 1)) E} {w : Fin n → E}, (cT (σ : E →+* E) (hd U) * J) *ᵥ w = 0 →
      (cT (σ : E →+* E) (tl U) * J) *ᵥ w = 0 → (cT (σ : E →+* E) U * J) *ᵥ w = 0 := fun {U w} e1 e2 => by
    funext i
    induction i using Fin.cases with
    | zero =>
      have := congrFun e1 0
      rwa [← cT_sub_row] at this
    | succ i =>
      have := congrFun e2 i
      rwa [← cT_sub_row] at this
  have tlz : ∀ {U : Matrix (Fin n) (Fin (r + 1)) E} {z : Fin m → E}, (cT (σ : E →+* E) (Q * tl U) * J') *ᵥ z = 0 →
      (cT (σ : E →+* E) (tl U) * J) *ᵥ (P *ᵥ z) = 0 := fun {U z} e => by
    rw [cT_mul, Matrix.mul_assoc, h.Qgram, ← Matrix.mul_assoc] at e
    rwa [Matrix.mulVec_mulVec]
  refine ⟨?_, ?_, ?_, fun z h1 h2 h3 => ?_⟩
  · rw [h.gram_P hW, pX, gram_sub, hW.xx]; rfl
  · rw [h.gram_P hW, pY, gram_sub, hW.yy]; rfl
  · rw [h.gram_P hW, pX, pY, gram_sub, hW.xy, Matrix.submatrix_one _ (Fin.succ_injective _)]
  · have e1 : (cT (σ : E →+* E) (hd X) * J) *ᵥ (P *ᵥ z) = 0 := by rw [Matrix.mulVec_mulVec, h.xP]; simp
    have e2 : (cT (σ : E →+* E) (hd Y) * J) *ᵥ (P *ᵥ z) = 0 := by rw [Matrix.mulVec_mulVec, h.yP]; simp
    have e3 : P *ᵥ z = 0 := hW.aniso _ (row e1 (tlz h1)) (row e2 (tlz h2)) ((h.hform_P z).trans h3)
    have e4 := congrArg (Q *ᵥ ·) e3
    simpa [Matrix.mulVec_mulVec, h.QP] using e4

end Witt

section Adelic

open NumberField GlobalTheory.SiegelSet Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open scoped TensorProduct

theorem iM_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (φ : R →+* R') (P : Matrix (Fin n) (Fin m) R)
    (Q : Matrix (Fin m) (Fin n) R) (g : Matrix (Fin m) (Fin m) R) :
    (iM P Q g).map φ = iM (P.map φ) (Q.map φ) (g.map φ) := by
  simp only [iM]
  rw [Matrix.map_add _ (map_add φ), Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem Fr.map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} {s : R →+* R} {s' : R' →+* R'} (φ : R →+* R')
    (hs : ∀ a, φ (s a) = s' (φ a)) (ss' : ∀ a, s' (s' a) = a) {J : Matrix (Fin n) (Fin n) R}
    {J' : Matrix (Fin m) (Fin m) R} {P : Matrix (Fin n) (Fin m) R} {Q : Matrix (Fin m) (Fin n) R}
    {x y : Matrix (Fin n) (Fin 1) R} (h : Fr s J J' P Q x y) :
    Fr s' (J.map φ) (J'.map φ) (P.map φ) (Q.map φ) (x.map φ) (y.map φ) := by
  have c : ∀ {a b : Type} (M : Matrix a b R), cT s' (M.map φ) = (cT s M).map φ :=
    fun M => Matrix.ext fun i j => (hs _).symm
  refine ⟨ss', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c, h.herm]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.gram]
  · rw [← Matrix.map_mul, h.QP, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, h.Qx, Matrix.map_zero _ (map_zero _)]
  · rw [← Matrix.map_mul, h.Qy, Matrix.map_zero _ (map_zero _)]
  · rw [c, c, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_add _ (map_add φ), ← Matrix.map_add _ (map_add φ), h.res, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.xx, Matrix.map_zero _ (map_zero _)]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.yy, Matrix.map_zero _ (map_zero _)]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.xP, Matrix.map_zero _ (map_zero _)]
  · rw [c, ← Matrix.map_mul, ← Matrix.map_mul, h.yP, Matrix.map_zero _ (map_zero _)]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E} {P : Matrix (Fin n) (Fin m) E}
  {Q : Matrix (Fin m) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem Fr.ad (hσ : IsCMExt F E σ) (h : Fr (σ : E →+* E) J J' P Q (hd X) (hd Y)) :
    Fr (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (adMat F P) (adMat F Q) (adMat F (hd X)) (adMat F (hd Y)) :=
  h.map (inclR (AF F)) (fun a => (sigRA_inclR a).symm) (sigRA_sigRA σ hσ)

def Fr.iG (h : Fr (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (adMat F P) (adMat F Q) (adMat F (hd X)) (adMat F (hd Y))) :
    GAd σ J' →* GAd σ J := h.iU

variable (h : Fr (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (adMat F P) (adMat F Q) (adMat F (hd X)) (adMat F (hd Y)))

theorem Fr.iG_val (g : GAd σ J') : (matHom _ σ J (h.iG g)).1 = iM (adMat F P) (adMat F Q) (matHom _ σ J' g).1 := rfl

theorem Fr.continuous_iG : Continuous h.iG := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hc : ∀ (f : GAd σ J' → GAd σ J'), Continuous f →
      Continuous fun g => iM (adMat F P) (adMat F Q) (matHom _ σ J' (f g)).1 := fun f hf => by
    unfold iM
    exact continuous_const.add ((continuous_const.matrix_mul ((continuous_matHom_val (σ := σ) (J := J')).comp hf)).matrix_mul
      continuous_const)
  have hc2 : Continuous fun g => matHom _ σ J (h.iG g) := by
    refine Units.continuous_iff.2 ⟨hc _ continuous_id, ?_⟩
    refine (hc _ continuous_inv).congr fun g => ?_
    rw [← Fr.iG_val, map_inv, map_inv]
  exact continuous_induced_rng.2 hc2

end Adelic

section Adelic2

open NumberField GlobalTheory.SiegelSet Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' yx_eq_one)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E} {P : Matrix (Fin n) (Fin m) E}
  {Q : Matrix (Fin m) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem Fr.iG_rat (hσ : IsCMExt F E σ) (h₀ : Fr (σ : E →+* E) J J' P Q (hd X) (hd Y)) {γ : GAd σ J'}
    (hγ : γ ∈ ratPts σ J') : (h₀.ad hσ).iG γ ∈ ratPts σ J := by
  obtain ⟨γ₀, hγ₀, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨(h₀.iU ⟨γ₀, hγ₀⟩).1, (h₀.iU ⟨γ₀, hγ₀⟩).2, Units.ext ?_⟩)
  have e1 : (matHom _ σ J' γ).1 = γ₀.1.map (inclR (F := F) (AF F)) := (congrArg Units.val e).symm
  change (iM P Q γ₀.1).map (inclR (F := F) (AF F)) = (matHom _ σ J ((h₀.ad hσ).iG γ)).1
  rw [Fr.iG_val, e1, iM_map]

variable (h : Fr (sigR (AF F) σ) (JR (F := F) (AF F) J) (JR (AF F) J') (adMat F P) (adMat F Q) (adMat F (hd X)) (adMat F (hd Y)))

theorem Fr.iG_sends (g : GAd σ J') : Sends σ J (h.iG g) (Xᵀ 0) (Xᵀ 0) := by
  have e := h.levi_embedding_fixes_vector (matHom _ σ J' g).1
  funext i
  exact congrFun (congrFun e i) 0

theorem mem_minParOne_of {p : GAd σ J} {u : (AF F ⊗[F] E)ˣ} (hu : GlobalTheory.Doubling.absE F E u = 1)
    {c : Matrix (Fin 1) (Fin r) (AF F ⊗[F] E)} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (hdg : ∀ i, ∃ v : (AF F ⊗[F] E)ˣ, B i i = v ∧ GlobalTheory.Doubling.absE F E v = 1)
    (e1 : (matHom _ σ J p).1 * adMat F (hd X) = (u : AF F ⊗[F] E) • adMat F (hd X))
    (e2 : (matHom _ σ J p).1 * adMat F (tl X) = adMat F (hd X) * c + adMat F (tl X) * B) :
    p ∈ minParOne σ J X := by
  refine ⟨blk u c B, blk_bt hB, ?_, fun i => ?_⟩
  · refine ext_cols ?_ ?_
    · rw [(mul_blk _ _ _ _).1, mul_hd]
      exact e1
    · rw [(mul_blk _ _ _ _).2, mul_tl]
      exact e2
  · induction i using Fin.cases with
    | zero => exact ⟨u, rfl, hu⟩
    | succ i => exact hdg i

theorem Fr.iG_minParOne {X' : Matrix (Fin m) (Fin r) E} (hX : adMat F P * adMat F X' = adMat F (tl X)) {q : GAd σ J'}
    (hq : q ∈ minParOne σ J' X') : h.iG q ∈ minParOne σ J X := by
  obtain ⟨B, hB, e, hu⟩ := hq
  refine mem_minParOne_of (u := 1) (map_one _) (c := 0) hB hu ?_ ?_
  · rw [Fr.iG_val, h.levi_embedding_fixes_vector]; simp
  · rw [Fr.iG_val, ← hX, ← Matrix.mul_assoc, h.iM_P, Matrix.mul_assoc, e]; simp [Matrix.mul_assoc]

theorem Fr.nice_mem {X' : Matrix (Fin m) (Fin r) E} (hX : adMat F P * adMat F X' = adMat F (tl X)) {p : GAd σ J}
    {u : (AF F ⊗[F] E)ˣ} (hu : GlobalTheory.Doubling.absE F E u = 1) {c : Matrix (Fin 1) (Fin m) (AF F ⊗[F] E)}
    (e1 : (matHom _ σ J p).1 * adMat F (hd X) = (u : AF F ⊗[F] E) • adMat F (hd X))
    (e2 : (matHom _ σ J p).1 * adMat F P = adMat F P + adMat F (hd X) * c) : p ∈ minParOne σ J X := by
  refine mem_minParOne_of hu (c := c * adMat F X') (B := 1) Matrix.blockTriangular_one
    (fun i => ⟨1, Matrix.one_apply_eq _, map_one _⟩) e1 ?_
  rw [← hX, ← Matrix.mul_assoc, e2, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc (adMat F (hd X))]
  exact add_comm _ _

variable (F E) in

def dd {k : ℕ} (t : Fin k → ℝ) : Fin k → AF F ⊗[F] E := fun i => algebraMap (AF F) (AF F ⊗[F] E) (rId F (t i)) - 1

variable (σ J) in

def tM {k : ℕ} (U V : Matrix (Fin n) (Fin k) E) (t : Fin k → ℝ) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  1 + adMat F U * diagonal (dd F E t) * (cT (sigR (AF F) σ) (adMat F V) * JR (F := F) (AF F) J) +
    adMat F V * diagonal (dd F E (-t)) * (cT (sigR (AF F) σ) (adMat F U) * JR (F := F) (AF F) J)

theorem tor_eq (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) {k : ℕ} {U V : Matrix (Fin n) (Fin k) E}
    (hW : IsWittFrame σ J U V) {a : (Fin k → ℝ) → GAd σ J} (ha : IsTorus σ J U V a) (t : Fin k → ℝ) :
    (matHom _ σ J (a t)).1 = tM σ J U V t := by
  have yx := yx_eq_one (fun x => sigma_sigma hσ x) hJ hW
  set A : Matrix (Fin n) (Fin n) E := 1 - U * (cT (σ : E →+* E) V * J) - V * (cT (σ : E →+* E) U * J) with hA
  have o1 : cT (σ : E →+* E) U * J * A = 0 := by
    rw [hA, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ U, ← Matrix.mul_assoc _ V, hW.xx, hW.xy,
      Matrix.zero_mul, Matrix.one_mul]
    simp
  have o2 : cT (σ : E →+* E) V * J * A = 0 := by
    rw [hA, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ U, ← Matrix.mul_assoc _ V, hW.yy, yx,
      Matrix.zero_mul, Matrix.one_mul]
    simp
  set M := (matHom _ σ J (a t)).1 with hM
  have key : M * adMat F A = adMat F A := by
    ext i j
    exact congrFun (ha.onV t (fun l => A l j) (funext fun l => congrFun (congrFun o1 l) j)
      (funext fun l => congrFun (congrFun o2 l) j)) i
  have eA : adMat F A = 1 - adMat F U * (cT (sigR (AF F) σ) (adMat F V) * JR (F := F) (AF F) J) -
      adMat F V * (cT (sigR (AF F) σ) (adMat F U) * JR (F := F) (AF F) J) := by
    rw [← cT_map_inclR, ← cT_map_inclR]
    simp only [hA, JR, adMat]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Matrix.map_mul]
  set a₁ : Matrix (Fin k) (Fin n) (AF F ⊗[F] E) := cT (sigR (AF F) σ) (adMat F V) * JR (AF F) J
  set b₁ : Matrix (Fin k) (Fin n) (AF F ⊗[F] E) := cT (sigR (AF F) σ) (adMat F U) * JR (AF F) J
  have eA' : adMat F A = 1 - adMat F U * a₁ - adMat F V * b₁ := eA
  have e1 : (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) = adMat F A + adMat F U * a₁ + adMat F V * b₁ := by rw [eA']; abel
  have eT : tM σ J U V t = 1 + adMat F U * diagonal (dd F E t) * a₁ + adMat F V * diagonal (dd F E (-t)) * b₁ := rfl
  have dg : ∀ t : Fin k → ℝ, diagonal (dd F E t) = diagonal (fun i => algebraMap (AF F) (AF F ⊗[F] E) (rId F (t i))) - 1 := fun t => by
    rw [← diagonal_one, diagonal_sub]; rfl
  calc M = M * (adMat F A + adMat F U * a₁ + adMat F V * b₁) := by rw [← e1, Matrix.mul_one]
    _ = adMat F A + M * adMat F U * a₁ + M * adMat F V * b₁ := by
        rw [Matrix.mul_add, Matrix.mul_add, key, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = tM σ J U V t := by
        rw [hM, ha.onX t, ha.onY t, eA', eT, dg, dg]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Pi.neg_apply]
        abel

end Adelic2

section Adelic3

open NumberField GlobalTheory.SiegelSet Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero')
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E} {P : Matrix (Fin n) (Fin m) E}
  {Q : Matrix (Fin m) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

variable (F E) in

def d1 (c : ℝ) : AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E) (rId F c) - 1

theorem diffOne_zero : d1 F E 0 = 0 := by rw [d1, rId_zero', map_one, sub_self]

theorem tM_split (U V : Matrix (Fin n) (Fin (r + 1)) E) (u : Fin (r + 1) → ℝ) :
    adMat F U * diagonal (dd F E u) * (cT (sigR (AF F) σ) (adMat F V) * JR (F := F) (AF F) J) =
      adMat F (hd U) * diagonal (fun _ : Fin 1 => d1 F E (u 0)) * (cT (sigR (AF F) σ) (adMat F (hd V)) * JR (F := F) (AF F) J) +
      adMat F (tl U) * diagonal (fun i : Fin r => d1 F E (u i.succ)) * (cT (sigR (AF F) σ) (adMat F (tl V)) * JR (F := F) (AF F) J) := by
  rw [mul_diag_mul, cT_sub_row, cT_sub_row]
  rfl

theorem tM_cons_zero (t : Fin r → ℝ) : tM σ J X Y (Fin.cons 0 t) =
    1 + adMat F (tl X) * diagonal (dd F E t) * (cT (sigR (AF F) σ) (adMat F (tl Y)) * JR (F := F) (AF F) J) +
      adMat F (tl Y) * diagonal (dd F E (-t)) * (cT (sigR (AF F) σ) (adMat F (tl X)) * JR (F := F) (AF F) J) := by
  have e1 : (fun i : Fin r => d1 F E ((Fin.cons 0 t : Fin (r + 1) → ℝ) i.succ)) = dd F E t := rfl
  have e2 : (fun i : Fin r => d1 F E ((-(Fin.cons 0 t : Fin (r + 1) → ℝ)) i.succ)) = dd F E (-t) := rfl
  have e3 : (-(Fin.cons 0 t : Fin (r + 1) → ℝ)) 0 = 0 := by simp
  rw [tM, tM_split, tM_split, e1, e2, e3, Fin.cons_zero, diffOne_zero]
  simp

theorem tM_cons_right (c : ℝ) : tM σ J X Y (Fin.cons c 0) =
    1 + adMat F (hd X) * diagonal (fun _ : Fin 1 => d1 F E c) * (cT (sigR (AF F) σ) (adMat F (hd Y)) * JR (F := F) (AF F) J) +
      adMat F (hd Y) * diagonal (fun _ : Fin 1 => d1 F E (-c)) * (cT (sigR (AF F) σ) (adMat F (hd X)) * JR (F := F) (AF F) J) := by
  have e1 : (fun i : Fin r => d1 F E ((Fin.cons c 0 : Fin (r + 1) → ℝ) i.succ)) = 0 := funext fun _ => diffOne_zero
  have e2 : (fun i : Fin r => d1 F E ((-(Fin.cons c 0 : Fin (r + 1) → ℝ)) i.succ)) = 0 := funext fun i => by
    simp [diffOne_zero]
  have e3 : (-(Fin.cons c 0 : Fin (r + 1) → ℝ)) 0 = -c := by simp
  rw [tM, tM_split, tM_split, e1, e2, e3, Fin.cons_zero]
  have e4 : diagonal (0 : Fin r → AF F ⊗[F] E) = 0 := diagonal_zero
  rw [e4]
  simp

theorem hd_mul_bt {k : Type} {R : Type} [CommRing R] (U : Matrix k (Fin (r + 1)) R) {B : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (hB : B.BlockTriangular id) : hd (U * B) = B 0 0 • hd U := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero fun l _ => by rw [hB (show id (0 : Fin (r + 1)) < id l.succ from Fin.succ_pos l), mul_zero]]
  simp [mul_comm]

variable (h : Fr (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (adMat F P) (adMat F Q) (adMat F (hd X)) (adMat F (hd Y)))

theorem Fr.iG_tor (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (hJ' : IsHermND σ J')
    {X' Y' : Matrix (Fin m) (Fin r) E} (hW' : IsWittFrame σ J' X' Y') (hX : adMat F P * adMat F X' = adMat F (tl X))
    (hY : adMat F P * adMat F Y' = adMat F (tl Y)) {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    {a' : (Fin r → ℝ) → GAd σ J'} (ha' : IsTorus σ J' X' Y' a') (s' : Fin r → ℝ) : h.iG (a' s') = a (Fin.cons 0 s') := by
  refine matHom_injective _ σ J (Units.ext ?_)
  rw [Fr.iG_val, tor_eq hσ hJ' hW' ha', tor_eq hσ hJ hW ha, tM_cons_zero, tM]
  exact h.iM_tor hX hY _ _

theorem Fr.iG_comm (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin (r + 1) → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (c : ℝ) (g : GAd σ J') : Commute (a (Fin.cons c 0)) (h.iG g) := by
  refine matHom_injective _ σ J (Units.ext ?_)
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Fr.iG_val, tor_eq hσ hJ hW ha, tM_cons_right]
  exact h.tor_comm _ _ _

include h in
theorem Fr.tor_on_P (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin (r + 1) → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (c : ℝ) : (matHom _ σ J (a (Fin.cons c 0))).1 * adMat F P = adMat F P := by
  rw [tor_eq hσ hJ hW ha, tM_cons_right]
  exact h.tor_P _ _

theorem Fr.dec (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {X' : Matrix (Fin m) (Fin r) E}
    (hX : adMat F P * adMat F X' = adMat F (tl X)) {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) :
    ∃ g', ∃ q₀ ∈ minParOne σ J X, ∃ s₁ : ℝ, p = q₀ * a (Fin.cons s₁ 0) * h.iG g' ∧
      ∀ h', (h.iG h')⁻¹ * q₀ * h.iG h' ∈ minParOne σ J X := by
  haveI := hσ.1
  have hF := pfrA hσ hJ hW
  have hp' := inv_mem_minPar hσ hJ hW hp
  have matInv : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) E} (q : GAd σ K),
      (matHom _ σ K q).1 * (matHom _ σ K q⁻¹).1 = 1 ∧ (matHom _ σ K q⁻¹).1 * (matHom _ σ K q).1 = 1 := fun q => by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, inv_mul_cancel, map_one, Units.val_one]
    exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := matInv p
  have hU := unitaryA_matHom p
  have hU' := unitaryA_matHom p⁻¹
  have lin : ∀ q ∈ minPar σ J X, (matHom _ σ J q).1 * adMat F (hd X) = Bm σ J X Y q 0 0 • adMat F (hd X) := fun q hq => by
    obtain ⟨hbt, e⟩ := (mem_minPar_iff hF).1 hq
    have := congrArg hd e
    rw [mul_hd, hd_mul_bt _ hbt] at this
    exact this
  have hx := lin p hp
  have hx' := lin p⁻¹ hp'
  have gg1 := h.gg h1 h2 hU' hx
  have gg2 := h.gg h2 h1 hU hx'
  have gU := h.g_unitary h1 hU hx'
  let g' : GAd σ J' := ⟨⟨_, _, gg1, gg2⟩, gU⟩
  have hg1 : (matHom _ σ J' g').1 = adMat F Q * (matHom _ σ J p).1 * adMat F P := rfl
  have hg2 : (matHom _ σ J' g'⁻¹).1 = adMat F Q * (matHom _ σ J p⁻¹).1 * adMat F P := rfl
  let β := uU σ J X Y hσ hJ hW hp hp' 0
  have hβ : 0 < (GlobalTheory.Doubling.absE F E β : ℝ) := NNReal.coe_pos.2 (pos_hom' _ _)
  have h0 : (0 : ℝ) < 2 * (Module.finrank ℚ F : ℝ) := mul_pos two_pos (Nat.cast_pos.2 Module.finrank_pos)
  let s₁ : ℝ := Real.log (GlobalTheory.Doubling.absE F E β) / (2 * (Module.finrank ℚ F : ℝ))
  let u := β * rIdU F E (-s₁)
  have hu : GlobalTheory.Doubling.absE F E u = 1 := by
    apply NNReal.eq
    rw [map_mul, NNReal.coe_mul, absE_rIdU hσ.2.2.1, NNReal.coe_one, mul_neg, mul_div_cancel₀ _ h0.ne', Real.exp_neg,
      Real.exp_log hβ, mul_inv_cancel₀ hβ.ne']
  set t : Fin (r + 1) → ℝ := Fin.cons s₁ 0 with ht
  have ha0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have hainv : (a t)⁻¹ = a (-t) := inv_eq_of_mul_eq_one_right (by rw [← ha.add, add_neg_cancel, ha0])
  have hA1 : (matHom _ σ J (a t)⁻¹).1 * adMat F (hd X) = algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s₁)) • adMat F (hd X) := by
    have e := congrArg hd (ha.onX (-t))
    rw [mul_hd, hd_mul_bt _ (Matrix.blockTriangular_diagonal _), Matrix.diagonal_apply_eq] at e
    rw [hainv]
    exact e
  have hA2 : (matHom _ σ J (a t)⁻¹).1 * adMat F P = adMat F P := by
    obtain ⟨-, i2⟩ := matInv (a t)
    conv_lhs => rw [← h.tor_on_P hσ hJ hW ha s₁]
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  let q₀ := p * (h.iG g')⁻¹ * (a t)⁻¹
  have hN : (matHom _ σ J q₀).1 = (matHom _ σ J p).1 * iM (adMat F P) (adMat F Q) (matHom _ σ J' g'⁻¹).1 *
      (matHom _ σ J (a t)⁻¹).1 := by
    have e0 : q₀ = p * h.iG g'⁻¹ * (a t)⁻¹ := by simp only [q₀, map_inv]
    rw [e0, map_mul, map_mul, Units.val_mul, Units.val_mul, Fr.iG_val]
  have eN1 : (matHom _ σ J q₀).1 * adMat F (hd X) = (u : AF F ⊗[F] E) • adMat F (hd X) := by
    rw [hN, Matrix.mul_assoc, hA1, Matrix.mul_smul, Matrix.mul_assoc, h.levi_embedding_fixes_vector, hx, smul_smul]
    exact congrArg (· • adMat F (hd X)) (mul_comm _ _)
  have eN2 : (matHom _ σ J q₀).1 * adMat F P = adMat F P +
      adMat F (hd X) * ((cT (sigR (AF F) σ) (adMat F (hd Y)) * JR (F := F) (AF F) J * ((matHom _ σ J p).1 * adMat F P)) *
        (matHom _ σ J' g'⁻¹).1) := by
    have eMP : (matHom _ σ J p).1 * adMat F P = adMat F P * (matHom _ σ J' g').1 + adMat F (hd X) *
        (cT (sigR (AF F) σ) (adMat F (hd Y)) * JR (F := F) (AF F) J * ((matHom _ σ J p).1 * adMat F P)) := h.MP h1 hU hx'
    calc (matHom _ σ J q₀).1 * adMat F P = (matHom _ σ J p).1 * (iM (adMat F P) (adMat F Q) (matHom _ σ J' g'⁻¹).1 *
          ((matHom _ σ J (a t)⁻¹).1 * adMat F P)) := by rw [hN]; simp only [Matrix.mul_assoc]
      _ = (matHom _ σ J p).1 * adMat F P * (matHom _ σ J' g'⁻¹).1 := by rw [hA2, h.iM_P, Matrix.mul_assoc]
      _ = (adMat F P * (matHom _ σ J' g').1 + adMat F (hd X) *
          (cT (sigR (AF F) σ) (adMat F (hd Y)) * JR (F := F) (AF F) J * ((matHom _ σ J p).1 * adMat F P))) *
            (matHom _ σ J' g'⁻¹).1 := congrArg (· * (matHom _ σ J' g'⁻¹).1) eMP
      _ = _ := by rw [Matrix.add_mul, Matrix.mul_assoc, (matInv g').1, Matrix.mul_one, Matrix.mul_assoc]
  have all : ∀ h', (h.iG h')⁻¹ * q₀ * h.iG h' ∈ minParOne σ J X := fun h' => by
    obtain ⟨c1, c2⟩ := h.nice_conj eN1 eN2 (matInv h').2
    have e : (matHom _ σ J ((h.iG h')⁻¹ * q₀ * h.iG h')).1 = iM (adMat F P) (adMat F Q) (matHom _ σ J' h'⁻¹).1 *
        (matHom _ σ J q₀).1 * iM (adMat F P) (adMat F Q) (matHom _ σ J' h').1 := by
      have e0 : (h.iG h')⁻¹ = h.iG h'⁻¹ := (map_inv _ _).symm
      rw [e0, map_mul, map_mul, Units.val_mul, Units.val_mul, Fr.iG_val, Fr.iG_val]
    exact Fr.nice_mem hX hu (e ▸ c1) (e ▸ c2)
  refine ⟨g', q₀, ?_, s₁, ?_, all⟩
  · have := all 1
    simpa using this
  · change p = p * (h.iG g')⁻¹ * (a t)⁻¹ * a t * h.iG g'
    rw [inv_mul_cancel_right, inv_mul_cancel_right]

end Adelic3

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∃ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E) (ι : GAd σ J' →* GAd σ J), IsHermND σ J' ∧ IsWittFrame σ J' X' Y' ∧ Continuous ι ∧ (∀ γ ∈ ratPts σ J', ι γ ∈ ratPts σ J) ∧ (∀ g', Sends σ J (ι g') (Xᵀ 0) (Xᵀ 0)) ∧ (∀ q ∈ minParOne σ J' X', ι q ∈ minParOne σ J X) ∧ ∀ a, IsTorus σ J X Y a → (∀ a', IsTorus σ J' X' Y' a' → ∀ s', ι (a' s') = a (Fin.cons 0 s')) ∧ (∀ (s₁ : ℝ) g', Commute (a (Fin.cons s₁ 0)) (ι g')) ∧ ∀ p ∈ minPar σ J X, ∃ g', ∃ q₀ ∈ minParOne σ J X, ∃ s₁ : ℝ, p = q₀ * a (Fin.cons s₁ 0) * ι g' ∧ ∀ h', (ι h')⁻¹ * q₀ * ι h' ∈ minParOne σ J X := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  obtain ⟨m, J', P, Q, h₀⟩ := exists_fr_witt hσ hJ hW
  have hJ' : IsHermND σ J' :=
    ⟨fun i j => congrFun (congrFun h₀.herm' i) j, h₀.det_ne hJ.2⟩
  have hW' := h₀.witt hW
  have hA := h₀.ad hσ
  have hX : adMat F P * adMat F (Q * tl X) = adMat F (tl X) := by rw [← Matrix.map_mul, h₀.P_tlX hW]
  have hY : adMat F P * adMat F (Q * tl Y) = adMat F (tl Y) := by rw [← Matrix.map_mul, h₀.P_tlY hW]
  refine ⟨m, J', Q * tl X, Q * tl Y, hA.iG, hJ', hW', hA.continuous_iG, fun γ hγ => h₀.iG_rat hσ hγ, hA.iG_sends,
    fun q hq => hA.iG_minParOne hX hq, fun a ha => ⟨fun a' ha' s' => hA.iG_tor hσ hJ hW hJ' hW' hX hY ha ha' s',
      fun s₁ g' => hA.iG_comm hσ hJ hW ha s₁ g', fun p hp => hA.dec hσ hJ hW hX ha hp⟩⟩

end GlobalTheory.CompanionTheory.RedCov.Levi

end
