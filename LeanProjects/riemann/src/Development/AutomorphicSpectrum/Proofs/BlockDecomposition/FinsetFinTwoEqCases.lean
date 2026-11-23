import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

section Gen

variable {A : Type} [CommRing A] {M : ℕ}

theorem sum_two {B : Type} [AddCommMonoid B] (f : Fin (M + 2) → B) :
    ∑ i, f i = f 0 + (f 1 + ∑ i : Fin M, f i.succ.succ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]; rfl

def blk (P : Matrix (Fin (M + 2)) (Fin (M + 2)) A) : Matrix (Fin M) (Fin M) A :=
  Matrix.of fun i j => P i.succ.succ j.succ.succ

def dg (u : Matrix (Fin M) (Fin M) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A :=
  Matrix.of (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0))
    (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (u i))))

section DgEntries
variable (u : Matrix (Fin M) (Fin M) A)
@[simp] theorem dg_zero_zero : dg u 0 0 = 1 := rfl
@[simp] theorem dg_zero_one : dg u 0 1 = 0 := rfl
@[simp] theorem dg_one_zero : dg u 1 0 = 0 := rfl
@[simp] theorem dg_one_one : dg u 1 1 = 1 := rfl
@[simp] theorem dg_zero_rest (j : Fin M) : dg u 0 j.succ.succ = 0 := rfl
@[simp] theorem dg_one_rest (j : Fin M) : dg u 1 j.succ.succ = 0 := rfl
@[simp] theorem dg_rest_zero (i : Fin M) : dg u i.succ.succ 0 = 0 := rfl
@[simp] theorem dg_rest_one (i : Fin M) : dg u i.succ.succ 1 = 0 := rfl
@[simp] theorem dg_rest_rest (i j : Fin M) : dg u i.succ.succ j.succ.succ = u i j := rfl
end DgEntries

theorem finset_fin_two_eq_cases {p : Fin (M + 2) → Prop} (h0 : p 0) (h1 : p 1) (h2 : ∀ i : Fin M, p i.succ.succ)
    (i : Fin (M + 2)) : p i := by
  refine Fin.cases h0 (fun i => ?_) i
  exact Fin.cases h1 h2 i

theorem mat_ext2 {P Q : Matrix (Fin (M + 2)) (Fin (M + 2)) A}
    (h00 : P 0 0 = Q 0 0) (h01 : P 0 1 = Q 0 1) (h10 : P 1 0 = Q 1 0) (h11 : P 1 1 = Q 1 1)
    (h0r : ∀ j : Fin M, P 0 j.succ.succ = Q 0 j.succ.succ)
    (h1r : ∀ j : Fin M, P 1 j.succ.succ = Q 1 j.succ.succ)
    (hr0 : ∀ i : Fin M, P i.succ.succ 0 = Q i.succ.succ 0)
    (hr1 : ∀ i : Fin M, P i.succ.succ 1 = Q i.succ.succ 1)
    (hrr : ∀ i j : Fin M, P i.succ.succ j.succ.succ = Q i.succ.succ j.succ.succ) : P = Q := by
  ext i j
  refine finset_fin_two_eq_cases (p := fun i => P i j = Q i j) ?_ ?_ (fun i => ?_) i
  · exact finset_fin_two_eq_cases (p := fun j => P 0 j = Q 0 j) h00 h01 h0r j
  · exact finset_fin_two_eq_cases (p := fun j => P 1 j = Q 1 j) h10 h11 h1r j
  · exact finset_fin_two_eq_cases (p := fun j => P i.succ.succ j = Q i.succ.succ j) (hr0 i) (hr1 i) (hrr i) j

@[simp] theorem one_zero_zero : (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 0 0 = 1 := rfl
@[simp] theorem one_one_one : (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 1 1 = 1 :=
  Matrix.one_apply_eq _
@[simp] theorem one_zero_one : (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 0 1 = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_one_zero : (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 1 0 = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_zero_rest (j : Fin M) :
    (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 0 j.succ.succ = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_one_rest (j : Fin M) :
    (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 1 j.succ.succ = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_rest_zero (i : Fin M) :
    (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) i.succ.succ 0 = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_rest_one (i : Fin M) :
    (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) i.succ.succ 1 = 0 :=
  Matrix.one_apply_ne (by simp [Fin.ext_iff])
@[simp] theorem one_rest_rest (i j : Fin M) :
    (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) i.succ.succ j.succ.succ =
      (1 : Matrix (Fin M) (Fin M) A) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    simpa using h

theorem dg_one : dg (1 : Matrix (Fin M) (Fin M) A) = 1 := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp

theorem dg_mul (u v : Matrix (Fin M) (Fin M) A) : dg (u * v) = dg u * dg v := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    simp [Matrix.mul_apply, sum_two]

def rowv (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x : Fin M → A) (b : Fin M) : A :=
  ∑ a, s (x a) * J a b

def hv (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) : A :=
  ∑ b, rowv s J x b * y b

theorem gram_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (P : Matrix (Fin (M + 2)) (Fin (M + 2)) A) (i j : Fin (M + 2)) :
    (cT s P * hypOne J * P) i j = s (P 0 i) * P 1 j + s (P 1 i) * P 0 j +
      hv s J (fun a => P a.succ.succ i) (fun b => P b.succ.succ j) := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, sum_two,
    hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
    hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, mul_zero, mul_one,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add, hv, rowv]
  ring

def ColE (P : Matrix (Fin (M + 2)) (Fin (M + 2)) A) : Prop :=
  ∀ i, P i 0 = (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) i 0

theorem mul_col {P Q : Matrix (Fin (M + 2)) (Fin (M + 2)) A} (hQ : ColE Q) (i : Fin (M + 2)) :
    (P * Q) i 0 = P i 0 := by
  rw [Matrix.mul_apply]
  simp only [hQ _]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem row_one (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    {P : Matrix (Fin (M + 2)) (Fin (M + 2)) A} (hU : cT s P * hypOne J * P = hypOne J)
    (hC : ColE P) (j : Fin (M + 2)) : P 1 j = hypOne J 0 j := by
  have h := gram_entry s J P 0 j
  rw [hU] at h
  have h00 : P 0 0 = 1 := hC 0
  have h10 : P 1 0 = 0 := hC 1
  have hr : (fun a : Fin M => P a.succ.succ 0) = 0 := by
    funext a; exact hC _
  rw [h00, h10, hr] at h
  simpa [hv, rowv] using h.symm

theorem blk_mul {P Q : Matrix (Fin (M + 2)) (Fin (M + 2)) A}
    (hP : ∀ i : Fin M, P i.succ.succ 0 = 0) (hQ : ∀ j : Fin M, Q 1 j.succ.succ = 0) :
    blk (P * Q) = blk P * blk Q := by
  ext i j
  simp [blk, Matrix.mul_apply, sum_two, hP, hQ]

theorem blk_one : blk (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) A) = 1 := by
  ext i j; simp [blk]

theorem blk_dg (u : Matrix (Fin M) (Fin M) A) : blk (dg u) = u := by
  ext i j; simp [blk]

theorem blk_unitary (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    {P : Matrix (Fin (M + 2)) (Fin (M + 2)) A} (hU : cT s P * hypOne J * P = hypOne J)
    (hC : ColE P) : cT s (blk P) * J * blk P = J := by
  ext i j
  have h := gram_entry s J P i.succ.succ j.succ.succ
  rw [hU, row_one s J hU hC j.succ.succ, hypOne_zero_rest, hypOne_rest_rest] at h
  have h2 : P 1 i.succ.succ = 0 := by rw [row_one s J hU hC]; rfl
  rw [h2] at h
  simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add] at h
  rw [h]
  simp [Matrix.mul_apply, cT, blk, hv, rowv]

theorem dg_unitary (s : A →+* A) (J u : Matrix (Fin M) (Fin M) A) (hu : cT s u * J * u = J) :
    cT s (dg u) * hypOne J * dg u = hypOne J := by
  have key : ∀ i j : Fin M, hv s J (fun a => u a i) (fun b => u b j) = J i j := by
    intro i j
    have := congrFun (congrFun hu i) j
    rw [← this]
    simp [Matrix.mul_apply, cT, hv, rowv]
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rw [gram_entry] <;>
    simp [key, hv, rowv, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one,
      hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]
  all_goals exact key _ _

def stabG (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) : Subgroup (GL (Fin (M + 2)) A) where
  carrier := {g | g ∈ UJ s (hypOne J) ∧ ColE (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A)}
  one_mem' := ⟨one_mem _, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ca⟩ ⟨hb, cb⟩
    refine ⟨mul_mem ha hb, fun i => ?_⟩
    rw [Units.val_mul, mul_col cb]
    exact ca i
  inv_mem' := by
    rintro a ⟨ha, ca⟩
    refine ⟨inv_mem ha, fun i => ?_⟩
    have h := mul_col (P := ((a⁻¹ : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A)) ca i
    rw [← Units.val_mul, inv_mul_cancel] at h
    exact h.symm

variable {s : A →+* A} {J : Matrix (Fin M) (Fin M) A}

theorem stabG_unit {g : GL (Fin (M + 2)) A} (hg : g ∈ stabG s J) :
    cT s (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) * hypOne J * (g : Matrix _ _ A) = hypOne J := hg.1

theorem stabG_col {g : GL (Fin (M + 2)) A} (hg : g ∈ stabG s J) :
    ColE (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) := hg.2

theorem stabG_rest_zero {g : GL (Fin (M + 2)) A} (hg : g ∈ stabG s J) (i : Fin M) :
    (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) i.succ.succ 0 = 0 := by
  rw [stabG_col hg]; simp

theorem stabG_row {g : GL (Fin (M + 2)) A} (hg : g ∈ stabG s J) (j : Fin M) :
    (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) 1 j.succ.succ = 0 := by
  rw [row_one s J (stabG_unit hg) (stabG_col hg)]; rfl

theorem blk_mul_stabG {g h : GL (Fin (M + 2)) A} (hg : g ∈ stabG s J) (hh : h ∈ stabG s J) :
    blk ((g * h : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) =
      blk (g : Matrix _ _ A) * blk (h : Matrix _ _ A) := by
  rw [Units.val_mul]
  exact blk_mul (stabG_rest_zero hg) (stabG_row hh)

variable (s J) in

def piG : stabG s J →* GL (Fin M) A :=
  MonoidHom.mk' (fun g =>
    { val := blk ((g : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A)
      inv := blk (((g⁻¹ : stabG s J) : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A)
      val_inv := by
        rw [← blk_mul_stabG g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel]
        exact blk_one
      inv_val := by
        rw [← blk_mul_stabG (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel]
        exact blk_one })
    (fun g h => Units.ext (blk_mul_stabG g.2 h.2))

theorem piG_val (g : stabG s J) :
    ((piG s J g : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) =
      blk ((g : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) := rfl

theorem piG_mem (g : stabG s J) : piG s J g ∈ UJ s J :=
  blk_unitary s J (stabG_unit g.2) (stabG_col g.2)

def dgHom : Matrix (Fin M) (Fin M) A →* Matrix (Fin (M + 2)) (Fin (M + 2)) A where
  toFun := dg
  map_one' := dg_one
  map_mul' := dg_mul

def dgGL : GL (Fin M) A →* GL (Fin (M + 2)) A := Units.map dgHom

theorem dgGL_val (u : GL (Fin M) A) :
    ((dgGL u : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) =
      dg (u : Matrix (Fin M) (Fin M) A) := rfl

theorem dgGL_mem {u : GL (Fin M) A} (hu : u ∈ UJ s J) : dgGL u ∈ stabG s J := by
  refine ⟨dg_unitary s J _ hu, fun i => ?_⟩
  refine finset_fin_two_eq_cases (p := fun i => dg (u : Matrix (Fin M) (Fin M) A) i 0 = (1 : Matrix _ _ A) i 0)
    ?_ ?_ (fun i => ?_) i <;> simp

def nM (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w : Fin M → A) (z : A) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) A :=
  Matrix.of (Fin.cons (Fin.cons 1 (Fin.cons z fun j => -rowv s J w j))
    (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
      fun i => Fin.cons 0 (Fin.cons (w i) ((1 : Matrix (Fin M) (Fin M) A) i))))

section NEntries
variable (s J) (w : Fin M → A) (z : A)
@[simp] theorem nM_zero_zero : nM s J w z 0 0 = 1 := rfl
@[simp] theorem nM_zero_one : nM s J w z 0 1 = z := rfl
@[simp] theorem nM_one_zero : nM s J w z 1 0 = 0 := rfl
@[simp] theorem nM_one_one : nM s J w z 1 1 = 1 := rfl
@[simp] theorem nM_zero_rest (j : Fin M) : nM s J w z 0 j.succ.succ = -rowv s J w j := rfl
@[simp] theorem nM_one_rest (j : Fin M) : nM s J w z 1 j.succ.succ = 0 := rfl
@[simp] theorem nM_rest_zero (i : Fin M) : nM s J w z i.succ.succ 0 = 0 := rfl
@[simp] theorem nM_rest_one (i : Fin M) : nM s J w z i.succ.succ 1 = w i := rfl
@[simp] theorem nM_rest_rest (i j : Fin M) :
    nM s J w z i.succ.succ j.succ.succ = (1 : Matrix (Fin M) (Fin M) A) i j := rfl
end NEntries

theorem rowv_add (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w w' : Fin M → A) (b : Fin M) :
    rowv s J (w + w') b = rowv s J w b + rowv s J w' b := by
  simp [rowv, add_mul, Finset.sum_add_distrib]

theorem rowv_neg (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w : Fin M → A) (b : Fin M) :
    rowv s J (-w) b = -rowv s J w b := by
  simp [rowv]

theorem rowv_zero (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (b : Fin M) :
    rowv s J (0 : Fin M → A) b = 0 := by
  simp [rowv]

theorem hv_neg_left (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w w' : Fin M → A) :
    hv s J (-w) w' = -hv s J w w' := by
  simp [hv, rowv_neg]

theorem hv_neg_right (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w w' : Fin M → A) :
    hv s J w (-w') = -hv s J w w' := by
  simp [hv]

theorem hv_single (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w : Fin M → A) (j : Fin M) :
    hv s J w (fun b => (1 : Matrix (Fin M) (Fin M) A) b j) = rowv s J w j := by
  simp [hv, Matrix.one_apply]

theorem nM_zero (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) : nM s J 0 0 = 1 := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp [rowv_zero]

theorem nM_mul (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (w w' : Fin M → A) (z z' : A) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hv s J w w') := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    simp [Matrix.mul_apply, sum_two, rowv_add, Matrix.one_apply, hv]
  ring

theorem s_rowv (hs : ∀ x, s (s x) = x) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin M → A) (i : Fin M) :
    s (rowv s J w i) = ∑ b, J i b * w b := by
  simp only [rowv, map_sum, map_mul, hs]
  exact Finset.sum_congr rfl fun b _ => by rw [hJ, mul_comm]

theorem nM_unitary (hs : ∀ x, s (s x) = x) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin M → A) (z : A)
    (hz : z + s z + hv s J w w = 0) : cT s (nM s J w z) * hypOne J * nM s J w z = hypOne J := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [gram_entry]; simp [hv, rowv, hypOne_zero_zero]
  · rw [gram_entry]; simp [hv, rowv, hypOne_zero_one]
  · rw [gram_entry]; simp [hv, rowv, hypOne_one_zero]
  · rw [gram_entry]
    simp only [nM_zero_one, nM_one_one, nM_rest_one, map_one, one_mul, mul_one, hypOne_one_one]
    rw [← hz]; ring
  · intro j; rw [gram_entry]; simp [hv, rowv, hypOne_zero_rest]
  · intro j
    rw [gram_entry]
    simp only [nM_zero_one, nM_one_one, nM_one_rest, nM_zero_rest, nM_rest_one, nM_rest_rest,
      map_one, one_mul, mul_zero, zero_add, hypOne_one_rest, hv_single]
    ring
  · intro i; rw [gram_entry]; simp [hv, rowv, hypOne_rest_zero]
  · intro i
    rw [gram_entry]
    simp only [nM_zero_rest, nM_one_rest, nM_one_one, nM_zero_one, nM_rest_one, nM_rest_rest,
      map_neg, map_zero, s_rowv hs hJ, mul_one, zero_mul, add_zero, hypOne_rest_one]
    simp [hv, rowv, Matrix.one_apply]
  · intro i j
    rw [gram_entry]
    simp [hv, rowv, hypOne_rest_rest, Matrix.one_apply]

def nGL (hs : ∀ x, s (s x) = x) (w : Fin M → A) (z : A) (hz : z + s z + hv s J w w = 0) :
    GL (Fin M.succ.succ) A where
  val := nM s J w z
  inv := nM s J (-w) (s z)
  val_inv := by
    rw [nM_mul, hv_neg_right, add_neg_cancel, ← nM_zero s J]
    congr 1
    rw [← hz]; ring
  inv_val := by
    rw [nM_mul, hv_neg_left, neg_add_cancel, ← nM_zero s J]
    congr 1
    rw [← hz]; ring

theorem nGL_val (hs : ∀ x, s (s x) = x) (w : Fin M → A) (z : A) (hz : z + s z + hv s J w w = 0) :
    ((nGL hs w z hz : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) = nM s J w z := rfl

theorem nGL_mem (hs : ∀ x, s (s x) = x) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin M → A) (z : A)
    (hz : z + s z + hv s J w w = 0) : nGL hs w z hz ∈ stabG s J := by
  refine ⟨nM_unitary hs hJ w z hz, fun i => ?_⟩
  rw [nGL_val]
  refine finset_fin_two_eq_cases (p := fun i => nM s J w z i 0 = (1 : Matrix _ _ A) i 0) ?_ ?_ (fun i => ?_) i <;>
    simp

theorem blk_nM (w : Fin M → A) (z : A) : blk (nM s J w z) = 1 := by
  ext i j; simp [blk]

theorem eq_nM {P : Matrix (Fin (M + 2)) (Fin (M + 2)) A} (hU : cT s P * hypOne J * P = hypOne J)
    (hC : ColE P) (hb : blk P = 1) :
    P = nM s J (fun i => P i.succ.succ 1) (P 0 1) ∧
      P 0 1 + s (P 0 1) + hv s J (fun i => P i.succ.succ 1) (fun i => P i.succ.succ 1) = 0 := by
  have h00 : P 0 0 = 1 := hC 0
  have h10 : P 1 0 = 0 := hC 1
  have hr0 : ∀ i : Fin M, P i.succ.succ 0 = 0 := fun i => by rw [hC]; simp
  have h11 : P 1 1 = 1 := row_one s J hU hC 1
  have h1r : ∀ j : Fin M, P 1 j.succ.succ = 0 := fun j => row_one s J hU hC j.succ.succ
  have hrr : ∀ i j : Fin M, P i.succ.succ j.succ.succ = (1 : Matrix (Fin M) (Fin M) A) i j :=
    fun i j => congrFun (congrFun hb i) j
  have e1 : ∀ j : Fin M, P 0 j.succ.succ = -rowv s J (fun i => P i.succ.succ 1) j := by
    intro j
    have h := gram_entry s J P 1 j.succ.succ
    rw [hU, hypOne_one_rest, h1r, h11] at h
    simp only [mul_zero, map_one, one_mul, zero_add] at h
    have e : (fun b : Fin M => P b.succ.succ j.succ.succ) =
        fun b => (1 : Matrix (Fin M) (Fin M) A) b j := by
      funext b; exact hrr b j
    rw [e, hv_single] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  refine ⟨?_, ?_⟩
  · refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa using h00
    · simp
    · simpa using h10
    · simpa using h11
    · intro j; simpa using e1 j
    · intro j; simpa using h1r j
    · intro i; simpa using hr0 i
    · intro i; simp
    · intro i j; simpa using hrr i j
  · have h := gram_entry s J P 1 1
    rw [hU, hypOne_one_one, h11] at h
    simp only [map_one, one_mul, mul_one] at h
    rw [h]
    ring

section Map

variable {B : Type} [CommRing B] (φ : A →+* B)

theorem dg_map (u : Matrix (Fin M) (Fin M) A) : (dg u).map φ = dg (u.map φ) := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp

theorem blk_map (P : Matrix (Fin (M + 2)) (Fin (M + 2)) A) : blk (P.map φ) = (blk P).map φ := rfl

theorem rowv_map {s' : B →+* B} (hφ : ∀ x, φ (s x) = s' (φ x)) (w : Fin M → A) (b : Fin M) :
    φ (rowv s J w b) = rowv s' (J.map φ) (fun i => φ (w i)) b := by
  simp [rowv, hφ]

theorem hv_map {s' : B →+* B} (hφ : ∀ x, φ (s x) = s' (φ x)) (w w' : Fin M → A) :
    φ (hv s J w w') = hv s' (J.map φ) (fun i => φ (w i)) (fun i => φ (w' i)) := by
  simp [hv, rowv_map φ hφ]

theorem nM_map {s' : B →+* B} (hφ : ∀ x, φ (s x) = s' (φ x)) (w : Fin M → A) (z : A) :
    (nM s J w z).map φ = nM s' (J.map φ) (fun i => φ (w i)) (φ z) := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    simp [rowv_map φ hφ, Matrix.one_apply, apply_ite φ]

end Map

section Vec

variable {k : ℕ}

theorem dg_mulVec_cons (u : Matrix (Fin M) (Fin M) A) (x y : A) (v : Fin M → A) :
    dg u *ᵥ (Fin.cons x (Fin.cons y v) : Fin (M + 2) → A) = Fin.cons x (Fin.cons y (u *ᵥ v)) := by
  funext i
  refine finset_fin_two_eq_cases (p := fun i => (dg u *ᵥ (Fin.cons x (Fin.cons y v) : Fin (M + 2) → A)) i =
    (Fin.cons x (Fin.cons y (u *ᵥ v)) : Fin (M + 2) → A) i) ?_ ?_ (fun i => ?_) i <;>
    simp [Matrix.mulVec, dotProduct, sum_two]

def topRow (P : Matrix (Fin (M + 2)) (Fin (M + 2)) A) (v : Fin M → A) : A :=
  ∑ i, P 0 i.succ.succ * v i

theorem mulVec_cons_of_blk {P : Matrix (Fin (M + 2)) (Fin (M + 2)) A}
    (h00 : P 0 0 = 1) (h10 : P 1 0 = 0) (hr0 : ∀ i : Fin M, P i.succ.succ 0 = 0)
    (h1r : ∀ j : Fin M, P 1 j.succ.succ = 0) (hb : blk P = 1) (x : A) (v : Fin M → A) :
    P *ᵥ (Fin.cons x (Fin.cons 0 v) : Fin (M + 2) → A) =
      Fin.cons (x + topRow P v) (Fin.cons 0 v) := by
  have hrr : ∀ i j : Fin M, P i.succ.succ j.succ.succ = (1 : Matrix (Fin M) (Fin M) A) i j :=
    fun i j => congrFun (congrFun hb i) j
  funext i
  refine finset_fin_two_eq_cases (p := fun i => (P *ᵥ (Fin.cons x (Fin.cons 0 v) : Fin (M + 2) → A)) i =
    (Fin.cons (x + topRow P v) (Fin.cons 0 v) : Fin (M + 2) → A) i) ?_ ?_ (fun i => ?_) i
  · simp [Matrix.mulVec, dotProduct, sum_two, h00, topRow]
  · simp [Matrix.mulVec, dotProduct, sum_two, h10, h1r]
  · simp [Matrix.mulVec, dotProduct, sum_two, hr0, hrr, Matrix.one_apply]

theorem topRow_mul {P Q : Matrix (Fin (M + 2)) (Fin (M + 2)) A} (hP0 : P 0 0 = 1)
    (hQ : ∀ j : Fin M, Q 1 j.succ.succ = 0) (hQb : blk Q = 1) (v : Fin M → A) :
    topRow (P * Q) v = topRow P v + topRow Q v := by
  have hrr : ∀ i j : Fin M, Q i.succ.succ j.succ.succ = (1 : Matrix (Fin M) (Fin M) A) i j :=
    fun i j => congrFun (congrFun hQb i) j
  simp only [topRow, Matrix.mul_apply, sum_two, hP0, hQ, hrr, Finset.sum_add_distrib, add_mul,
    mul_zero, zero_add, one_mul, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [add_comm]

end Vec

end Gen

section Over

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem JR_hypOne {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) := by
  refine mat_ext2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    simp [JR, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def mkH (g : GL (Fin M) (R ⊗[F] E)) (hg : g ∈ HR R σ J) : HA R σ J := (⟨g, hg⟩ : HR R σ J)

theorem mat_mkH (g : GL (Fin M) (R ⊗[F] E)) (hg : g ∈ HR R σ J) :
    HA.mat R σ J (mkH R σ J g hg) = g := rfl

theorem mat_mem (h : HA R σ J) : HA.mat R σ J h ∈ HR R σ J :=
  Subtype.property (show HR R σ J from h)

theorem HA_ext {g h : HA R σ J} (e : HA.mat R σ J g = HA.mat R σ J h) : g = h :=
  Subtype.ext (p := fun x => x ∈ HR R σ J) e

theorem mat_mul' (g h : HA R σ J) : HA.mat R σ J (g * h) = HA.mat R σ J g * HA.mat R σ J h := rfl

theorem mat_one' : HA.mat R σ J 1 = 1 := rfl

theorem mulVec_first (P : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) (i : Fin (M + 2)) :
    (P *ᵥ (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E)) i = P i 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem first_eq_one (i : Fin (M + 2)) :
    (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → R ⊗[F] E) i =
      (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) i 0 := by
  refine finset_fin_two_eq_cases (p := fun i => (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → R ⊗[F] E) i =
      (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) i 0) ?_ ?_ (fun i => ?_) i <;> simp

theorem colE_iff (h : HA R σ (hypOne J)) :
    actW R σ (hypOne J) h (e0 _ M) = e0 _ M ↔
      ColE ((HA.mat R σ (hypOne J) h : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) := by
  constructor
  · intro e i
    have := congrFun (congrFun e 0) i
    change (((HA.mat R σ (hypOne J) h : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) *ᵥ
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E)) i =
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) i at this
    rw [mulVec_first, first_eq_one] at this
    exact this
  · intro c
    funext a i
    change (((HA.mat R σ (hypOne J) h : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) *ᵥ
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E)) i =
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) i
    rw [mulVec_first, first_eq_one]
    exact c i

theorem stab_mem_stabG (p : stabilizer₂ R σ J) :
    HA.mat R σ (hypOne J) p.1 ∈ stabG (sigR R σ) (JR R J) := by
  refine ⟨?_, (colE_iff R σ J p.1).1 p.2⟩
  rw [← JR_hypOne]
  exact mat_mem R σ (hypOne J) p.1

def toG : stabilizer₂ R σ J →* stabG (sigR R σ) (JR R J) :=
  MonoidHom.mk' (fun p => ⟨HA.mat R σ (hypOne J) p.1, stab_mem_stabG R σ J p⟩)
    (fun _ _ => rfl)

def piR : stabilizer₂ R σ J →* HA R σ J :=
  MonoidHom.mk' (fun p => mkH R σ J (piG _ _ (toG R σ J p)) (show _ ∈ UJ _ _ from piG_mem _))
    (fun p q => HA_ext R σ J (show piG _ _ (toG R σ J (p * q)) =
      piG _ _ (toG R σ J p) * piG _ _ (toG R σ J q) by rw [map_mul, map_mul]))

def iotaR : HA R σ J →* stabilizer₂ R σ J :=
  MonoidHom.mk' (fun u => ⟨mkH R σ (hypOne J) (dgGL (HA.mat R σ J u)) (by
      have h : dgGL (HA.mat R σ J u) ∈ stabG (sigR R σ) (JR R J) := dgGL_mem (mat_mem R σ J u)
      have h1 := h.1
      rw [← JR_hypOne] at h1
      exact h1), (colE_iff R σ J _).2 (dgGL_mem (s := sigR R σ) (J := JR R J) (mat_mem R σ J u)).2⟩)
    (fun u v => Subtype.ext (HA_ext R σ (hypOne J) (by
      change dgGL (HA.mat R σ J u * HA.mat R σ J v) = dgGL _ * dgGL _
      rw [map_mul])))

theorem mat_piR (p : stabilizer₂ R σ J) :
    ((HA.mat R σ J (piR R σ J p) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      blk ((HA.mat R σ (hypOne J) p.1 : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) := rfl

theorem mat_iotaR (u : HA R σ J) :
    ((HA.mat R σ (hypOne J) (iotaR R σ J u).1 : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) =
      dg ((HA.mat R σ J u : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := rfl

theorem piR_iotaR (u : HA R σ J) : piR R σ J (iotaR R σ J u) = u :=
  HA_ext R σ J (Units.ext (blk_dg _))

theorem actW_eq {n : ℕ} (h : HA R σ (hypOne J)) (X : Fin n → Fin (M + 2) → R ⊗[F] E) (a : Fin n) :
    actW R σ (hypOne J) h X a =
      ((HA.mat R σ (hypOne J) h : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) *ᵥ X a := rfl

theorem first_cons :
    (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → R ⊗[F] E) = Fin.cons 1 (Fin.cons 0 (0 : Fin M → R ⊗[F] E)) := by
  funext i
  refine finset_fin_two_eq_cases (p := fun i => (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → R ⊗[F] E) i =
    (Fin.cons 1 (Fin.cons 0 (0 : Fin M → R ⊗[F] E)) : Fin (M + 2) → R ⊗[F] E) i) ?_ ?_ (fun i => ?_) i <;>
    simp

theorem actW_iotaR (k : ℕ) (u : HA R σ J) (a : Fin 1 → Fin k → R ⊗[F] E)
    (Y : Fin k → Fin M → R ⊗[F] E) :
    actW R σ (hypOne J) (iotaR R σ J u : HA R σ (hypOne J)) (consA a Y) =
      consA a (actW R σ J u Y) := by
  funext r
  rw [actW_eq, mat_iotaR]
  refine Fin.cases ?_ (fun j => ?_) r
  · change dg _ *ᵥ (Fin.cons 1 fun _ => 0) = (Fin.cons 1 fun _ => 0)
    rw [first_cons, dg_mulVec_cons, Matrix.mulVec_zero]
  · change dg _ *ᵥ Fin.cons (a 0 j) (Fin.cons 0 (Y j)) = Fin.cons (a 0 j) (Fin.cons 0 _)
    rw [dg_mulVec_cons]
    rfl

abbrev matP (p : stabilizer₂ R σ J) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) :=
  ((HA.mat R σ (hypOne J) p.1 : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E))

theorem stabilizer_ext {p q : stabilizer₂ R σ J} (e : matP R σ J p = matP R σ J q) : p = q :=
  Subtype.ext (HA_ext R σ (hypOne J) (Units.ext e))

theorem toMatrix_mul₂ (p q : stabilizer₂ R σ J) : matP R σ J (p * q) = matP R σ J p * matP R σ J q := rfl

theorem toMatrix_unitary₂ (p : stabilizer₂ R σ J) :
    cT (sigR R σ) (matP R σ J p) * hypOne (JR R J) * matP R σ J p = hypOne (JR R J) :=
  (stab_mem_stabG R σ J p).1

theorem toMatrix_col (p : stabilizer₂ R σ J) : ColE (matP R σ J p) := (stab_mem_stabG R σ J p).2

theorem toMatrix_row (p : stabilizer₂ R σ J) (j : Fin M) : matP R σ J p 1 j.succ.succ = 0 :=
  stabG_row (stab_mem_stabG R σ J p) j

theorem ker_blk {m : stabilizer₂ R σ J} (hm : m ∈ (piR R σ J).ker) : blk (matP R σ J m) = 1 := by
  rw [← mat_piR, MonoidHom.mem_ker.1 hm]
  rfl

theorem actW_ker {k : ℕ} (m : (piR R σ J).ker) (a : Fin 1 → Fin k → R ⊗[F] E)
    (Y : Fin k → Fin M → R ⊗[F] E) :
    actW R σ (hypOne J) ((m : stabilizer₂ R σ J) : HA R σ (hypOne J)) (consA a Y) =
      consA (a + fun _ j => topRow (matP R σ J m) (Y j)) Y := by
  have hc := toMatrix_col R σ J m.1
  have h00 : matP R σ J m.1 0 0 = 1 := hc 0
  have h10 : matP R σ J m.1 1 0 = 0 := hc 1
  have hr0 : ∀ i : Fin M, matP R σ J m.1 i.succ.succ 0 = 0 := fun i => by rw [hc]; simp
  have key := mulVec_cons_of_blk h00 h10 hr0 (toMatrix_row R σ J m.1) (ker_blk R σ J m.2)
  funext r
  rw [actW_eq]
  refine Fin.cases ?_ (fun j => ?_) r
  · change matP R σ J m.1 *ᵥ (Fin.cons 1 fun _ => 0) = (Fin.cons 1 fun _ => 0)
    rw [first_cons, key]
    simp [topRow]
  · change matP R σ J m.1 *ᵥ Fin.cons (a 0 j) (Fin.cons 0 (Y j)) =
      Fin.cons (a 0 j + topRow (matP R σ J m.1) (Y j)) (Fin.cons 0 (Y j))
    rw [key]

theorem topRow_ker_mul (x y : (piR R σ J).ker) (v : Fin M → R ⊗[F] E) :
    topRow (matP R σ J ((x * y : (piR R σ J).ker) : stabilizer₂ R σ J)) v =
      topRow (matP R σ J x.1) v + topRow (matP R σ J y.1) v :=
  topRow_mul (toMatrix_col R σ J x.1 0) (toMatrix_row R σ J y.1) (ker_blk R σ J y.2) v

section Rat

theorem iotaR_rat {u : HA R σ J} (hu : u ∈ HFinIn R σ J) : iotaR R σ J u ∈ ratP R σ J := by
  obtain ⟨g, rfl⟩ := exists_ratH R σ J u hu
  refine (mem_HFinIn_iff R σ (hypOne J) _).2
    ⟨dgGL (g : GL (Fin M) E), (dgGL_mem (s := (σ : E →+* E)) g.2).1, Units.ext ?_⟩
  exact dg_map (inclR R) _

theorem incl_one_entry (i : Fin (M + 2)) :
    inclR (F := F) (E := E) R ((1 : Matrix (Fin (M + 2)) (Fin (M + 2)) E) i 0) =
      (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) i 0 := by
  refine finset_fin_two_eq_cases (p := fun i => inclR (F := F) (E := E) R ((1 : Matrix (Fin (M + 2)) (Fin (M + 2)) E) i 0) =
      (1 : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) i 0) ?_ ?_ (fun i => ?_) i <;> simp

theorem piR_rat (hinj : Function.Injective (inclR (F := F) (E := E) R)) {p : stabilizer₂ R σ J}
    (hp : p ∈ ratP R σ J) : piR R σ J p ∈ HFinIn R σ J := by
  obtain ⟨g, hg⟩ := exists_ratH R σ (hypOne J) p.1 hp
  have hm : matP R σ J p = ((g : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E).map (inclR R) := by
    change ((HA.mat R σ (hypOne J) p.1 : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) = _
    rw [hg, mat_ratH]
    rfl
  have hc : ColE ((g : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) := by
    intro i
    apply hinj
    have h := toMatrix_col R σ J p i
    rw [hm] at h
    rw [incl_one_entry]
    exact h
  have hS : (g : GL (Fin (M + 2)) E) ∈ stabG (σ : E →+* E) J := ⟨g.2, hc⟩
  refine (mem_HFinIn_iff R σ J _).2 ⟨piG _ _ ⟨_, hS⟩, piG_mem _, Units.ext ?_⟩
  change (blk ((g : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E)).map (inclR R) = blk (matP R σ J p)
  rw [hm]
  rfl

end Rat

end Over

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_HA_iff {X : Type} [TopologicalSpace X] {f : X → HA R σ J} :
    Continuous f ↔
      Continuous (fun x => ((HA.mat R σ J (f x) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) ∧
      Continuous (fun x => (((HA.mat R σ J (f x))⁻¹ : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) := by
  have h : Continuous f ↔ Continuous (fun x => HA.mat R σ J (f x)) :=
    (Topology.IsInducing.subtypeVal (t := (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))))).continuous_iff
  rw [h, Units.continuous_iff]
  rfl

theorem continuous_mat2 {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f : X → Matrix (Fin (M + 2)) (Fin (M + 2)) A}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1)
    (h0r : ∀ j : Fin M, Continuous fun x => f x 0 j.succ.succ)
    (h1r : ∀ j : Fin M, Continuous fun x => f x 1 j.succ.succ)
    (hr0 : ∀ i : Fin M, Continuous fun x => f x i.succ.succ 0)
    (hr1 : ∀ i : Fin M, Continuous fun x => f x i.succ.succ 1)
    (hrr : ∀ i j : Fin M, Continuous fun x => f x i.succ.succ j.succ.succ) : Continuous f := by
  refine continuous_matrix fun i j => ?_
  refine finset_fin_two_eq_cases (p := fun i => Continuous fun x => f x i j) ?_ ?_ (fun i => ?_) i
  · exact finset_fin_two_eq_cases (p := fun j => Continuous fun x => f x 0 j) h00 h01 h0r j
  · exact finset_fin_two_eq_cases (p := fun j => Continuous fun x => f x 1 j) h10 h11 h1r j
  · exact finset_fin_two_eq_cases (p := fun j => Continuous fun x => f x i.succ.succ j) (hr0 i) (hr1 i) (hrr i) j

theorem continuous_blk {A : Type} [CommRing A] [TopologicalSpace A] :
    Continuous (blk : Matrix (Fin (M + 2)) (Fin (M + 2)) A → Matrix (Fin M) (Fin M) A) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_dg {A : Type} [CommRing A] [TopologicalSpace A] :
    Continuous (dg : Matrix (Fin M) (Fin M) A → Matrix (Fin (M + 2)) (Fin (M + 2)) A) := by
  refine continuous_mat2 ?_ ?_ ?_ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_)
    (fun i j => ?_)
  any_goals exact continuous_const
  exact continuous_id.matrix_elem i j

theorem continuous_matStab :
    Continuous (fun p : stabilizer₂ R σ J => matP R σ J p) ∧
      Continuous (fun p : stabilizer₂ R σ J => matP R σ J p⁻¹) :=
  (continuous_HA_iff R σ (hypOne J)).1 continuous_subtype_val

theorem continuous_piR : Continuous (piR R σ J) := by
  rw [continuous_HA_iff]
  exact ⟨continuous_blk.comp (continuous_matStab R σ J).1, continuous_blk.comp (continuous_matStab R σ J).2⟩

theorem continuous_iotaR : Continuous (iotaR R σ J) := by
  refine Continuous.subtype_mk ?_ _
  rw [continuous_HA_iff]
  have h := (continuous_HA_iff R σ J).1 (continuous_id (X := HA R σ J))
  exact ⟨continuous_dg.comp h.1, continuous_dg.comp h.2⟩

end Top

section Unip

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sigR_incl (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem JR_herm (hJ : ∀ i j, σ (J j i) = J i j) (i j : Fin M) :
    sigR R σ (JR R J j i) = JR R J i j := by
  simp only [JR, Matrix.map_apply, sigR_incl, hJ]

variable {R σ J}

def nP (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (w : Fin M → R ⊗[F] E) (z : R ⊗[F] E)
    (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) : stabilizer₂ R σ J :=
  ⟨mkH R σ (hypOne J) (nGL (HaarCoord.sigR_sigR R hσ) w z hz) (by
      have h := (nGL_mem (J := JR R J) (HaarCoord.sigR_sigR R hσ) (JR_herm R σ J hJ) w z hz).1
      rw [← JR_hypOne] at h
      exact h),
    (colE_iff R σ J _).2 (nGL_mem (J := JR R J) (HaarCoord.sigR_sigR R hσ) (JR_herm R σ J hJ) w z hz).2⟩

theorem toMatrix_unipotent (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (w : Fin M → R ⊗[F] E)
    (z : R ⊗[F] E) (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) :
    matP R σ J (nP hσ hJ w z hz) = nM (sigR R σ) (JR R J) w z := rfl

theorem toMatrix_unipotent_inv (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (w : Fin M → R ⊗[F] E)
    (z : R ⊗[F] E) (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) :
    matP R σ J (nP hσ hJ w z hz)⁻¹ = nM (sigR R σ) (JR R J) (-w) (sigR R σ z) := rfl

theorem nP_mem_ker (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (w : Fin M → R ⊗[F] E)
    (z : R ⊗[F] E) (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) :
    nP hσ hJ w z hz ∈ (piR R σ J).ker :=
  MonoidHom.mem_ker.2 (HA_ext R σ J (Units.ext (blk_nM w z)))

theorem nM_form (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {p : stabilizer₂ R σ J}
    (hp : p ∈ (piR R σ J).ker) {w : Fin M → R ⊗[F] E} {z : R ⊗[F] E}
    (e : matP R σ J p = nM (sigR R σ) (JR R J) w z) :
    ∃ hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0, p = nP hσ hJ w z hz := by
  have h := (eq_nM (toMatrix_unitary₂ R σ J p) (toMatrix_col R σ J p) (ker_blk R σ J hp)).2
  rw [e] at h
  exact ⟨h, stabilizer_ext R σ J e⟩

theorem exists_nP (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {p : stabilizer₂ R σ J}
    (hp : p ∈ (piR R σ J).ker) :
    ∃ (w : Fin M → R ⊗[F] E) (z : R ⊗[F] E)
      (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0), p = nP hσ hJ w z hz := by
  obtain ⟨hz, e⟩ := nM_form hσ hJ hp
    (eq_nM (toMatrix_unitary₂ R σ J p) (toMatrix_col R σ J p) (ker_blk R σ J hp)).1
  exact ⟨_, _, hz, e⟩

theorem nP_mem_ratP (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (w : Fin M → E) (z : E)
    (hz : z + σ z + hv (σ : E →+* E) J w w = 0)
    (hz' : inclR R z + sigR R σ (inclR R z) +
      hv (sigR R σ) (JR R J) (fun i => inclR R (w i)) (fun i => inclR R (w i)) = 0) :
    nP hσ hJ (fun i => inclR R (w i)) (inclR R z) hz' ∈ ratP R σ J := by
  refine (mem_HFinIn_iff R σ (hypOne J) _).2
    ⟨nGL (s := (σ : E →+* E)) hσ w z hz,
      (nGL_mem (s := (σ : E →+* E)) hσ hJ w z hz).1, Units.ext ?_⟩
  exact nM_map (inclR R) (fun x => (sigR_incl R σ x).symm) w z

end Unip

section Half

variable {A : Type} [CommRing A] {M : ℕ} {s : A →+* A} {J : Matrix (Fin M) (Fin M) A}

theorem s_hv (hs : ∀ x, s (s x) = x) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin M → A) :
    s (hv s J x y) = hv s J y x := by
  simp only [hv, rowv, map_sum, map_mul, hs, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ]
  ring

theorem z_half (hs : ∀ x, s (s x) = x) (hJ : ∀ i j, s (J j i) = J i j) {half t : A}
    (h2 : half + half = 1) (hh : s half = half) (ht : s t = -t) (w : Fin M → A) :
    (t - half * hv s J w w) + s (t - half * hv s J w w) + hv s J w w = 0 := by
  simp only [map_sub, map_mul, hh, s_hv hs hJ, ht]
  linear_combination (-hv s J w w) * h2

theorem topRow_nM (w v : Fin M → A) (z : A) : topRow (nM s J w z) v = -hv s J w v := by
  simp [topRow, hv]

end Half

section Skew

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] : R ⊗[F] E :=
  inclR R (2⁻¹ : E)

theorem halfR_add [CharZero E] : halfR F E R + halfR F E R = 1 := by
  have h : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [halfR, ← map_add, h, map_one]

theorem sigR_halfR (σ : E →ₐ[F] E) [CharZero E] : sigR R σ (halfR F E R) = halfR F E R := by
  rw [halfR, sigR_incl, map_inv₀, map_ofNat]

theorem exists_coord {σ : E →ₐ[F] E} [CharZero E] (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0)
    (hσδ : σ δ = -δ) (e : E) : ∃ x y : F, x • (1 : E) + y • δ = e := by
  have hind : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rw [Algebra.smul_def, Algebra.smul_def] at hab
    have h1 := congrArg σ hab
    simp only [map_add, map_mul, AlgHom.commutes, map_one, hσδ, map_zero] at h1
    have ha : (2 : E) * algebraMap F E a = 0 := by linear_combination hab + h1
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    have hb : algebraMap F E b * δ = 0 := by simpa using hab
    exact ⟨rfl, by simpa [hδ] using hb⟩
  have hspan := hind.span_eq_top_of_card_eq_finrank (by simp [h2])
  have he : e ∈ Submodule.span F (Set.range ![(1 : E), δ]) := by rw [hspan]; trivial
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union] at he
  exact Submodule.mem_span_pair.1 he

theorem exists_tensor_coord {σ : E →ₐ[F] E} [CharZero E] (h2 : Module.finrank F E = 2) {δ : E}
    (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (t : R ⊗[F] E) :
    ∃ a b : R, t = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] δ := by
  induction t with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r e =>
    obtain ⟨x, y, rfl⟩ := exists_coord h2 hδ hσδ e
    refine ⟨x • r, y • r, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  | add u v hu hv =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a + a', b + b', ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
    abel

theorem eq_tmul_of_skew {σ : E →ₐ[F] E} [CharZero E] (h2 : Module.finrank F E = 2) {δ : E}
    (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {t : R ⊗[F] E} (ht : sigR R σ t = -t) :
    ∃ b : R, t = b ⊗ₜ[F] δ := by
  obtain ⟨a, b, rfl⟩ := exists_tensor_coord R h2 hδ hσδ t
  refine ⟨b, ?_⟩
  rw [map_add, HaarCoord.sigR_tmul, HaarCoord.sigR_tmul, map_one, hσδ, TensorProduct.tmul_neg] at ht
  have h0 : a ⊗ₜ[F] (1 : E) + a ⊗ₜ[F] (1 : E) = 0 := by linear_combination ht
  have h1 : a ⊗ₜ[F] (1 : E) = 0 := by
    have h3 := halfR_add (F := F) (E := E) R
    linear_combination (a ⊗ₜ[F] (1 : E)) * (-h3) + halfR F E R * h0
  rw [h1, zero_add]

end Skew

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct
