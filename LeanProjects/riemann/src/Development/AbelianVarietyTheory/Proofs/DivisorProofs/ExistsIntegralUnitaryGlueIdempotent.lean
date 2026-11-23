import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.GlueUnitary

theorem tri_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (e1 e2 e3 : R) (h12 : e1 * e2 = 0) (h13 : e1 * e3 = 0) (h23 : e2 * e3 = 0)
    (A B C A' B' C' : Matrix n n R) :
    (e1 • A + e2 • B + e3 • C) * (e1 • A' + e2 • B' + e3 • C') =
      (e1 * e1) • (A * A') + (e2 * e2) • (B * B') + (e3 * e3) • (C * C') := by
  have h21 : e2 * e1 = 0 := by rw [mul_comm]; exact h12
  have h31 : e3 * e1 = 0 := by rw [mul_comm]; exact h13
  have h32 : e3 * e2 = 0 := by rw [mul_comm]; exact h23
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h12, h13, h23, h21, h31, h32,
    zero_smul, add_zero, zero_add]

theorem st_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] (s : R →+* R) (A B : Matrix n n R) :
    ((A * B).map s).transpose = (B.map s).transpose * (A.map s).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem st_smul {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (c : R) (A : Matrix n n R) :
    ((c • A).map s).transpose = s c • (A.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply]

theorem st_add {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (A B : Matrix n n R) :
    ((A + B).map s).transpose = (A.map s).transpose + (B.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

theorem st_one {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] (s : R →+* R) :
    (((1 : Matrix n n R)).map s).transpose = 1 := by
  ext i j; by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem st_st {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (hs : ∀ y, s (s y) = y)
    (A : Matrix n n R) : ((((A.map s).transpose).map s).transpose) = A := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, hs]

end GlobalTheory.GlueUnitary

namespace GlobalTheory.GlueUnitary

theorem key_alg {R : Type*} [CommRing R] (z p d f fb g : R) (hg : g = 1 - f - fb) (h : fb * f = 0) :
    z - (f * z + fb * p + g * d) = (z - fb * p - (1 - fb) * d) * (1 - f) := by
  subst hg; linear_combination (d - p) * h

theorem glue_unitary : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 a Z f w hf hw hff hffb hfdet h1f
  set s := sgA D with hs
  have hss : ∀ y, s (s y) = y := VacMove.sgA_sgA D
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  have hφapp : ∀ z : 𝓞 D.host.E, φ z = inc D (z : D.host.E) := fun z => rfl
  have hφint : ∀ z : 𝓞 D.host.E, φ z ∈ OhE D := fun z => VacMove.inc_int D z
  set fb := s f with hfb
  set g := 1 - f - fb with hg
  have hfbf : fb * f = 0 := by rw [mul_comm]; exact hffb
  have hfbfb : fb * fb = fb := by rw [hfb, ← map_mul, hff]
  have hfg : f * g = 0 := by rw [hg]; linear_combination -hff - hffb
  have hfbg : fb * g = 0 := by rw [hg]; linear_combination -hfbf - hfbfb
  have hgg : g * g = g := by rw [hg]; linear_combination hff + hfbfb + 2 * hffb
  have hsg : s g = g := by rw [hg, map_sub, map_sub, map_one, hss]; ring
  have hfO : fb ∈ OhE D := VacMove.sgA_mem D hf
  have hgO : g ∈ OhE D := by
    rw [hg]; exact sub_mem (sub_mem (one_mem _) hf) hfO
  let st : Matrix (Fin a) (Fin a) (AE D) → Matrix (Fin a) (Fin a) (AE D) := fun M => (M.map s).transpose
  let Zi : Matrix (Fin a) (Fin a) (AE D) := Z.map φ
  let P : Matrix (Fin a) (Fin a) (AE D) := w • Z.adjugate.map φ
  have hZP : Zi * P = f • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    simp only [Zi, P, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
    rw [hfdet]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.smul_apply, hφapp, mul_comm]
    · simp [Matrix.smul_apply, Matrix.one_apply, h]
  let X : Matrix (Fin a) (Fin a) (AE D) := f • Zi + fb • st P + g • 1
  let X' : Matrix (Fin a) (Fin a) (AE D) := f • P + fb • st Zi + g • 1
  have hXX' : X * X' = 1 := by
    simp only [X, X']
    rw [tri_mul f fb g hffb hfg hfbg, ← st_mul s Zi P, hZP]
    simp only [st, st_smul, st_one, hff, hfbfb, hgg, Matrix.mul_one, smul_smul]
    rw [← hfb, hfbfb, ← add_smul, ← add_smul, hg]; simp
  have hstX' : st X' = X := by
    simp only [X, X', st, st_add, st_smul, st_one, hsg]
    rw [← hfb, hss, st_st s hss]
    abel
  have hX'X : X' * X = 1 := mul_eq_one_comm.mp hXX'
  let u : GL (Fin a) (AE D) := ⟨X', X, hX'X, hXX'⟩
  have huGA : u ∈ GA D a := by
    rw [PtsMem.mem_GA]
    change st X' * X' = 1
    rw [hstX', hXX']
  let k : GA D a := ⟨u, huGA⟩
  have hkinv : (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = X := rfl
  have hentO : ∀ (M : Matrix (Fin a) (Fin a) (AE D)), (∀ i j, M i j ∈ OhE D) → ∀ i j, st M i j ∈ OhE D := by
    intro M hM i j; exact VacMove.sgA_mem D (hM j i)
  have hZiO : ∀ i j, Zi i j ∈ OhE D := fun i j => hφint _
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => mul_mem hw (hφint _)
  have h1O : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
    intro i j; by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Matrix.one_apply, h, zero_mem]
  have hXO : ∀ i j, X i j ∈ OhE D := by
    intro i j
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hZiO i j)) (mul_mem hfO (hentO P hPO i j))) (mul_mem hgO (h1O i j))
  have hX'O : ∀ i j, X' i j ∈ OhE D := by
    intro i j
    simp only [X', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hPO i j)) (mul_mem hfO (hentO Zi hZiO i j))) (mul_mem hgO (h1O i j))
  refine ⟨k, ?_, ?_⟩
  · rw [mem_intG]
    intro i j
    exact ⟨hX'O i j, hXO i j⟩
  · intro i l
    rw [hkinv]
    have hZ : Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) = Zi := rfl
    rw [hZ]
    rw [Matrix.sub_apply]
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [key_alg (Zi i l) (st P i l) ((1 : Matrix (Fin a) (Fin a) (AE D)) i l) f fb g hg hfbf]
    refine GlobalTheory.CongIdx.mul_mem_hatId ?_ h1f
    exact sub_mem (sub_mem (hZiO i l) (mul_mem hfO (hentO P hPO i l))) (mul_mem (sub_mem (one_mem _) hfO) (h1O i l))

end GlobalTheory.GlueUnitary
