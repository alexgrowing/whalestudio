import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem hatId_mul_of_mem_OhE (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ OhE D)
    (hy : y ∈ hatId D 𝔪) : x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, (OhE D).mul_mem hx hs, by ring⟩
  | zero => simp
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

def blockUpperSub (R : Type) [CommRing R] (N a : ℕ) : Subalgebra R (Matrix (Fin N) (Fin N) R) where
  carrier := {A | ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0}
  mul_mem' {A B} hA hB i j hj hi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [hA i l hl hi, zero_mul]
    · rw [hB l j hj (not_lt.1 hl), mul_zero]
  add_mem' {A B} hA hB i j hj hi := by simp [hA i j hj hi, hB i j hj hi]
  algebraMap_mem' r i j hj hi := by
    have : i ≠ j := fun e => by subst e; omega
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne this]

theorem blockUpper_of_mul_eq_one {R : Type} [CommRing R] {N a : ℕ} {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = 1) (hA : ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0) :
    ∀ i j : Fin N, j.1 < a → a ≤ i.1 → B i j = 0 := by
  have hA' : A ∈ blockUpperSub R N a := hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set p := A.charpoly
  have hq : Polynomial.aeval A p.divX ∈ blockUpperSub R N a :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hA') (Polynomial.aeval_mem_adjoin_singleton R _)
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add p, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have h2 : p.coeff 0 • B = -Polynomial.aeval A p.divX := by
    have := congrArg (fun M => B * M) hCH
    simp only [mul_add, ← mul_assoc, hBA, one_mul, mul_zero, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  have hB : B ∈ blockUpperSub R N a := by
    have hu : ((-1) ^ Fintype.card (Fin N) * B.det) * p.coeff 0 = 1 := by linear_combination hdet
    have : B = ((-1) ^ Fintype.card (Fin N) * B.det) • (p.coeff 0 • B) := by rw [smul_smul, hu, one_smul]
    rw [this, h2]
    exact Subalgebra.smul_mem _ (neg_mem hq) _
  exact hB

def blockLevelSub (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) where
  carrier := blockSet D 𝔪 a N
  one_mem' := by
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hij : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hij]
  mul_mem' {x y} hx hy := by
    have hX := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hY := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [mul_comm]; exact hatId_mul_of_mem_OhE D 𝔪 (hY l j).1 (hx.2 i l hl hi)
    · exact hatId_mul_of_mem_OhE D 𝔪 (hX i l).1 (hy.2 l j hj (not_lt.1 hl))
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, fun i j hj hi => ?_⟩
    have hI := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    let J : Ideal (OhE D) :=
      { carrier := {z | (z : AE D) ∈ hatId D 𝔪}
        add_mem' := fun {u v} hu hv => by simpa using add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun c z hz => by simpa using hatId_mul_of_mem_OhE D 𝔪 c.2 hz }
    let M : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).1⟩
    let M' : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).2⟩
    have hMM : M * M' = 1 := by
      have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) (OhE D) => A.map (OhE D).subtype :=
        fun A B e => by
          ext i j
          exact congrFun (congrFun e i) j
      apply hinj
      change (M * M').map (OhE D).subtype = (1 : Matrix (Fin N) (Fin N) (OhE D)).map (OhE D).subtype
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have e1 : M.map (OhE D).subtype = ((x : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      have e2 : M'.map (OhE D).subtype =
          (((x : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      rw [e1, e2, Units.mul_inv]
    have hred := blockUpper_of_mul_eq_one (a := a) (A := M.map (Ideal.Quotient.mk J))
      (B := M'.map (Ideal.Quotient.mk J))
      (by rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i j hj hi => by
        rw [Matrix.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hx.2 i j hj hi)) i j hj hi
    rw [Matrix.map_apply] at hred
    have hm := Ideal.Quotient.eq_zero_iff_mem.1 hred
    exact hm

theorem blockJ_mem_iff_blockSet : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) (h : GA D N),
    h ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 a N ↔ h ∈ GlobalTheory.BotPairSmall.blockSet D 𝔪 a N := by
  intro D 𝔪 a N h
  constructor
  · intro hh
    exact (Subgroup.closure_le (blockLevelSub D 𝔪 a N)).2 (fun _ hx => hx) hh
  · intro hh
    exact Subgroup.subset_closure hh

end GlobalTheory.BotPairSmall
