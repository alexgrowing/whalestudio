import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockMem

variable {D : D7}

theorem hatId_mul_mem (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ hatId D 𝔪) (hy : y ∈ OhE D) :
    x * y ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => simp [zero_mem]
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def hatIdeal (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Ideal (OhE D) where
  carrier := {x | (x : AE D) ∈ hatId D 𝔪}
  add_mem' := fun {x y} hx hy => by
    show ((x : AE D) + (y : AE D)) ∈ hatId D 𝔪
    exact add_mem hx hy
  zero_mem' := by
    show ((0 : OhE D) : AE D) ∈ hatId D 𝔪
    exact zero_mem _
  smul_mem' := fun c x hx => by
    show (c : AE D) * (x : AE D) ∈ hatId D 𝔪
    rw [mul_comm]; exact hatId_mul_mem 𝔪 hx c.2

def liftM {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    Matrix (Fin d) (Fin d) (OhE D) :=
  Matrix.of fun i j => ⟨g i j, hg i j⟩

theorem liftM_map {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    (liftM g hg).map (OhE D).subtype = g := by
  ext i j; rfl

def blk (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

theorem blk_lt {a d : ℕ} (i j : Fin d) : blk a j < blk a i ↔ j.1 < a ∧ a ≤ i.1 := by
  unfold blk; split_ifs <;> omega

theorem cond_iff {d : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ) (g : Matrix (Fin d) (Fin d) (AE D))
    (hg : ∀ i j, g i j ∈ OhE D) :
    (∀ i j : Fin d, j.1 < a → a ≤ i.1 → g i j ∈ hatId D 𝔪) ↔
      ((liftM g hg).map (Ideal.Quotient.mk (hatIdeal D 𝔪))).BlockTriangular (blk a) := by
  constructor
  · intro h i j hij
    rw [blk_lt] at hij
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h i j hij.1 hij.2
  · intro h i j hj hi
    have := h ((blk_lt i j).2 ⟨hj, hi⟩)
    simp only [Matrix.map_apply] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this

theorem bt_transfer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    {X Y : Matrix (Fin d) (Fin d) R} (h : Y * X = 1) (b : Fin d → ℕ) (hX : (X.map f).BlockTriangular b) :
    (Y.map f).BlockTriangular b := by
  have h' : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ f.map_zero f.map_one]
  letI : Invertible (X.map f) := ⟨Y.map f, h', mul_eq_one_comm.mp h'⟩
  have := Matrix.blockTriangular_inv_of_blockTriangular hX
  rwa [Matrix.inv_eq_left_inv h'] at this

theorem mem_iff (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d) :
    h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  refine ⟨fun hh => ?_, fun hh => Subgroup.subset_closure hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hne : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hne, zero_mem]
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have iy := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · exact hatId_mul_mem 𝔪 (hx.2 i l hl hi) (iy l j).1
    · rw [mul_comm]
      exact hatId_mul_mem 𝔪 (hy.2 l j hj (not_lt.1 hl)) (ix i l).1
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hX : ∀ i j, ((x : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => (ix i j).1
    have hY : ∀ i j, (((x⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => by simpa using (ix i j).2
    rw [cond_iff 𝔪 a _ hY]
    have hXc := (cond_iff 𝔪 a _ hX).1 hx.2
    set X := liftM _ hX
    set Y := liftM _ hY
    have hYX : Y * X = 1 := by
      have key : (Y * X).map (OhE D).subtype = (1 : Matrix (Fin d) (Fin d) (OhE D)).map (OhE D).subtype := by
        rw [Matrix.map_mul, liftM_map, liftM_map, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      exact Matrix.map_injective (fun u v huv => Subtype.ext huv) key
    exact bt_transfer (Ideal.Quotient.mk (hatIdeal D 𝔪)) hYX (blk a) hXc

end GlobalTheory.FunObj.StdDatum.BlockMem

end
