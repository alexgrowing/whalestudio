import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
import Formalism.PolynomialDimension.FinalHar

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem wtPQ_eq (m a b : ℕ) (hm : 1 ≤ m) : wtPQ m a b = letterWt m a true + letterWt m b false := by
  funext i
  have hi := i.isLt
  simp only [wtPQ, letterWt, Pi.add_apply, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem wtPQ_anti (m a b : ℕ) (hm : 1 ≤ m) : Antitone (wtPQ m a b) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [wtPQ, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> omega

theorem nuOf_wtPQ (m a b : ℕ) (hm : 1 ≤ m) :
    nuOf (wtPQ m a b) = nuOf (letterWt m a true) + nuOf (letterWt m b false) := by
  funext t
  have ht := t.isLt
  simp only [nuOf, wtPQ_eq m a b hm, Pi.add_apply, letterWt, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem delta_block (K : Type) [Field K] (m : ℕ) (b : Bool) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (blockEmb K b F) = F := by
  simp [deltaB, blockEmb, rename_rename, Function.comp_def]
  exact rename_id_apply F

theorem delta_prod (K : Type) [Field K] (m : ℕ) (F : Bool → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (∏ b, blockEmb K b (F b)) = F true * F false := by
  rw [map_prod, Fintype.prod_bool, delta_block, delta_block]

theorem mem_invariant_sections_two_weight_iff (hCO : CartanOnto) {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [IsFractionRing O Kf] (m a b : ℕ) (hm : 1 ≤ m) (Λ : Submodule O (Fin (m + 1) → Kf))
    (hΛ : IsLattice O Λ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    y ∈ H0 O m (wtPQ m a b) Λ ↔ ∃ x ∈ twoLat O m a b Λ, deltaB Kf m x = y := by
  have hA : Antitone (letterWt m a true) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    simp only [letterWt, if_true, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hB : Antitone (letterWt m b false) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    simp only [letterWt, Bool.false_eq_true, if_false, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  have key : H0 O m (wtPQ m a b) Λ =
      Submodule.map ((deltaB Kf m).toLinearMap.restrictScalars O) (twoLat O m a b Λ) := by
    rw [wtPQ_eq m a b hm, hCO O Kf m _ _ Λ hΛ hA hB, twoLat, tensorLat, Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨F, hF, G, hG, rfl⟩
      refine ⟨∏ s, blockEmb Kf s (if s = true then F else G), ⟨fun s => if s = true then F else G, ?_, rfl⟩, ?_⟩
      · intro s
        cases s <;> simpa using ‹_›
      · simp [delta_block]
    · rintro ⟨x, ⟨F, hF, rfl⟩, rfl⟩
      refine ⟨F true, by simpa using hF true, F false, by simpa using hF false, ?_⟩
      simp [delta_block]
  rw [key, Submodule.mem_map]
  exact Iff.rfl

theorem delta_twoSp (K : Type) [Field K] (m a b : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ twoSp K m a b, deltaB K m x ∈ dualWeyl K (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  intro x hx
  rw [nuOf_wtPQ m a b hm]
  unfold twoSp tensorLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    rw [delta_prod]
    have h1 := hF true
    have h2 := hF false
    simp only [eq_self_iff_true, if_true, Bool.false_eq_true, if_false] at h1 h2
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul h1 h2
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem hXY_ne_zero (K : Type) [Field K] (k : ℕ) : hXY K (k + 1) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (Sum.elim (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0)
    (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0))) h
  simp [hXY] at this

end Formalism.MainNotions.flipOneThree.Pf

end
