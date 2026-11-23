import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem abs_lin_le (a a' u w M : ℤ) (hu : |u| ≤ M) (hw : |w| ≤ M) : |a * u - a' * w| ≤ M * (|a| + |a'|) := by
  calc |a * u - a' * w| ≤ |a * u| + |a' * w| := abs_sub _ _
    _ = |a| * |u| + |a'| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |a'| * M := add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
    _ = M * (|a| + |a'|) := by ring

theorem abs_list_sum_le {α : Type*} (f : α → ℤ) (C : ℤ) :
    ∀ l : List α, (∀ b ∈ l, |f b| ≤ C) → |(l.map f).sum| ≤ l.length * C
  | [], _ => by simp
  | b :: l, h => by
    have h1 := h b (by simp)
    have h2 := abs_list_sum_le f C l fun x hx => h x (by simp [hx])
    rw [List.map_cons, List.sum_cons, List.length_cons]
    calc |f b + (l.map f).sum| ≤ |f b| + |(l.map f).sum| := abs_add_le _ _
      _ ≤ C + l.length * C := add_le_add h1 h2
      _ = ((l.length + 1 : ℕ) : ℤ) * C := by push_cast; ring

theorem abs_auxiliaryVectorUniformizerExponent_le (a a' : ℤ) {n : Type*} (c M : ℕ) (hc : c ≤ M) (y : n ⊕ Fin c) :
    |auxiliaryVectorUniformizerExponent a a' c y| ≤ (M : ℤ) * (|a| + |a'|) := by
  rcases y with x | p
  · simp only [auxiliaryVectorUniformizerExponent, abs_zero]; positivity
  · simp only [auxiliaryVectorUniformizerExponent]
    have hp := p.2
    apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem abs_vtxExp_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (j x : ℕ) (hx : x < G.rank (G.m, j)) :
    |vtxExp a a' (G.m - 1 - j) (topRank G j) x| ≤ (G.m : ℤ) * (|a| + |a'|) := by
  have key := topRank_add hs j
  unfold vtxExp
  split_ifs with h
  · apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  · simp only [abs_zero]; positivity

theorem abs_vtxDet_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (X : ℕ × ℕ) (hX : X.2 ≤ G.m) :
    |vtxDet G a a' X| ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
  unfold vtxDet
  split_ifs with h
  · calc |∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x|
          ≤ ∑ x : Fin (G.rank (G.m, X.2)), |vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin (G.rank (G.m, X.2)), (G.m : ℤ) * (|a| + |a'|) :=
            Finset.sum_le_sum fun x _ => abs_vtxExp_le G hs a a' X.2 x x.2
      _ = (G.rank (G.m, X.2) : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by simp
      _ ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hN _ _ le_rfl hX
  · simp only [abs_zero]; positivity

theorem mem_oppositePath_bound {m : ℕ} {b : Edge} (hb : b ∈ oppositePath m) :
    b.src.1 ≤ m ∧ b.src.2 ≤ m ∧ b.tgt.1 ≤ m ∧ b.tgt.2 ≤ m := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Edge.src, Edge.tgt]; omega
  · simp only [Edge.src, Edge.tgt]; omega

theorem length_oppositePath (m : ℕ) : (oppositePath m).length = 2 * m := by
  simp [oppositePath]; ring

theorem abs_pathSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
      ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) := by
  rw [← length_oppositePath]
  apply abs_list_sum_le
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := mem_oppositePath_bound hb
  have e1 := abs_vtxDet_le G hs a a' N hN b.src h2
  have e2 := abs_vtxDet_le G hs a a' N hN b.tgt h4
  have r1 : ((G.rank b.tgt : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h3 h4
  have r2 : ((G.rank b.src : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h1 h2
  have hC : 0 ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by positivity
  calc |vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src|
        ≤ |vtxDet G a a' b.src * G.rank b.tgt| + |vtxDet G a a' b.tgt * G.rank b.src| := abs_sub _ _
    _ = |vtxDet G a a' b.src| * G.rank b.tgt + |vtxDet G a a' b.tgt| * G.rank b.src := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
    _ ≤ ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N + ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N :=
        add_le_add (mul_le_mul e1 r1 (by positivity) hC) (mul_le_mul e2 r2 (by positivity) hC)
    _ = 2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)))) := by ring

theorem abs_boxExp_le (G : Grid k) (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    |boxExp G a a' j v| ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by
  have hj := j.2
  have e1 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j + 1) G.m (by omega) v.1.2
  have e2 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j) G.m (by omega) v.1.1
  unfold boxExp
  have ha : |a| ≤ |a| + |a'| := le_add_of_nonneg_right (abs_nonneg _)
  calc |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1|
        ≤ |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := abs_add_le _ _
    _ ≤ |a| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := by
        gcongr; exact abs_sub _ _
    _ ≤ (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) := by gcongr
    _ = (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by ring

open Classical in
theorem card_stepVar_le (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (j : Fin (G.m - 1)) :
    Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N * N := by
  have hj := j.2
  have k0 := topRank_add hs j
  have k1 := topRank_add hs ((j : ℕ) + 1)
  have n0 := hN G.m j le_rfl (by omega)
  have n1 := hN G.m (j + 1) le_rfl (by omega)
  refine (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans ?_
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  exact Nat.mul_le_mul (by omega) (by omega)

open Classical in
theorem abs_boxSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |∑ j, ∑ v, boxExp G a a' j v| ≤ ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by
  have hC : 0 ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by positivity
  calc |∑ j, ∑ v, boxExp G a a' j v| ≤ ∑ j, |∑ v, boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (G.m - 1), (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |∑ v, boxExp G a a' j v| ≤ ∑ v, |boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j)),
                (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := Finset.sum_le_sum fun v _ => abs_boxExp_le G a a' j v
          _ = (Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ) *
                ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by simp
          _ ≤ (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
                apply mul_le_mul_of_nonneg_right _ hC
                exact_mod_cast card_stepVar_le G hs N hN j
    _ = ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by simp

theorem abs_expo_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) →
      |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  intro k _ _ _ _ G hs a a' N hN
  classical
  have hP := abs_pathSum_le G hs a a' N hN
  have hB := abs_boxSum_le G hs a a' N hN
  have hpoly : 4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1) ≤ 8 * (G.m : ℤ) ^ 3 := by
    rcases Nat.eq_zero_or_pos G.m with h | h
    · simp [h]
    · have h1 : ((G.m - 1 : ℕ) : ℤ) = (G.m : ℤ) - 1 := by push_cast [Nat.cast_sub h]; ring
      have h2 : (1 : ℤ) ≤ G.m := by exact_mod_cast h
      rw [h1]; nlinarith
  have hT : 0 ≤ (N : ℤ) ^ 2 * (|a| + |a'|) := by positivity
  unfold expo
  calc _ ≤ |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + |2 * ∑ j, ∑ v, boxExp G a a' j v| := abs_sub _ _
    _ = |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + 2 * |∑ j, ∑ v, boxExp G a a' j v| := by rw [abs_mul]; norm_num
    _ ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) +
          2 * (((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)))) := by gcongr
    _ = (4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1)) * ((N : ℤ) ^ 2 * (|a| + |a'|)) := by
          push_cast; ring
    _ ≤ 8 * (G.m : ℤ) ^ 3 * ((N : ℤ) ^ 2 * (|a| + |a'|)) := mul_le_mul_of_nonneg_right hpoly hT
    _ = 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by ring

end GlobalTheory.OriginBox
