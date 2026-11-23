import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj.FlatDep
open GlobalTheory.RootEx

variable {k : Type} [Field k]

theorem stepPt_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) :
    stepPt (x₀ + a₀) u = stepPt x₀ u + fromBlocks a₀ 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> (simp [stepPt, basePt]; try abel)

variable {G : Grid k}

theorem colVar_add (x a : ColArgs G) (u : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) :
    colVar (x + a) u j r = colVar x u j r := by
  simp [colVar, stepPt_add]

theorem rowVar_add (x a : ColArgs G) (u : Vars G) (j : ℕ) (s : Fin (topRank G j)) :
    rowVar (x + a) u j s = rowVar x u j s + if j < G.m - 1 then 0 else a j (topLast G (j + 1)) s := by
  unfold rowVar
  split_ifs with h
  · simp [stepPt_add]
  · simp

theorem ch_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) : ch (stepPt (x₀ + a₀) u) = ch (stepPt x₀ u) := by
  simp [ch, stepPt_add]

theorem phase_add (x a : ColArgs G) (u : Vars G) : phase (x + a) u = phase x u +
    ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0 else
      a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0 := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, ch_add]
  by_cases hE : Even (G.m - 2 - (j : ℕ))
  · simp only [if_pos hE, rowVar_add, colVar_add, add_mul, Finset.sum_add_distrib, add_assoc]
  · simp only [if_neg hE, add_zero]

section Loc
variable [ValuativeRel k] (hs : 1 ≤ G.s)

omit [ValuativeRel k] in
theorem mem_opp_theta {j : ℕ} (hj : j < G.m) : Edge.theta G.m j ∈ oppositePath G.m := by
  simp [oppositePath]; omega

omit [ValuativeRel k] in
theorem mem_opp {b : Edge} (hb : b ∈ oppositePath G.m) :
    (∃ i, i < G.m ∧ b = .ex i G.m) ∨ ∃ j, j < G.m ∧ b = .theta G.m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact .inl ⟨i, hi, rfl⟩
  · exact .inr ⟨j, hj, rfl⟩

omit [ValuativeRel k] in
theorem downMap_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) {j : ℕ} (hj : j < G.m) :
    downMap hs x u j = downMap hs x' u j := by
  unfold downMap; rw [hx j hj]

omit [ValuativeRel k] in
theorem fill_congr {x x' : ColArgs G} {y y' : RowArgs G} (hx : ∀ j, j < G.m → x j = x' j)
    (hy : ∀ i, i < G.m → y i = y' i) (u : Vars G) {b : Edge} (hb : b ∈ oppositePath G.m) :
    fill hs x y u b = fill hs x' y' u b := by
  rcases mem_opp hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [fill_ex, fill_ex, hy i hi]
  · rw [fill_theta, fill_theta, downMap_congr hs hx u hj]

omit [ValuativeRel k] in
theorem phase_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) :
    phase x u = phase x' u := by
  unfold phase colVar rowVar
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := hx j (by have := j.2; omega)
  have h2 := hx (j + 1) (by have := j.2; omega)
  rw [h1, h2]

theorem fromBlocks_le {n n' m m' : Type*} {A : Matrix n n' k} {t : ValueGroupWithZero k}
    (hA : ∀ r s, valuation k (A r s) ≤ t) (r : n ⊕ m) (s : n' ⊕ m') :
    valuation k (fromBlocks A 0 0 (0 : Matrix m m' k) r s) ≤ t := by
  rcases r with r | r <;> rcases s with s | s <;> simp [hA]

theorem fill_sub_le {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((fill hs (x + a) (y + b) u - fill hs x y u) c r s) ≤ t := by
  rcases mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Pi.sub_apply, fill_ex, Matrix.sub_apply, transpose_apply, Pi.add_apply, Matrix.add_apply,
      add_sub_cancel_left]
    exact hb i hi s r
  · simp only [Pi.sub_apply, fill_theta, Matrix.sub_apply, transpose_apply]
    unfold downMap
    split_ifs with h h'
    · simp only [reindex_apply, submatrix_apply, Pi.add_apply, stepPt_add, Matrix.add_apply, add_sub_cancel_left]
      exact fromBlocks_le (ha j hj) _ _
    · simp only [submatrix_apply, Pi.add_apply, Matrix.add_apply, add_sub_cancel_left]
      exact ha j hj _ _
    · simp

omit [ValuativeRel k] in
theorem exists_colVar_eq (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j : Fin (G.m - 1))
    (r : Fin (topRank G (j + 1))) : ∃ p q, colVar x u j r = fill hs x y u (.theta G.m j) p q := by
  refine ⟨frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega)
      (.inr ⟨(G.m - 2 - j) / 2, by omega⟩),
    frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) (.inl r), ?_⟩
  rw [fill_theta, transpose_apply, downMap, dif_pos j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, colVar, Fin.eta]

end Loc
end GlobalTheory.FunObj.FlatDep

open GlobalTheory.FunObj.FlatDep in
theorem GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hψ hT
  obtain ⟨n, hA, hB⟩ := GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant G ϖ e T keep g hϖ hT
  refine ⟨fun x x' y y' hx hy => ?_, n, fun x a y b ha hb => ?_⟩
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    rw [phase_congr hx u]
    have hTe : T (G.moveArgs .one g (fill hs x y u)) = T (G.moveArgs .one g (fill hs x' y' u)) :=
      hT.1 fun c hc => by simp only [Grid.moveArgs, fill_congr hs hx hy u hc]
    simp only [moved, Grid.pathAct, hTe]
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    have hS : moved G keep g T (fill hs (x + a) (y + b) u) = moved G keep g T (fill hs x y u) := by
      have h := hB (fill hs x y u) (fill hs (x + a) (y + b) u - fill hs x y u)
        fun c hc r s => fill_sub_le hs ha hb u hc r s
      rwa [add_sub_cancel] at h
    rw [hS]
    by_cases h0 : moved G keep g T (fill hs x y u) = 0
    · simp [h0]
    have hbd := hA _ h0
    have hD : ∀ (j : Fin (G.m - 1)) r, valuation k ((if (j : ℕ) + 1 < G.m - 1 then 0 else
        a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r) ≤ 1 := by
      intro j r
      have := j.2
      split_ifs with h
      · simp
      · obtain ⟨p, q, hpq⟩ := exists_colVar_eq hs x y u j r
        rw [map_mul, hpq]
        calc _ ≤ valuation k ((ϖ ^ n : kˣ) : k) * valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) :=
              mul_le_mul' (ha _ (by omega) _ _) (hbd _ (mem_opp_theta (by omega)) _ _)
          _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hsum : valuation k (-(∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0
        else a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0)) ≤ valuation k ((1 : kˣ) : k) := by
      rw [Valuation.map_neg, Units.val_one, map_one]
      refine (valuation k).map_sum_le fun j _ => ?_
      by_cases hE : Even (G.m - 2 - (j : ℕ))
      · rw [if_pos hE]; exact (valuation k).map_sum_le fun r _ => hD j r
      · rw [if_neg hE, map_zero]; exact zero_le'
    rw [phase_add, neg_add, AddChar.map_add_eq_mul, (hψ 1).2 le_rfl _ hsum, mul_one]
