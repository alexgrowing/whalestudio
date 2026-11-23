import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDScalLast

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Gen

variable {s r : ℕ}

private theorem gen_wh_of_pos_separated_of_le_deg {N T : ℕ} (deg : Fin N → ℕ) (pos : Fin T → ℕ) (j : Fin T → ℕ) (u : Fin N) (jp : ℕ)
    (w : Fin N → ℕ) (hpos : ∀ i, pos i + 1 < N) (hu : ∀ i, pos i + 1 < (u : ℕ))
    (hdis : ∀ i i', i ≠ i' → pos i ≠ pos i' ∧ pos i ≠ pos i' + 1 ∧ pos i + 1 ≠ pos i')
    (hj : ∀ i, j i ≤ deg ⟨pos i, by have := hpos i; omega⟩ ∧ j i ≤ deg ⟨pos i + 1, hpos i⟩)
    (hjp : jp ≤ deg u) :
    ∑ a, ((deg a - ∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) - if a = u then jp else 0) * w a
      + (∑ i, j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) + jp * w u)
      = ∑ a, deg a * w a := by
  have key : ∀ a : Fin N, (∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0)
      + (if a = u then jp else 0) ≤ deg a := by
    intro a
    by_cases hau : a = u
    · subst hau
      have hn : ∀ i, ¬ ((a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1) := fun i h => by
        have := hu i
        omega
      simp only [hn, if_false, Finset.sum_const_zero, if_true, zero_add]
      exact hjp
    · rw [if_neg hau, add_zero]
      by_cases hex : ∃ i0, (a : ℕ) = pos i0 ∨ (a : ℕ) = pos i0 + 1
      · obtain ⟨i0, h0⟩ := hex
        rw [Finset.sum_eq_single i0]
        · rw [if_pos h0]
          rcases h0 with h0 | h0
          · have h' := (hj i0).1
            have ha : a = ⟨pos i0, by have := hpos i0; omega⟩ := Fin.ext h0
            rw [ha]
            exact h'
          · have h' := (hj i0).2
            have ha : a = ⟨pos i0 + 1, hpos i0⟩ := Fin.ext h0
            rw [ha]
            exact h'
        · intro i _ hi
          rw [if_neg]
          intro h
          have := hdis i i0 hi
          omega
        · intro h
          exact absurd (Finset.mem_univ i0) h
      · push_neg at hex
        rw [Finset.sum_eq_zero]
        · exact Nat.zero_le _
        · intro i _
          rw [if_neg]
          rintro (h | h)
          · exact (hex i).1 h
          · exact (hex i).2 h
  have split : ∀ i, ∑ a : Fin N, (if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) * w a
      = j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) := by
    intro i
    have hs : ∀ a : Fin N, (if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0)
        = (if a = ⟨pos i, by have := hpos i; omega⟩ then j i else 0)
          + (if a = ⟨pos i + 1, hpos i⟩ then j i else 0) := by
      intro a
      by_cases h1 : (a : ℕ) = pos i
      · have h2 : a ≠ ⟨pos i + 1, hpos i⟩ := fun h => by
          rw [h] at h1
          simp at h1
        rw [if_pos (Or.inl h1), if_pos (Fin.ext h1), if_neg h2, add_zero]
      · by_cases h3 : (a : ℕ) = pos i + 1
        · have h2 : a ≠ ⟨pos i, by have := hpos i; omega⟩ := fun h => h1 (by rw [h])
          rw [if_pos (Or.inr h3), if_neg h2, if_pos (Fin.ext h3), zero_add]
        · have h2 : a ≠ ⟨pos i, by have := hpos i; omega⟩ := fun h => h1 (by rw [h])
          have h4 : a ≠ ⟨pos i + 1, hpos i⟩ := fun h => h3 (by rw [h])
          rw [if_neg (by tauto), if_neg h2, if_neg h4, add_zero]
    simp only [hs, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_add]
  have hB : ∑ a : Fin N, (if a = u then jp else 0) * w a = jp * w u := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hA : ∑ a : Fin N, (∑ i, if (a : ℕ) = pos i ∨ (a : ℕ) = pos i + 1 then j i else 0) * w a
      = ∑ i, j i * (w ⟨pos i, by have := hpos i; omega⟩ + w ⟨pos i + 1, hpos i⟩) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => split i)
  rw [← hA, ← hB, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← add_mul, ← add_mul, Nat.sub_sub, Nat.sub_add_cancel (key a)]

theorem gen_wh (O : Type) [CommRing O] [IsDomain O] [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (mm : ℝ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a)
    (h2 : ∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))
    (h3 : ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _))
    (jl : Fin (blockData p S aTop aPlus mm b).T.t → ℕ) (jp : ℕ) (hlev : (blockData p S aTop aPlus mm b).LevelOK jl jp)
    (y : MvPolynomial (Fin (2 * s + 1) × Fin r) (KK O))
    (hy : y ∈ Pol (KK O) r ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg)
    (g : MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t) (KK O))
    (hG : IsWeightedHomogeneous ω g (((blockData p S aTop aPlus mm b).B - jp) * ωL (Fin.last _))) :
    IsWeightedHomogeneous ω
      ((∏ i, (blockData p S aTop aPlus mm b).Ehat O (r := r) i ^ jl i) * (blockData p S aTop aPlus mm b).Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.castSucc i)) ^ (blockData p S aTop aPlus mm b).T.z i) *
      X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.last (blockData p S aTop aPlus mm b).T.t)) ^
        (blockData p S aTop aPlus mm b).zPlus *
      rename (chainEmb (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t) y * g) (OmB p S aTop aPlus b ω ωL) := by
  have hE : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Ehat O (r := r) i)
        (ωL (finPos (2 * s + 1) (2 * (uTop S i : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S i : ℕ) + 1))) := by
    intro i
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ (fun c _ => ?_))
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact h2 i
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact congrArg₂ (· + ·) (h1 _ c) (h1 _ c)
  have hP : IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Eplus O (r := r))
      (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) := by
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ (fun c _ => ?_))
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact h3
    · refine wh_congr ((isWeightedHomogeneous_X (KK O) ω _).mul (isWeightedHomogeneous_X (KK O) ω _)) ?_
      exact congrArg₂ (· + ·) (h1 _ c) (h1 _ c)
  have hEp := IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _ => (hE i).pow (jl i))
  have hZp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => X (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.castSucc i)) ^ (blockData p S aTop aPlus mm b).T.z i)
    _ (fun i _ => (isWeightedHomogeneous_X (KK O) ω _).pow _)
  have hC := wh_chain ω ωL h1 _ y hy
  refine wh_congr ((((((hEp.mul (hP.pow jp)).mul hZp).mul ((isWeightedHomogeneous_X (KK O) ω _).pow _)).mul hC)).mul hG) ?_
  simp only [smul_eq_mul, OmB]
  have hpos : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t, 2 * (uTop S i : ℕ) + 1 < 2 * s + 1 := by
    intro i
    have := (uTop S i).isLt
    omega
  have hu : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      2 * (uTop S i : ℕ) + 1 < ((⟨2 * s, by omega⟩ : Fin (2 * s + 1)) : ℕ) := by
    intro i
    have := (uTop S i).isLt
    show _ < 2 * s
    omega
  have hdis : ∀ i i' : Fin (blockData p S aTop aPlus mm b).T.t, i ≠ i' →
      2 * (uTop S i : ℕ) ≠ 2 * (uTop S i' : ℕ) ∧ 2 * (uTop S i : ℕ) ≠ 2 * (uTop S i' : ℕ) + 1 ∧
        2 * (uTop S i : ℕ) + 1 ≠ 2 * (uTop S i' : ℕ) := by
    intro i i' h
    have hv : (i : ℕ) ≠ i' := fun e => h (Fin.ext e)
    have e1 : (uTop S i : ℕ) = S.sigma + i := rfl
    have e2 : (uTop S i' : ℕ) = S.sigma + i' := rfl
    omega
  have hj : ∀ i : Fin (blockData p S aTop aPlus mm b).T.t,
      jl i ≤ (segChain p S aTop b).deg ⟨2 * (uTop S i : ℕ), by have := hpos i; omega⟩ ∧
        jl i ≤ (segChain p S aTop b).deg ⟨2 * (uTop S i : ℕ) + 1, hpos i⟩ := by
    intro i
    obtain ⟨a1, a2⟩ := hlev.1 i
    have hu' := (uTop S i).isLt
    have e1 : (blockData p S aTop aPlus mm b).letterAt ((blockData p S aTop aPlus mm b).T.pos i)
        = ⟨2 * (uTop S i : ℕ), by omega⟩ :=
      Fin.ext (by show min (2 * (uTop S i : ℕ)) (2 * s + 1 - 1) = 2 * (uTop S i : ℕ); omega)
    have e2 : (blockData p S aTop aPlus mm b).letterAt ((blockData p S aTop aPlus mm b).T.pos i + 1)
        = ⟨2 * (uTop S i : ℕ) + 1, by omega⟩ :=
      Fin.ext (by show min (2 * (uTop S i : ℕ) + 1) (2 * s + 1 - 1) = 2 * (uTop S i : ℕ) + 1; omega)
    rw [e1] at a1
    rw [e2] at a2
    exact ⟨a1, a2⟩
  have hjp : jp ≤ (segChain p S aTop b).deg ⟨2 * s, by omega⟩ := (le_min_iff.mp hlev.2).1
  have hBj : jp ≤ (blockData p S aTop aPlus mm b).B := (le_min_iff.mp hlev.2).2
  have hk := gen_wh_of_pos_separated_of_le_deg (segChain p S aTop b).deg
    (fun l : Fin (blockData p S aTop aPlus mm b).T.t => 2 * (uTop S l : ℕ)) jl ⟨2 * s, by omega⟩ jp
    (fun a => ωL a.castSucc) hpos hu hdis hj hjp
  beta_reduce at hk
  have hf : ∀ k (hk' : k < 2 * s + 1), finPos (2 * s + 1) k = Fin.castSucc ⟨k, hk'⟩ := by
    intro k hk'
    exact Fin.ext (by show min k (2 * s + 1) = k; omega)
  have eE : ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      jl x * (ωL (finPos (2 * s + 1) (2 * ↑(uTop S x))) + ωL (finPos (2 * s + 1) (2 * ↑(uTop S x) + 1)))
      = ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      jl x * (ωL (Fin.castSucc ⟨2 * (uTop S x : ℕ), by have := hpos x; omega⟩)
        + ωL (Fin.castSucc ⟨2 * (uTop S x : ℕ) + 1, hpos x⟩)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hf _ (by have := hpos x; omega), hf _ (hpos x)]
  have eL : ∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL a.castSucc
      = ∑ a : Fin (2 * s + 1), (((segChain p S aTop b).deg a - ∑ i : Fin (blockData p S aTop aPlus mm b).T.t,
        if (a : ℕ) = 2 * (uTop S i : ℕ) ∨ (a : ℕ) = 2 * (uTop S i : ℕ) + 1 then jl i else 0)
        - if a = ⟨2 * s, by omega⟩ then jp else 0) * ωL a.castSucc := rfl
  have eZ : ∑ x : Fin (blockData p S aTop aPlus mm b).T.t,
      (blockData p S aTop aPlus mm b).T.z x * ω (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t x.castSucc)
      = ∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (l.castSucc, false)) := rfl
  have eZl : (blockData p S aTop aPlus mm b).zPlus *
      ω (scalZ (2 * s + 1) r (blockData p S aTop aPlus mm b).T.t (Fin.last (blockData p S aTop aPlus mm b).T.t))
      = (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) := rfl
  have eB : (blockData p S aTop aPlus mm b).B = S.bPlus := rfl
  rw [eE, eZ, eZl, eL, ← hk]
  rw [eB] at hBj
  rw [eB]
  obtain ⟨k, hk2⟩ := Nat.exists_eq_add_of_le hBj
  rw [hk2, Nat.add_sub_cancel_left]
  ring

end Gen

end Formalism.MainNotions.ColumnSystems.Pf
