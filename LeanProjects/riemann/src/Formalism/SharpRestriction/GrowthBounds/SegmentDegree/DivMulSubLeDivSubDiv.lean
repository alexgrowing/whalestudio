import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem div_mul_sub_le_div_sub_div (n s P Q ee kk rr : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hs : s < kk * P) (he : ee < rr * Q) :
    ((n / (P * Q) : ℕ) : ℤ) - ((kk + rr + 1 : ℕ) : ℤ) ≤ ((((n - s) / P - ee) / Q : ℕ) : ℤ) := by
  have hA : ((n / (P * Q) : ℕ) : ℤ) * ((P : ℤ) * Q) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (P * Q)
  have hU : (((n - s : ℕ)) : ℤ) < (((n - s) / P : ℕ) : ℤ) * P + P := by exact_mod_cast Nat.lt_div_mul_add hP
  have hW : ((((n - s) / P - ee : ℕ)) : ℤ) < ((((n - s) / P - ee) / Q : ℕ) : ℤ) * Q + Q := by
    exact_mod_cast Nat.lt_div_mul_add hQ
  have hns : (n : ℤ) - s ≤ ((n - s : ℕ) : ℤ) := by omega
  have hue : (((n - s) / P : ℕ) : ℤ) - ee ≤ ((((n - s) / P - ee : ℕ)) : ℤ) := by omega
  have hs' : (s : ℤ) < kk * P := by exact_mod_cast hs
  have he' : (ee : ℤ) < rr * Q := by exact_mod_cast he
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  set A : ℤ := ((n / (P * Q) : ℕ) : ℤ)
  set U : ℤ := (((n - s) / P : ℕ) : ℤ)
  set W : ℤ := ((((n - s) / P - ee) / Q : ℕ) : ℤ)
  have st1 : A * Q - kk < U + 1 := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_left hc hP'.le
    nlinarith
  have st2 : A - rr - kk < W + 1 := by
    by_contra hc
    push_neg at hc
    have h1 := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℤ) ≤ Q)
    have hk0 : (0 : ℤ) ≤ kk := by positivity
    have h2 := mul_le_mul_of_nonneg_left hQ' hk0
    nlinarith
  push_cast
  linarith

section Pad

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem eZ_lt_mul_Qc (hX : X.Hyp p K) (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ)
    (he : e ∈ X.EE p K la) (j : ℤ) (i : Fin r) : X.eZ e j i < r * X.Qc p K j := by
  have hV := hX.valid
  have hJ : 0 < X.F.J := hV.1
  unfold Dat.eZ
  rw [dif_pos hJ]
  have hmem := Fintype.mem_piFinset.1
    (Fintype.mem_piFinset.1 he ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ hJ⟩) i
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  have h0 : (0 : ℤ) ≤ j % (X.F.J : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hJ.ne')
  have h1 : j % (X.F.J : ℤ) < X.F.J := Int.emod_lt_of_pos _ (by exact_mod_cast hJ)
  have hv : ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = j % (X.F.J : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hq : X.Qc p K ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = X.Qc p K j := by
    rw [hv]
    have e1 : j % (X.F.J : ℤ) + (j / (X.F.J : ℤ)) * X.F.J = j := by
      exact Int.emod_add_ediv_mul j (X.F.J : ℤ)
    have e2 := sum_Qc_per (p := p) (K := K) X hV (j % (X.F.J : ℤ)) (j / (X.F.J : ℤ))
    rw [e1] at e2
    exact e2.symm
  rw [hq] at hmem
  exact hmem.1

theorem sum_la_lt (hX : X.Hyp p K) (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j x : ℤ)
    (hx : x ∈ X.toLate j) : ∑ c, la (posOf n' x) c < (r + K) * X.Pz p K j x := by
  classical
  have hmem := Fintype.mem_piFinset.1 hla (posOf n' x)
  have hmem2 := Finset.mem_filter.1 hmem
  have hlt := (hmem2.2.2 j x hx rfl).1
  have hne : (Finset.univ : Finset (Fin (r + K))).Nonempty :=
    ⟨⟨0, by have := NeZero.ne r; omega⟩, Finset.mem_univ _⟩
  calc ∑ c, la (posOf n' x) c < ∑ _c : Fin (r + K), X.Pz p K j x :=
        Finset.sum_lt_sum_of_nonempty hne (fun c _ => hlt c)
    _ = (r + K) * X.Pz p K j x := by simp

end Pad

theorem restPad : RestPad 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk la hla e he j
  have hV := hX.valid
  have hp := hX.prime.pos
  have hr : 0 < r := NeZero.pos r
  constructor
  · intro x hx hW
    have hb := mem_letters_bounds hx
    obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV (j - 1) x hb.2.2 hb.1 (r - 1) (Nat.sub_lt hr Nat.one_pos) hW
    have hval : X.bfam p K la e j (X.F.fr (j - 1) i) =
        (X.nz p K la (j - 1) (X.F.fr (j - 1) i) - X.eZ e (j - 1) ⟨i, hi⟩) / X.Qc p K (j - 1) := by
      unfold Dat.bfam
      rw [if_pos hx, if_pos hW, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · rw [if_pos rfl]
      · intro b _ hb'
        rw [if_neg]
        intro heq
        apply hb'
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact absurd heq.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV (j - 1) b.val i h hi))
        · exact absurd heq (ne_of_lt (fr_lt_fr_of_lt_of_valid hV (j - 1) i b.val h b.isLt))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hval]
    have hPQ := sum_PzQc hX (j - 1) _ hW
    rw [sub_add_cancel] at hPQ
    unfold Dat.Bw
    rw [← hPQ]
    unfold Dat.nz
    exact div_mul_sub_le_div_sub_div _ _ _ _ _ (r + K) r (Pz_pos hp _ _) (by unfold Dat.Qc; exact pow_pos hp _)
      (sum_la_lt hX la hla (j - 1) _ (sum_frlate X hV (j - 1) ⟨i, hi⟩)) (eZ_lt_mul_Qc hX la e he (j - 1) ⟨i, hi⟩)
  · intro x hx
    have hl := sum_LLsub X hV j x hx
    obtain ⟨h1, h2, -, -⟩ := sum_late_mem hl.1
    have hval : X.bfam p K la e j x = X.nz p K la j x := by
      unfold Dat.bfam
      rw [if_pos h1, if_neg h2, if_neg (not_le.mpr hl.2)]
    rw [hval]
    exact family_degrees_admissible hr hp (fun j x hx => (sum_LLsub X hV j x hx).1) la hla j x hx

end Formalism.MainNotions.SelectionLemmas.Pf
