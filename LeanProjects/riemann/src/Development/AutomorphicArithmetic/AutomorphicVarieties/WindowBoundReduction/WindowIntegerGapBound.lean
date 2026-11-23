import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

private theorem lift_int (c : ℂ) (m : Multiset ℂ) (h : ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + c) :
    ∃ m' : Multiset ℤ, m = m'.map (fun n : ℤ => (n : ℂ) + c) := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons z m ih =>
    obtain ⟨m', rfl⟩ := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    obtain ⟨n, rfl⟩ := h z (Multiset.mem_cons_self _ _)
    exact ⟨n ::ₘ m', by simp⟩

private theorem gap {a : ℕ} (e : Fin a → ℤ) (he : StrictMono e) (i : Fin a) :
    ∀ (d : ℕ) (j : Fin a), (j : ℕ) = i + d → e i + d ≤ e j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have : j = i := Fin.ext (by simpa using hj)
    subst this; simp
  | succ d ih =>
    intro j hj
    have hlt : (i : ℕ) + d < a := by have := j.2; omega
    have h1 := ih ⟨i + d, hlt⟩ rfl
    have h2 : e ⟨i + d, hlt⟩ < e j := he (by rw [Fin.lt_def]; simp only; omega)
    push_cast; omega

theorem UpperTheory.window_integer_gap_bound :
    ∀ (a : ℕ) (m : Multiset ℂ), IsRegInt a m → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ ν : Fin a → ℕ, Antitone ν ∧ ∀ u : ℂ, ∏ k : Fin a, (u + ((a : ℂ) - 1) / 2 - (N : ℂ) - (k : ℂ) + (ν k : ℂ)) = ((m.map Neg.neg).map (u + ·)).prod := by
  rintro a m ⟨hc, hn, hz⟩
  obtain ⟨m', rfl⟩ := lift_int _ m hz
  have hn' : m'.Nodup := Multiset.Nodup.of_map _ hn
  let s : Finset ℤ := ⟨m', hn'⟩
  have hs : s.card = a := by simpa [s, Finset.card] using hc
  let e := s.orderEmbOfFin hs
  have hm : m' = (Finset.univ : Finset (Fin a)).val.map e := by
    have := congrArg Finset.val (Finset.map_orderEmbOfFin_univ s hs)
    rw [Finset.map_val] at this
    exact this.symm
  refine ⟨a + ∑ k : Fin a, (e k).toNat, fun N hN => ?_⟩
  have hpos : ∀ k : Fin a, 0 ≤ (N : ℤ) + k + 1 - a - e k := by
    intro k
    have := Finset.single_le_sum (f := fun k : Fin a => (e k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  refine ⟨fun k => ((N : ℤ) + k + 1 - a - e k).toNat, ?_, fun u => ?_⟩
  · intro i j hij
    have h1 := gap e e.strictMono i (j - i) j (by have : (i : ℕ) ≤ j := hij; omega)
    have : (i : ℕ) ≤ j := hij
    simp only
    omega
  · rw [hm, Multiset.map_map, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun k _ => ?_
    have h : ((((N : ℤ) + k + 1 - a - e k).toNat : ℕ) : ℂ) = (N : ℂ) + (k : ℕ) + 1 - a - (e k : ℤ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hpos k)]
      push_cast; ring
    simp only [Function.comp, h]
    ring
