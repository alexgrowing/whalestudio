import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas

open MvPolynomial

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  suffices key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from
    fun a s has => key s.val s rfl a has
  intro k
  induction k with
  | zero =>
    intro s hs a ha
    omega
  | succ k ih =>
    intro s hs a ha
    have hk : k < n := by have := s.isLt; omega
    have h1 := h ⟨k, hk⟩ s (by simpa using hs) a
    have h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b < a := (Finset.mem_filter.mp hb).2
      have hba' : b.val < a.val := hba
      exact ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)
    rw [h2, zero_add] at h1
    have h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
      Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)
    omega

theorem lower_triangular_over_field : LowerTriK := by
  intro O K _ _ _ _ _ r n ν Q hQ
  have hlead : ∀ f ∈ dualWeyl K r n ν, f ≠ 0 → LowerTri ((colLex r n).degree f) := fun f hf hf0 =>
    lowerTri_of_interlaced (leadInterlaced K r n ν f hf hf0)
  refine ⟨?_, ?_⟩
  · suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl K r n ν,
        (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → coeff e f ∈ Set.range (algebraMap O K)) →
        (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ (dualWeyl O r n ν).map (toK O K) by
      intro h
      exact key _ Q hQ h rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hco hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      set m := (colLex r n).degree f with hm
      have hint : Interlaced m := leadInterlaced K r n ν f hf hf0
      have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
        colSums K r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨N, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
      obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant K r n N sz hsz I hmono
      have hbO : bideterminant O sz hsz I ∈ dualWeyl O r n ν := by
        have := bidetMem O r n N sz hsz I
        rw [hshape] at this
        exact this
      have hbK : bideterminant K sz hsz I ∈ dualWeyl K r n ν := by
        have := bidetMem K r n N sz hsz I
        rw [hshape] at this
        exact this
      have hmap : toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I :=
        ldlat_map_bidet (algebraMap O K) sz hsz I
      obtain ⟨c, hc⟩ := hco m (lowerTri_of_interlaced hint)
      have hc' : (colLex r n).leadingCoeff f = algebraMap O K c := hc.symm
      have hcb : (colLex r n).leadingCoeff f • bideterminant K sz hsz I = toK O K (c • bideterminant O sz hsz I) := by
        rw [map_smul, hmap, hc', algebraMap_smul]
      have hcbmem : (colLex r n).leadingCoeff f • bideterminant K sz hsz I ∈ (dualWeyl O r n ν).map (toK O K) := by
        rw [hcb]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ hbO)
      set f' := f - (colLex r n).leadingCoeff f • bideterminant K sz hsz I with hf'
      have hf'mem : f' ∈ dualWeyl K r n ν :=
        Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbK)
      have hdecomp : f = f' + (colLex r n).leadingCoeff f • bideterminant K sz hsz I := by
        rw [hf']; abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ hcbmem
      by_cases h0 : f' = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant K sz hsz I) (hbdeg.trans hexp) hblc h0
      refine ih _ (hd ▸ hlt) f' hf'mem ?_ rfl
      intro e he
      obtain ⟨x, hx⟩ := hco e he
      refine ⟨x - coeff e (c • bideterminant O sz hsz I), ?_⟩
      have hce : coeff e (toK O K (c • bideterminant O sz hsz I)) = algebraMap O K (coeff e (c • bideterminant O sz hsz I)) :=
        coeff_map (algebraMap O K) _ e
      rw [hf', coeff_sub, hcb, map_sub, hx, hce]
  · intro h
    by_contra hQ0
    exact ((colLex r n).coeff_degree_ne_zero_iff).mpr hQ0 (h _ (hlead Q hQ hQ0))

end Formalism.L2.G.Model.TS
