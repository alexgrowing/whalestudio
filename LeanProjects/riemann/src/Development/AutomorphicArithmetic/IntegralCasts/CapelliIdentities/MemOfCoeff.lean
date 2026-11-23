import Mathlib

namespace UpperTheory.Reformulated.B.S1

theorem mem_of_coeff {O σ ι : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O)) (e : ι → σ) (s : Finset ι)
    (hs : ∀ i ∈ s, MvPowerSeries.X (e i) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) : f ∈ I := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact I.zero_mem
  | insert a s _ ih =>
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have hgI : g ∈ I := by
      refine ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) g ?_
      intro n hn
      rw [hg]
      split_ifs with h
      · refine hf n ?_
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have hd : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have hfg : f - g ∈ I :=
      Ideal.mem_of_dvd I hd (hs a (Finset.mem_insert_self a s))
    simpa using I.add_mem hfg hgI

end UpperTheory.Reformulated.B.S1
