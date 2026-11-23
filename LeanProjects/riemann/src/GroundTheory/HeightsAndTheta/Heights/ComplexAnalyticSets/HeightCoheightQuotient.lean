import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ringKrullDim_quotient_eq_coheight {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]

theorem height_add_ringKrullDim_quotient_le {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩

theorem height_map_add_one_le_of_mem_nonZeroDivisors {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by
  set I := Ideal.span {y} with hI
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm
  rw [hn]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I))
    (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)
  let f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hab ⊢
      exact Ideal.comap_mono hab
    · ext1
      have := congrArg PrimeSpectrum.asIdeal hab
      exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
  let L := l.map f hf
  have hyhead : y ∈ L.head.asIdeal := by
    change y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le
  let p0 : PrimeSpectrum B := ⟨p, hp.1.1⟩
  have hlt : p0 < L.head := by
    refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_
    have hyp : y ∈ p := by
      have : p = L.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [this]
      exact hyhead
    exact Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩
  let L' := L.cons p0 hlt
  have hLlast : L'.last = ⟨P, hP⟩ := by
    simp only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]
    ext1
    exact Ideal.comap_map_mk hIP
  have hlen' : L'.length = n + 1 := by
    simp [L', L, hlen]
  have := Order.length_le_height_last (p := L')
  rw [hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight] at this
  exact_mod_cast this

end GroundTheory.Heights₂.Heights
