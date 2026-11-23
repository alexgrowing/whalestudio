import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxu
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]
      exact map_one _
  · intro w
    rw [GlobalTheory.HeckeProduct.localIdele_fst]
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxc
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
