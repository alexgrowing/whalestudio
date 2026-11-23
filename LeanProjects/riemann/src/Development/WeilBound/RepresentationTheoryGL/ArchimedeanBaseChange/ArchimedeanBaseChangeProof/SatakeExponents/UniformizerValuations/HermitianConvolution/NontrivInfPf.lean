import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf

noncomputable section

open NumberField IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra

namespace PositivityTheory.Rg.BcB.F.FBL.NontrivInfPf

lemma finrank_real_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (h : Subsingleton (InfinitePlace E)) :
    Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have hc : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 h) Fintype.card_pos
  rw [← IsCMField.card_infinitePlace_eq_card_infinitePlace] at hc
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (maximalRealSubfield E)
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank (maximalRealSubfield E)
  have h3 := IsTotallyReal.nrComplexPlaces_eq_zero (maximalRealSubfield E)
  omega

lemma surj_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  have hbot : (⊤ : Subalgebra ℚ F) = ⊥ :=
    Subalgebra.finrank_eq_one_iff.1 (by rw [Subalgebra.topEquiv.toLinearEquiv.finrank_eq]; exact h)
  have hx : (x : F) ∈ (⊥ : Subalgebra ℚ F) := hbot ▸ Algebra.mem_top
  obtain ⟨q, hq⟩ := Algebra.mem_bot.1 hx
  have hint : IsIntegral ℤ q := by
    have : IsIntegral ℤ (x : F) := x.isIntegral_coe
    rwa [← hq, isIntegral_algebraMap_iff (algebraMap ℚ F).injective] at this
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, ?_⟩
  apply RingOfIntegers.ext
  rw [← hq, ← hn]
  simp

lemma fu_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    Algebra.FormallyUnramified ℤ (𝓞 F) :=
  Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 F)) (surj_of_finrank_one F h)

theorem main (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hF := finrank_real_eq_one E hnt
  have : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) := fu_of_finrank_one _ hF
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt ℤ w.asIdeal := fun w => by
    have := hU w
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime w.asIdeal)
  have htop : differentIdeal ℤ (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hPne : P ≠ ⊥ := fun h => differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (eq_bot_iff.2 (h ▸ hle))
    let w : HeightOneSpectrum (𝓞 E) := ⟨P, hPmax.isPrime, hPne⟩
    have := (not_dvd_differentIdeal_iff (A := ℤ) (P := w.asIdeal)).2 (hunr w)
    exact this (Ideal.dvd_iff_le.2 hle)
  have hd := absNorm_differentIdeal E (𝓞 E)
  rw [htop, Ideal.absNorm_top] at hd
  have hrank : 1 < Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    have h4 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
    omega
  have h2 := abs_discr_gt_two hrank
  have h1 : |discr E| = 1 := by rw [Int.abs_eq_natAbs, ← hd]; rfl
  omega

end PositivityTheory.Rg.BcB.F.FBL.NontrivInfPf

namespace PositivityTheory.Rg.BcB.F.FBL

theorem nontrivInf : NontrivInf := fun E _ _ _ hU => NontrivInfPf.main E hU

end PositivityTheory.Rg.BcB.F.FBL

end
