import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagCoef

theorem coef_integral_of_flag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hc : IsFixedConv Λ g F)
    (j : ℕ) (x : S.V) (hx : x ∈ Xflag F j)
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
        ∃ o : 𝓞 E, (s : E) * w c = o := by
  classical
  have hxa : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hxa

  have hxw : x = ∑ i, l i • F.fl.e i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp
  refine ⟨fun c => l c, hxw, ?_, ?_⟩
  · intro c hc
    by_contra h
    have hmem : c.val < j := hl (Finsupp.mem_support_iff.2 h)
    omega
  · intro P hgP c
    have := P.isPrime
    have key : ∀ {L : Submodule (𝓞 E) S.V} {y : S.V},
        y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ u ∈ P.asIdeal.primeCompl, u • y ∈ L := Iff.rfl

    obtain ⟨s, hs, hsx⟩ := key.1 (hP P hgP)
    have hxX : x ∈ Submodule.span E (Set.range F.fl.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hxa
    have hsX : s • x ∈ Formalism.MainNotions.S.Lat.XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨hsx, ?_⟩
      exact Submodule.smul_of_tower_mem _ s hxX

    obtain ⟨cc, -, hc1, heq⟩ := hc.1 P
    have hloc : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ F) :=
      key.2 ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hsX⟩
    have hfun : (fun a => cc a • F.fl.e a) = F.fl.e :=
      funext fun a => by rw [hc1 hgP a, one_smul]
    rw [heq, hfun] at hloc
    obtain ⟨t, ht, htx⟩ := key.1 hloc
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
    have h1 : ∑ i, ((o i : 𝓞 E) : E) • F.fl.e i = t • s • x := by
      rw [← ho]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact algebraMap_smul E (o i) (F.fl.e i)
    have h2 : t • s • x = ∑ i, (((t * s : 𝓞 E) : E) * l i) • F.fl.e i := by
      rw [← mul_smul, ← algebraMap_smul E (t * s) x, hxw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    have hsum : ∑ i, (((o i : 𝓞 E) : E) - ((t * s : 𝓞 E) : E) * l i) • F.fl.e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, ← h2, sub_self]
    have hc0 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum c
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, o c, (sub_eq_zero.1 hc0).symm⟩

end GlobalTheory.FlagCoef
