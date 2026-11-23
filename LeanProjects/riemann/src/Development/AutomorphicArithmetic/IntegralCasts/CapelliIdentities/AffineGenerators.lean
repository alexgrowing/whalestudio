import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem mem_spanOver_of_mem_span {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (S : Set E) {v : E}
    (hv : v ∈ Submodule.span R S) : v ∈ spanOver R S := by
  obtain ⟨m, a, g, rfl⟩ := Submodule.mem_span_set'.1 hv
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨(a i : Ω), (a i).2, (g i : E), (g i).2, rfl⟩

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem exists_finset_span_of_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (N : ℕ) (L : AddSubgroup E)
    (h : LocFree R N L) :
    ∃ T : Finset E, (∀ t ∈ T, t ∈ L) ∧ ∀ e ∈ L, e ∈ Submodule.span R (T : Set E) := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := h
  choose b _ _ hb using hb
  have hgen : ∀ l q, ∃ m : ℕ, f l ^ m • b l q ∈ L := by
    intro l q
    refine (hb l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hq] using R.zero_mem
    · simp [Pi.single_apply]
  choose m hm using hgen
  refine ⟨Finset.univ.image fun x : Fin k × Fin N => f x.1 ^ m x.1 x.2 • b x.1 x.2, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    exact hm x.1 x.2
  · intro e he
    let f' : Fin k → R := fun l => ⟨f l, hf l⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f') ?_ e ?_
    · rw [Ideal.eq_top_iff_one]
      have h1 : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * f' l := by
        apply Subtype.ext
        simpa [f'] using hsum.symm
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
    · rintro ⟨_, l, rfl⟩
      obtain ⟨a, ha, hea⟩ := (hb l e).1 ⟨0, by simpa using he⟩
      choose j hj using ha
      refine ⟨∑ q, (j q + m l q), ?_⟩
      rw [hea, Finset.smul_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      have hle : j q + m l q ≤ ∑ q, (j q + m l q) :=
        Finset.single_le_sum (f := fun q => j q + m l q) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ q)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have heq : (f' l ^ (∑ q, (j q + m l q))) • a q • b l q =
          (f' l ^ d * (⟨f l ^ j q * a q, hj q⟩ : R)) • (f l ^ m l q • b l q) := by
        rw [hd]
        change (f l ^ (j q + m l q + d)) • a q • b l q =
          (f l ^ d * (f l ^ j q * a q)) • (f l ^ m l q • b l q)
        rw [smul_smul, smul_smul]
        congr 1
        ring
      change (f' l ^ (∑ q, (j q + m l q))) • a q • b l q ∈ _
      rw [heq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(l, q), Finset.mem_univ _, rfl⟩)

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem linMap_injective {Ω : Type} [Field Ω] {F : Type} [Zero F] [One F] (n : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : LinearMap.ker (linMap n χ) = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro l hl
  funext i
  have h := congrFun hl (Pi.single i 1)
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [h1] using h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, h0]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem UpperTheory.Reformulated.B.AffineGenerators.af_gens :
    ∀ {o Ω : Type} [inst : CommRing o] [inst_1 : Field Ω] [inst_2 : Algebra o Ω] {F : Type} [inst_3 : Zero F]
      [inst_4 : One F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : GlobalTheory.CompanionTheory.Ar.Num.LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
      (p N : ℕ) (χ : F → Ω),
      χ (0 : F) = (0 : Ω) →
        χ (1 : F) = (1 : Ω) →
          GlobalTheory.CompanionTheory.Ar.Num.LocFree R N (D.l1 R p) →
            GlobalTheory.CompanionTheory.Ar.Num.Summand (D.l1 R p) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ).range →
              ∃ (S : Finset (Fin n → Ω)),
                (↑S : Set (Fin n → Ω)) ⊆ (↑(D.af R p χ) : Set (Fin n → Ω)) ∧
                  D.af R p χ ≤ GlobalTheory.CompanionTheory.Ar.Num.spanOver R (↑S : Set (Fin n → Ω)) := by
  intro o Ω _ _ _ F _ _ n Sg r s D R p N χ h0 h1 hfree hsum
  classical
  obtain ⟨T, hT, hspan⟩ := exists_finset_span_of_locFree R N _ hfree
  obtain ⟨ρ, hρU, hρid, hρL⟩ := hsum
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (linMap_injective n χ h0 h1)
  have hg' : ∀ l, g (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := fun l => LinearMap.congr_fun hg l
  refine ⟨T.image fun t => g (ρ t), ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
    obtain ⟨l, hl⟩ := hρU t
    change GlobalTheory.CompanionTheory.Ar.Num.linMap n χ (g (ρ t)) ∈ D.l1 R p
    rw [← hl, hg', hl]
    exact hρL t (hT t ht)
  · intro l hl
    have hl' : GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l ∈ D.l1 R p := hl
    have hmem := Submodule.apply_mem_span_image_of_mem_span
      ((g ∘ₗ ρ).restrictScalars R) (hspan _ hl')
    apply mem_spanOver_of_mem_span
    rw [Finset.coe_image]
    have heq : ((g ∘ₗ ρ).restrictScalars R) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := by
      change g (ρ (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l)) = l
      rw [hρid _ ⟨l, rfl⟩, hg']
    rw [heq] at hmem
    exact hmem
