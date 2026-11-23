import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RootSystemLinearProgramCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.LowerSymplecticEntriesEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem vx_nCo_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) (w : ℤ × ℤ) :
    nCo (X.map f) w = f (nCo X w) := by
  unfold nCo
  split_ifs <;> simp

private theorem vx_nCo_tconj {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (w : ℤ × ℤ) :
    nCo (tconj t X) w = (wv t w : R) * nCo X w := by
  unfold nCo
  split_ifs with h1 h2 h3 h4
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl
  · simp

private theorem vx_nCo_mem {R : Type} [CommRing R] (X : M4 R) (w : ℤ × ℤ) (h : nCo X w ≠ 0) : w ∈ nM := by
  unfold nCo at h
  split_ifs at h with h1 h2 h3 h4
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h3]; decide
  · rw [h4]; decide
  · exact absurd rfl h

private theorem vx_nCo_ideal {R : Type} [CommRing R] (I : Ideal R) (X : M4 R)
    (h : ∀ i j, i ≠ j → wt i j ≠ -wPs → X i j ∈ I) (w : ℤ × ℤ) (hw : w ≠ -wPs) : nCo X w ∈ I := by
  unfold nCo
  split_ifs with h1 h2 h3
  · exact h _ _ (by decide) (by decide)
  · exact h _ _ (by decide) (by decide)
  · exact h _ _ (by decide) (by decide)
  · exact I.zero_mem

private theorem vx_res {K : Type} [Field K] (V : ValuationSubring K) (x : V) :
    residue V x ≠ 0 ↔ V.valuation (x : K) = 1 := by
  rw [residue_ne_zero_iff_isUnit, V.valuation_eq_one_iff]

theorem UpperTheory.V.Ws.Lat.vertex :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (P : PD Unit Γ 𝔞.V), 𝔞.Small P → IsLow (P.n ()) →
      (∀ g i j, i ≠ j → P.r g i j ∈ maximalIdeal 𝔞.V) → (∀ i j, i ≠ j → wt i j ≠ -wPs → P.n () i j ∈ maximalIdeal 𝔞.V) → StarE P.r →
      ∃ (t : 𝔞.Kˣ × 𝔞.Kˣ) (P' : PD Unit Γ 𝔞.V), TConj 𝔞.toK t P P' ∧ CompanionTheory (Tight (P'.map (residue 𝔞.V))) := by
  rintro l _ 𝔞 Γ _ _ P ⟨A, _, _, _, f, P₁, hf, -, rfl⟩ hlow hr hn ⟨s1, s2, s3⟩
  have hm : ∀ x : A, f x ∈ maximalIdeal 𝔞.V → x ∈ maximalIdeal A := fun x hx hu => hx (hu.map f)
  have hwt : ∀ i j : Fin 4, i ≠ j ↔ wt i j ∈ roots := by decide
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  let E : ℤ × ℤ → Set A := fun w => {x | ∃ g i j, i ≠ j ∧ wt i j = w ∧ P₁.r g i j = x}
  have hE : ∀ w ∈ roots, Ent (P₁.map f).r w → ∃ x ∈ E w, x ≠ 0 := by
    rintro w hw ⟨g, i, j, e, h⟩
    refine ⟨_, ⟨g, i, j, (hwt i j).2 (e ▸ hw), e, rfl⟩, fun h0 => h ?_⟩
    show f (P₁.r g i j) = 0
    rw [h0, map_zero]
  obtain ⟨t, Si, h1, h2, h3, h4⟩ := h7 𝔞.K 𝔞.V A f hf.inj hf.loc E (nCo (P₁.n ()))
    (by
      rintro w x ⟨g, i, j, hij, -, rfl⟩
      exact hm _ (hr g i j hij))
    (vx_nCo_ideal _ _ fun i j a b => hm _ (hn i j a b))
    (hE _ (by decide) s1) (hE _ (by decide) s2)
    (by
      rcases s3 with s | s | s
      · exact ⟨_, by decide, hE _ (by decide) s⟩
      · exact ⟨_, by decide, hE _ (by decide) s⟩
      · exact ⟨_, by decide, hE _ (by decide) s⟩)
  obtain ⟨P', hP'⟩ := tcEx 𝔞.V t (P₁.map f) (fun _ => hlow)
    (by
      intro g i j
      by_cases hij : i = j
      · subst hij
        rw [hw0]
        simpa [wv] using 𝔞.V.valuation_le_one _
      · exact h1 _ ((hwt i j).1 hij) _ ⟨g, i, j, hij, rfl, rfl⟩)
    (by
      intro v w hw
      rw [PD.map_n, vx_nCo_map]
      exact h2 w hw)
  refine ⟨t, P', hP', ?_⟩
  have er : ∀ g i j, ((P'.r g i j : 𝔞.V) : 𝔞.K) = (wv t (wt i j) : 𝔞.K) * (f (P₁.r g i j) : 𝔞.K) :=
    fun g i j => congrFun (congrFun (hP'.1 g) i) j
  have en : ∀ w, ((nCo (P'.n ()) w : 𝔞.V) : 𝔞.K) = (wv t w : 𝔞.K) * (f (nCo (P₁.n ()) w) : 𝔞.K) := by
    intro w
    have e := congrArg (fun X => nCo X w) (hP'.2 ())
    simp only [vx_nCo_tconj, PD.map_n, vx_nCo_map] at e
    exact e
  have hS : Tight (P'.map (residue 𝔞.V)) = Si := by
    ext w
    rw [h3]
    constructor
    · rintro ⟨hw, ⟨g, i, j, e, h⟩ | ⟨v, h⟩⟩
      · refine .inl ⟨hw, _, ⟨g, i, j, (hwt i j).2 (e ▸ hw), e, rfl⟩, ?_⟩
        rw [← e, ← er]
        exact (vx_res _ _).1 h
      · refine .inr ⟨vx_nCo_mem _ _ h, ?_⟩
        rw [PD.map_n, vx_nCo_map] at h
        rw [← en]
        exact (vx_res _ _).1 h
    · rintro (⟨hw, x, ⟨g, i, j, -, e, rfl⟩, h⟩ | ⟨hw, h⟩)
      · refine ⟨hw, .inl ⟨g, i, j, e, ?_⟩⟩
        rw [← e, ← er] at h
        exact (vx_res _ _).2 h
      · refine ⟨(by decide : nM ⊆ roots) hw, .inr ⟨(), ?_⟩⟩
        rw [PD.map_n, vx_nCo_map]
        rw [← en] at h
        exact (vx_res _ _).2 h
  rw [hS]
  exact h4
