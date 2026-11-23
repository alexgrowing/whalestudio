import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUnrOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.h1cZero :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → K.Normal → ∀ (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ), (∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) → K ≤ γ.ker → (∀ v ∈ T, ∃ g ∈ Dec (F := ℚ) (pl v), γ g ≠ 1) → Van T pl K γ → (galFrame SP T Q v0 pl K).H1c ρ = ⊥ := by
  intro Ω _ _ _ l SP T Q v0 pl K hD hK k _ M _ _ ρ γ hρ hKγ hT hV
  rw [eq_bot_iff]
  rintro ⟨c, b⟩ ⟨h1, h2, h3, h4, h5⟩
  have h3' : ∀ q : Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → c (toGS Ω SP g) = 0 := by
    intro q g hg hgK
    exact h3 q ⟨g, Ine_le_Dec _ hg⟩ (Subgroup.mem_subgroupOf.2 ⟨hg, hgK⟩)
  have h4' : ∀ v : T, ∀ g ∈ Dec (F := ℚ) (pl v), c (toGS Ω SP g) = (γ g : k) • b v - b v := by
    intro v g hg
    rw [← hρ]
    exact h4 v ⟨g, hg⟩
  have h5' : b v0 = 0 := h5
  obtain ⟨S, e, hS, -, hTp, hQ⟩ := galIdx Ω l v0 hD
  have hcont : Continuous (toGS Ω SP) := continuous_quot_mk
  have hc : ∀ g, c (toGS Ω SP g) = 0 := by
    intro g
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun f => ?_
    have hz : ∀ g h, f (c (toGS Ω SP (g * h))) = f (c (toGS Ω SP g)) + (γ g : k) * f (c (toGS Ω SP h)) := by
      intro g h
      have := h2 (toGS Ω SP g) (toGS Ω SP h)
      simp only at this
      rw [map_mul, this, hρ, map_add, map_smul, smul_eq_mul]
    have hu := unrOf Ω k γ K hKγ SP T (fun s => f (c s)) hz (by
      intro v hv
      obtain ⟨y, hy⟩ := e.surjective ⟨v, by rw [hS] at hv; exact hv⟩
      have hv' : (e y).1 = v := congrArg Subtype.val hy
      rcases y with t | q
      · have h := hTp t ((t.1 : ℕ) : 𝓞 ℚ)
        have e' : algebraMap ℚ Ω (((t.1 : ℕ) : 𝓞 ℚ) : ℚ) = ((t.1 : ℕ) : Ω) := by simp
        rw [e', hv'] at h
        exact Or.inl ⟨t.1, t.2, h.1 (hD.isOver _ (Or.inl t.2))⟩
      · refine Or.inr ⟨pl q, hv' ▸ hQ q, fun g hg hgK => ?_⟩
        simp only [h3' q g hg hgK, map_zero])
    obtain ⟨m, hm⟩ := hV (fun g => f (c (toGS Ω SP g))) ((h1.comp_continuous hcont).comp f) hz hu (by
      intro v hv
      refine ⟨f (b ⟨v, hv⟩), fun g hg => ?_⟩
      simp only [h4' ⟨v, hv⟩ g hg, map_sub, map_smul, smul_eq_mul])
    obtain ⟨g0, hg0, hne⟩ := hT v0 v0.2
    have h0 := hm g0
    simp only [h4' v0 g0 hg0, h5', smul_zero, sub_zero, map_zero] at h0
    have hm0 : m = 0 := by
      have : ((γ g0 : k) - 1) * m = 0 := by rw [sub_mul, one_mul]; exact h0.symm
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
    have := hm g
    simpa [hm0] using this
  refine (Submodule.mem_bot k).2 (Prod.ext (funext fun s => ?_) (funext fun v => ?_))
  · obtain ⟨g, rfl⟩ : ∃ g, toGS Ω SP g = s := QuotientGroup.mk_surjective s
    exact hc g
  · obtain ⟨g0, hg0, hne⟩ := hT v.1 v.2
    have h0 := h4' v g0 hg0
    rw [hc] at h0
    have : ((γ g0 : k) - 1) • b v = 0 := by rw [sub_smul, one_smul]; exact h0.symm
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
