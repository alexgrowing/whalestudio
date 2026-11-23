import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_norm_sub_one_le (l : ℕ) [Fact l.Prime] (a : ℕ) (x : ℤ_[l]ˣ) :
    x ∈ KStar.TotallyRealRoots.princ l a ↔ ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ)) := by
  have h : x ∈ KStar.TotallyRealRoots.princ l a ↔ PadicInt.toZModPow a (x : ℤ_[l]) = 1 := by
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  rw [h, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]

private theorem princ_isClosed (l : ℕ) [Fact l.Prime] (a : ℕ) :
    IsClosed ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
  have e : ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) =
      {x : ℤ_[l]ˣ | ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ))} := by
    ext x
    exact mem_princ_iff_norm_sub_one_le l a x
  rw [e]
  exact isClosed_le (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

private theorem princ_antitone (l : ℕ) [Fact l.Prime] {a b : ℕ} (hab : a ≤ b) (x : ℤ_[l]ˣ)
    (hx : x ∈ KStar.TotallyRealRoots.princ l b) : x ∈ KStar.TotallyRealRoots.princ l a := by
  rw [mem_princ_iff_norm_sub_one_le] at hx ⊢
  refine hx.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

private theorem eq_one_of_mem_all_princ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]ˣ)
    (hx : ∀ a, x ∈ KStar.TotallyRealRoots.princ l a) : x = 1 := by
  ext
  refine PadicInt.ext_of_toZModPow.mp fun a => ?_
  have h := hx a
  simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff] at h
  simpa using h

theorem UpperTheory.V.Kum.levCompact :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (n : ℕ) (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [Zero M] (ψ : T × levU l U n → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant ψ →
    (∀ t (u : levU l U n), u.1 ∈ cycU l U → ψ (t, u) = 0) → ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), u.1 ∈ levU l U m → ψ (t, u) = 0 := by
  intro F Ω _ _ _ _ _ l _ U n T _ _ M _ ψ hU hψ h0
  have memL : ∀ (m : ℕ) (x : G F Ω), x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    simp [UpperTheory.V.Base.levU, Subgroup.mem_inf, Subgroup.mem_comap]
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    simp [UpperTheory.V.Base.cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
  have closedL : ∀ m : ℕ, IsClosed ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro m
    have e : ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) =
        (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' ((KStar.TotallyRealRoots.princ l m : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
      ext x
      exact memL m x
    rw [e]
    exact hU.inter ((princ_isClosed l m).preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (levU l U n) := isCompact_iff_compactSpace.mp (closedL n).isCompact
  let K : Set (T × levU l U n) := {p | ψ p ≠ 0}
  have hKc : IsClosed K := by
    have ho : IsOpen (ψ ⁻¹' {0}) := hψ.isOpen_fiber 0
    exact ho.isClosed_compl
  let t : ℕ → Set (T × levU l U n) := fun m => {p | (p.2 : G F Ω) ∈ levU l U m}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (closedL m).preimage (continuous_subtype_val.comp continuous_snd)
  have hst : K ∩ ⋂ m, t m = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hall
    apply hp
    obtain ⟨s, u⟩ := p
    apply h0 s u
    rw [memC]
    refine ⟨((memL n u.1).1 u.2).1, eq_one_of_mem_all_princ l _ fun a => ((memL a u.1).1 (hall a)).2⟩
  obtain ⟨v, hv⟩ := hKc.isCompact.elim_finite_subfamily_closed t htc hst
  refine ⟨max n (v.sup id), le_max_left _ _, ?_⟩
  intro s u hu
  by_contra hne
  have hmem : (s, u) ∈ K ∩ ⋂ i ∈ v, t i := by
    refine ⟨hne, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    show (u : G F Ω) ∈ levU l U i
    rw [memL] at hu ⊢
    refine ⟨hu.1, princ_antitone l ?_ _ hu.2⟩
    exact (Finset.le_sup (f := id) hi).trans (le_max_right _ _)
  rw [hv] at hmem
  exact hmem
