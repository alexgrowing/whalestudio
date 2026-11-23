import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.VanishCyc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ext_of_prod {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (C U : Subgroup Γ) [hN : U.Normal] (hC : IsClosed (C : Set Γ))
    (hU : IsClosed (U : Set Γ)) (hCU : ∀ g : Γ, ∃ p : C × U, p.1.1 * p.2.1 = g) (φ : U → M) (hρ : ContAction ρ)
    (htr : ∀ u ∈ U, ∀ m, ρ u m = m) (hφ : Continuous φ) (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (heq : ∀ (g : Γ) (u u' : U), u'.1 * g = g * u.1 → φ u' = ρ g (φ u)) (hv : ∀ x : U, x.1 ∈ C → φ x = 0) :
    ∃ z ∈ Z1 ρ, ∀ u : U, z u.1 = φ u := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : C × U → Γ, ∀ p, f p = p.1.1 * p.2.1 := ⟨_, fun _ => rfl⟩
  have hwd : ∀ p q : C × U, f p = f q → ρ p.1.1 (φ p.2) = ρ q.1.1 (φ q.2) := by
    rintro ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ ⟨⟨c', hc'⟩, ⟨u', hu'⟩⟩ h
    rw [hf, hf] at h
    change c * u = c' * u' at h
    change ρ c (φ ⟨u, hu⟩) = ρ c' (φ ⟨u', hu'⟩)
    have hw1 : c'⁻¹ * c = u' * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hwC : c'⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hc') hc
    have hwU : c'⁻¹ * c ∈ U := hw1 ▸ U.mul_mem hu' (U.inv_mem hu)
    have hφw : φ ⟨_, hwU⟩ = 0 := hv _ hwC
    have hu'eq : (⟨u', hu'⟩ : U) = ⟨_, hwU⟩ * ⟨u, hu⟩ := by
      ext
      simp [hw1]
    have h2 : φ ⟨u', hu'⟩ = φ ⟨u, hu⟩ := by rw [hu'eq, hadd, hφw, zero_add]
    rw [h2, show ρ c = ρ c' * ρ (c'⁻¹ * c) by rw [← map_mul, mul_inv_cancel_left],
      Module.End.mul_apply, htr _ hwU]
  choose s hs using hCU
  obtain ⟨z, hz⟩ : ∃ z : Γ → M, ∀ g, z g = ρ (s g).1.1 (φ (s g).2) := ⟨_, fun _ => rfl⟩
  have hzf : ∀ p : C × U, z (f p) = ρ p.1.1 (φ p.2) := by
    intro p
    rw [hz]
    exact hwd _ _ (by rw [hf, hs])
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hfc : Continuous f := by
    have : f = fun p : C × U => p.1.1 * p.2.1 := funext hf
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfs : Function.Surjective f := fun g => ⟨s g, by rw [hf, hs]⟩
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
  have hzc : Continuous z := by
    rw [hq.continuous_iff]
    have : z ∘ f = fun p : C × U => ρ p.1.1 (φ p.2) := funext hzf
    rw [this]
    exact hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  have hzU : ∀ u : U, z u.1 = φ u := by
    intro u
    have h1 := hzf (⟨1, C.one_mem⟩, u)
    rw [hf] at h1
    simpa using h1
  have hcoc : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := by
    intro g h
    obtain ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, rfl⟩ := hfs g
    obtain ⟨⟨⟨d, hd⟩, ⟨v, hv'⟩⟩, rfl⟩ := hfs h
    have hu0 : d⁻¹ * u * d ∈ U := by simpa using hN.conj_mem u hu d⁻¹
    have hprod : f (⟨c, hc⟩, ⟨u, hu⟩) * f (⟨d, hd⟩, ⟨v, hv'⟩)
        = f (⟨c * d, C.mul_mem hc hd⟩, ⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩) := by
      simp only [hf, Subgroup.coe_mul]
      group
    rw [hprod, hzf, hzf, hzf, hf]
    change ρ (c * d) (φ (⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩)) = ρ c (φ ⟨u, hu⟩) + ρ (c * u) (ρ d (φ ⟨v, hv'⟩))
    have hconj : φ ⟨u, hu⟩ = ρ d (φ ⟨d⁻¹ * u * d, hu0⟩) :=
      heq d ⟨d⁻¹ * u * d, hu0⟩ ⟨u, hu⟩ (by show u * d = d * (d⁻¹ * u * d); group)
    rw [hadd, map_add, hconj]
    simp only [map_mul, Module.End.mul_apply]
    rw [htr u hu]
  exact ⟨z, ⟨hzc, hcoc⟩, hzU⟩

theorem UpperTheory.V.Kum.extCocycle :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (φ : Uinf F Ω l → M), Procyc F Ω l → ContAction ρ → (∀ u ∈ Uinf F Ω l, ∀ m, ρ u m = m) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) →
    IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ g : G F Ω, φ ∈ conjCond (Uinf F Ω l) g.toRingEquiv (ρ g)) → ∃ z ∈ Z1 ρ, ∀ u : Uinf F Ω l, z u.1 = φ u := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ ρ φ hP hρ htr htors hloc hadd hconj
  classical
  have hVc : IsClosed ((cycZ F Ω l).range : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ F Ω l)).isClosed
  have hcond : l ≠ 2 ∨ (cycZ F Ω l).range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mpr (h g)
  obtain ⟨γ0, hγ0, hgen⟩ := existsGen l _ hVc hcond
  obtain ⟨γ, rfl⟩ := hγ0
  have hnf : ¬ IsOfFinOrder (cycZ F Ω l γ) := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hS : ∀ u ∈ (cycZ F Ω l).range, u ^ n = 1 := by
      intro u hu
      have hsub : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
          ⊆ {x | x ^ n = 1} := by
        apply closure_minimal
        · intro x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          show ((cycZ F Ω l γ) ^ k) ^ n = 1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
        · exact isClosed_eq (continuous_pow n) continuous_const
      have h1 := hgen hu
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
      exact hsub h1
    have htop : KStar.TotallyRealRoots.nu l (KStar.TotallyRealRoots.galImage l F) n = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro k
      rw [KStar.TotallyRealRoots.le_nu_iff_pow_mem_princ]
      intro u hu
      rw [KStar.TotallyRealRoots.mem_galImage_iff_of_equiv (RingEquiv.refl F) Ω] at hu
      obtain ⟨g, rfl⟩ := hu
      have h2 := hS (cyclotomicCharacter Ω l g.toRingEquiv) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      rw [h2]
      exact Subgroup.one_mem _
    exact KStar.TotallyRealRoots.nu_ne_top KStar.TotallyRealRoots.isOpen_galImage hn.ne' htop
  haveI hN : (Uinf F Ω l).Normal := by
    show (⊤ ⊓ (cycZ F Ω l).ker).Normal
    infer_instance
  have hUc : IsClosed ((Uinf F Ω l : Subgroup (G F Ω)) : Set (G F Ω)) := by
    show IsClosed ((⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω)) : Set (G F Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_top, Set.univ_inter, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ F Ω l)
  have hCc := Subgroup.isClosed_topologicalClosure (Subgroup.zpowers γ)
  have hmemU : ∀ x : G F Ω, cycZ F Ω l x = 1 → x ∈ Uinf F Ω l := by
    intro x hx
    show x ∈ (⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω))
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, MonoidHom.mem_ker.mpr hx⟩
  have hCU : ∀ g : G F Ω, ∃ p : (Subgroup.zpowers γ).topologicalClosure × Uinf F Ω l,
      p.1.1 * p.2.1 = g := by
    intro g
    have himg : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
        ⊆ (cycZ F Ω l) '' ((Subgroup.zpowers γ).topologicalClosure : Set (G F Ω)) := by
      apply closure_minimal
      · intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨γ ^ k, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k), map_zpow _ _ _⟩
      · exact (hCc.isCompact.image (continuous_cycZ F Ω l)).isClosed
    have hg := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hg
    obtain ⟨c, hc, hcg⟩ := himg hg
    refine ⟨(⟨c, hc⟩, ⟨c⁻¹ * g, hmemU _ ?_⟩), mul_inv_cancel_left c g⟩
    rw [map_mul, map_inv, hcg, inv_mul_cancel]
  have heq : ∀ (g : G F Ω) (u u' : Uinf F Ω l), u'.1 * g = g * u.1 → φ u' = ρ g (φ u) := by
    intro g u u' h
    apply hconj g u u'
    intro x
    have h3 := congrArg (fun e : G F Ω => e x) h
    simpa [AlgEquiv.mul_apply] using h3
  have hv : ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 :=
    fun x hx => vanishCyc F Ω l M φ γ hloc hadd htors hnf x hx
  exact ext_of_prod ρ _ _ hCc hUc hCU φ hρ htr hloc.continuous hadd heq hv
