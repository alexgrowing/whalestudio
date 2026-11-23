import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

open NumberField NumberField.InfinitePlace Real in
private theorem pid4 (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {2 ^ 2} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K, IsCyclotomicExtension.Rat.finrank (2 ^ 2) K,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (2 ^ 2) K]
  have h4 : (2 ^ 2 : ℕ).totient = 2 := by decide
  rw [h4]
  norm_num [Nat.factorial]
  nlinarith [Real.pi_gt_three]

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum in
private theorem char_triv (K Ω : Type) [Field K] [NumberField K] [IsCyclotomicExtension {2 ^ 2} ℚ K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (C : Type) [CommGroup C] (χ : G K Ω →* C) (h : IsLocallyConstant χ)
    (hI : ∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker) (g : G K Ω) : χ g = 1 := by
  haveI : IsPrincipalIdealRing (𝓞 K) := pid4 K
  have hc : Fintype.card (ClassGroup (𝓞 K)) = 1 := by
    convert card_classGroup_eq_one (R := 𝓞 K)
  have hsub : Subsingleton (ClassGroup (𝓞 K)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hc)
  have hopen : IsOpen (χ.ker : Set (G K Ω)) := by
    have : (χ.ker : Set (G K Ω)) = χ ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact h.isOpen_fiber 1
  have hconj : ∀ c : G K Ω, UpperTheory.V.IsConjOm c.toRingEquiv → χ c = 1 := by
    rintro c ⟨j, hj⟩
    exfalso
    have hζ := IsCyclotomicExtension.zeta_spec (2 ^ 2) ℚ K
    set z : Ω := algebraMap K Ω (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) with hz
    have hz4 : z ^ 4 = 1 := by
      rw [hz, ← map_pow, show (4 : ℕ) = 2 ^ 2 by norm_num, hζ.pow_eq_one, map_one]
    have hz2 : z ^ 2 ≠ 1 := by
      intro h2
      have hinj := (algebraMap K Ω).injective
      have : (IsCyclotomicExtension.zeta (2 ^ 2) ℚ K) ^ 2 = 1 := by
        apply hinj
        rw [map_pow, map_one]
        exact h2
      have := (hζ.pow_eq_one_iff_dvd 2).1 this
      norm_num at this
    have hsq : z ^ 2 = -1 := by
      have hf : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
        have : (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
        rw [this, hz4, sub_self]
      rcases mul_eq_zero.1 hf with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hz2
      · exact eq_neg_of_add_eq_zero_left h0
    have hfix : c z = z := by
      rw [hz]
      exact c.commutes _
    have hw := hj z
    have hcz : c.toRingEquiv z = z := hfix
    rw [hcz] at hw
    have hw2 : (j z) ^ 2 = -1 := by
      rw [← map_pow, hsq, map_neg, map_one]
    have him : (j z).im = 0 := by
      have := congrArg Complex.im hw
      simp at this
      linarith
    have hre := congrArg Complex.re hw2
    simp [pow_two, Complex.mul_re, him] at hre
    nlinarith [sq_nonneg (j z).re]
  have hk := UpperTheory.V.Kum.artKer K Ω C χ hopen hI hconj
  have hg : g ∈ (UpperTheory.V.Kum.artCl K Ω).ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  exact hk hg

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum IntermediateField in
private theorem mem_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : G ℚ Ω) : σ ∈ galOf ℚ ℚ⟮ζ⟯ Ω ↔ eta4 Ω σ = 1 := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd 2).1 h
    omega
  have hcls : ∀ τ : Formalism.ConjugateSelfDual.G ℚ Ω, τ ζ = ζ ↔ eta4 Ω τ = 1 := by
    intro τ
    have hs := UpperTheory.V.Chr.cls_spec (k := ℚ) 4 τ ζ hζ.pow_eq_one
    have he : eta4 Ω τ = 1 ↔ ZMod.χ₄ ((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = 1 := by
      rw [Units.ext_iff]
      rfl
    rw [he]
    generalize ((UpperTheory.V.Chr.cls ℚ Ω 4 τ : (ZMod 4)ˣ) : ZMod 4) = c at hs
    rw [← ZMod.natCast_zmod_val c]
    have hn : c.val < 4 := ZMod.val_lt c
    generalize c.val = n at hs hn
    rw [hs]
    interval_cases n
    · constructor
      · intro h
        exact absurd (by simpa using h.symm) h1
      · intro h
        exact absurd h (by decide)
    · constructor
      · intro _
        decide
      · intro _
        exact pow_one ζ
    · constructor
      · intro h
        exfalso
        apply h1
        have h' : ζ * ζ = ζ * 1 := by
          rw [mul_one, ← pow_two]
          exact h
        exact mul_left_cancel₀ hz h'
      · intro h
        exact absurd h (by decide)
    · constructor
      · intro h
        exfalso
        apply h2
        have h' : ζ ^ 2 * ζ = 1 * ζ := by
          rw [one_mul, ← pow_succ]
          exact h
        exact mul_right_cancel₀ hz h'
      · intro h
        exact absurd h (by decide)
  constructor
  · intro h
    exact (hcls σ).1 (h ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩)
  · intro h x
    have hs : σ ζ = ζ := (hcls σ).2 h
    have hle : ℚ⟮ζ⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hst : σ ∈ MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ := hs
      have := (Subgroup.zpowers_le (H := MulAction.stabilizer (Formalism.ConjugateSelfDual.G ℚ Ω) ζ)).2 hst hτ
      exact this
    have hx := (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) σ (Subgroup.mem_zpowers σ)
    exact hx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V in
open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v)
    {τ : G k Ω} (hτ : τ ∈ Ine (F := k) B) : ∃ g : G k Ω, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hl : UpperTheory.V.IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hm : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have key := UpperTheory.V.conjGal_mem_Ine hl hm hτ
  refine ⟨σ, ?_⟩
  have he : UpperTheory.V.conjGal hl τ = σ⁻¹ * τ * σ := by
    ext x
    rfl
  rwa [he] at key

open NumberField Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum IntermediateField in
theorem UpperTheory.V.UnitaryThreeInertia.frame_class_one :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    F.Cl1 := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF
  intro Ab _ χ hloc hχ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ 4 := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 4 Ω)
      (Polynomial.degree_cyclotomic_pos 4 Ω (by norm_num)).ne.symm
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).1 hz⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField ℚ⟮ζ⟯ := {}
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ ℚ⟮ζ⟯ := by
    have h4 := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    norm_num
    exact h4
  haveI : IsAlgClosure ℚ⟮ζ⟯ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ℚ⟮ζ⟯⟩
  obtain ⟨hDec, hIne, hcont, hhom⟩ := UpperTheory.V.Kum.toGalDict ℚ Ω ℚ⟮ζ⟯ (galOf ℚ ℚ⟮ζ⟯ Ω) le_rfl
  obtain ⟨hh, _⟩ := hhom le_rfl
  let eq := MulEquiv.ofBijective (UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω))) hh.bijective
  have hker : ∀ u : galOf ℚ ℚ⟮ζ⟯ Ω, F.π u ∈ F.η.ker := by
    intro u
    rw [MonoidHom.mem_ker]
    have h1 := DFunLike.congr_fun hF.η (u : Formalism.ConjugateSelfDual.G ℚ Ω)
    rw [MonoidHom.comp_apply] at h1
    rw [h1]
    exact (mem_iff Ω ζ hζ u).1 u.2
  let ρ : galOf ℚ ℚ⟮ζ⟯ Ω →* F.η.ker := (F.π.comp (galOf ℚ ℚ⟮ζ⟯ Ω).subtype).codRestrict F.η.ker hker
  have hπc : Continuous F.π := by
    rw [hF.π]
    exact continuous_toGS Ω _
  have hρc : Continuous ρ := Continuous.subtype_mk (hπc.comp continuous_subtype_val) _
  have hec : Continuous eq.symm := by
    have hs := (hh.homeomorph _).symm.continuous
    convert hs using 1
    funext x
    apply eq.injective
    rw [MulEquiv.apply_symm_apply]
    exact ((hh.homeomorph _).apply_symm_apply x).symm
  have key : ∀ (B : ValuationSubring Ω) (u : galOf ℚ ℚ⟮ζ⟯ Ω), (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (F := ℚ) B → χ (ρ u) = 1 := by
    intro B u hu
    by_cases hB : B = ⊤
    · have h0 := ((UpperTheory.V.Base.places ℚ Ω l B).2.1 hB).1
      rw [h0, Subgroup.mem_bot] at hu
      have : u = 1 := Subtype.ext hu
      rw [this, map_one, map_one]
    · obtain ⟨v, hv⟩ := (UpperTheory.V.Base.places ℚ Ω l B).1 hB
      by_cases hvS : v ∈ S
      · obtain ⟨g, hg⟩ := conj_ine (hF.isOver ⟨v, hvS⟩) hv hu
        have hgD : g⁻¹ * (u : Formalism.ConjugateSelfDual.G ℚ Ω) * g ∈ F.D ⟨v, hvS⟩ := by
          rw [hF.D]
          exact hg.1
        have hgI : (⟨_, hgD⟩ : F.D ⟨v, hvS⟩) ∈ F.Iv ⟨v, hvS⟩ := by
          rw [Subgroup.mem_subgroupOf, hF.I]
          exact hg
        have heq : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ = F.π u := by
          simp only [UpperTheory.V.UnitaryThreeInertia.Frame.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
          group
        have hmem : F.π g * (F.loc ⟨v, hvS⟩) ⟨_, hgD⟩ * (F.π g)⁻¹ ∈ F.η.ker := by
          rw [heq]
          exact hker u
        have := hχ ⟨v, hvS⟩ ⟨_, hgD⟩ (F.π g) hmem hgI
        rw [← this]
        congr 1
        exact Subtype.ext heq.symm
      · have hN : (u : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ NS Ω (↑S : Set Pl) := by
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          refine Set.mem_iUnion₂.2 ⟨v, ?_, Set.mem_iUnion₂.2 ⟨B, hv, hu⟩⟩
          simpa using hvS
        have : ρ u = 1 := by
          apply Subtype.ext
          show F.π u = 1
          rw [hF.π]
          exact (QuotientGroup.eq_one_iff _).2 hN
        rw [this, map_one]
  have htriv := char_triv ℚ⟮ζ⟯ Ω Ab ((χ.comp ρ).comp eq.symm.toMonoidHom)
    ((hloc.comp_continuous (hρc.comp hec)))
    (by
      intro B τ hτ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
      apply key B
      rw [← hIne B]
      have : UpperTheory.V.Kum.toGal ℚ⟮ζ⟯ (le_refl (galOf ℚ ℚ⟮ζ⟯ Ω)) (eq.symm τ) = τ := eq.apply_symm_apply τ
      rw [MulEquiv.coe_toMonoidHom, this]
      exact hτ)
  ext ⟨γ, hγ⟩
  obtain ⟨u, rfl⟩ : ∃ u : Formalism.ConjugateSelfDual.G ℚ Ω, F.π u = γ := by
    rw [hF.π]
    exact QuotientGroup.mk'_surjective _ γ
  have hu : u ∈ galOf ℚ ℚ⟮ζ⟯ Ω := by
    rw [mem_iff Ω ζ hζ u]
    have h1 := DFunLike.congr_fun hF.η u
    rw [MonoidHom.comp_apply] at h1
    rw [← h1]
    exact hγ
  have := htriv (eq ⟨u, hu⟩)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
  rw [MonoidHom.one_apply, ← this]
  rfl
