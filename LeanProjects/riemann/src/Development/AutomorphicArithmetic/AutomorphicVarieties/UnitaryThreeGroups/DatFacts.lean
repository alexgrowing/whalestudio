import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdIffIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EqOfIndexTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem open_galOf (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsOpen (galOf ℚ K Ω : Set (G ℚ Ω)) := by
  let b := Module.finBasis ℚ K
  have e : (galOf ℚ K Ω : Set (G ℚ Ω)) = ⋂ i, {σ : G ℚ Ω | σ (algebraMap K Ω (b i)) = algebraMap K Ω (b i)} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_galOf]
    refine ⟨fun h i => h _, fun h x => ?_⟩
    have := b.ext (f₁ := σ.toLinearMap ∘ₗ (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap)
      (f₂ := (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap) h
    exact LinearMap.congr_fun this x
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := ℚ) _ (fun t => t = algebraMap K Ω (b i))

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem tor_eq_one {R : Type} [CommRing R] {t : Rˣ} (h : tor R t = 1) : t = 1 := by
  have h1 := congrArg (fun x : GL (Fin 3) R => (x : Matrix (Fin 3) (Fin 3) R) 0 0) h
  apply Units.ext
  simpa [tor_val, wt1] using h1

private theorem diagonal_rep_eq_one_iff {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    r0 η Ψ g = 1 ↔ η g = 1 ∧ Ψ g = 1 := by
  refine ⟨fun h => ⟨congrArg SemidirectProduct.right h, tor_eq_one (congrArg SemidirectProduct.left h)⟩, fun h => ?_⟩
  refine SemidirectProduct.ext ?_ h.1
  rw [unitaryThreeReflection_left, h.2, map_one]
  rfl

private theorem bar_lc {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ)
    (hΨ : CharCont Ψ) : IsLocallyConstant (barChar O Ψ) := by
  refine IsLocallyConstant.desc _ Units.val ?_ Units.val_injective
  have h := (hΨ 1 1).comp (Ideal.Quotient.factor (pow_one (maximalIdeal O)).le)
  simp only [zpow_one] at h
  exact h

theorem UpperTheory.V.U3.dat_facts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      D.cc * D.cc = 1 ∧ D.η D.cc = -1 ∧ D.Ψ D.cc = 1 ∧ IsLocallyConstant D.η ∧ IsLocallyConstant (barChar c.O D.Ψ) ∧
      (∀ g ∈ D.Kill, r0 D.η D.Ψ g = 1) ∧ IsUnit (2 : c.O) ∧ IsCMField K ∧ Continuous D.ΨQ ∧
      (∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧ D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1) ∧
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.η.ker ∧
        ∃ s ∈ Ine (F := ℚ) A, IsUnit ((D.Ψ s : c.O) ^ 2 - 1)) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨w, η', a, hlit⟩ := (gdIff Ω K l c e N ψ).1.1 D.gd
  have himag := D.gd.imag
  have hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
      D.Ψ g = Chr.dirG ℚ Ω ψ g := fun A hA g hg => by
    show (chiO ℚ Ω l c.O g) ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g = _
    have : chiO ℚ Ω l c.O g = 1 := by
      unfold chiO
      rw [MonoidHom.comp_apply, cyc_ine Ω l A hA hg, map_one]
    rw [this, _root_.one_zpow, one_mul]
  have hkill : ∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧
      D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1 := fun g => by
    refine exists_congr fun A => and_congr_right fun hA => and_congr_right fun hg => ?_
    unfold rbar
    rw [diagonal_rep_eq_one_iff]
    refine and_congr_right fun _ => ?_
    unfold barChar
    rw [MonoidHom.comp_apply, hΨ A hA g hg]
    refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hlit.ord ?_ (one_pow _) ?_
    · rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, Units.val_one, map_one]
      exact congrArg Units.val h
  obtain ⟨φ, hφ⟩ := D.conj
  refine ⟨?_, ?_, hlit.par D.cc ⟨φ, hφ⟩, ?_, ?_, fun g hg => ?_, ?_, ?_, ?_, hkill, fun A hA => ?_⟩
  · refine AlgEquiv.ext fun x => φ.injective ?_
    rw [AlgEquiv.mul_apply, hφ, hφ]
    simp
  · refine (Int.units_eq_one_or _).resolve_left fun h => ?_
    have h1 : D.cc ∈ galOf ℚ K Ω := D.η_ker ▸ h
    refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]
  · exact locConst _ (D.η_ker ▸ open_galOf Ω K)
  · exact bar_lc _ D.Ψ_cont
  · obtain ⟨A, hA, hg, h1, h2⟩ := (hkill g).1 hg
    exact (diagonal_rep_eq_one_iff _ _ _).2 ⟨h1, (hΨ A hA g hg).trans h2⟩
  · have := (dvrFacts l c.O).2.2.2.2.2.2.2.2 2 fun h => D.gd.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  · have : Algebra.IsQuadraticExtension ℚ K := ⟨D.gd.quad⟩
    exact IsCMField.ofCMExtension ℚ K
  · have hf : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom := by
      refine ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val).congr fun x => ?_
      exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x).symm
    have h1 := ((hf.units_map _).comp (continuous_cycZ ℚ Ω l)).zpow (e : ℤ)
    have h2 := (((locConst _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom).comp
      (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom)).continuous
    refine (h1.mul h2).congr fun g => ?_
    show _ = Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g)
    rw [map_mul, map_zpow]
    rfl
  · obtain ⟨h1, s, hs, h2⟩ := (gdLoc Ω K l c e N ψ w η' a hlit).1 A hA
    refine ⟨D.η_ker ▸ h1, s, hs, ?_⟩
    rw [Units.val_pow_eq_pow_val] at h2
    exact not_not.1 h2
