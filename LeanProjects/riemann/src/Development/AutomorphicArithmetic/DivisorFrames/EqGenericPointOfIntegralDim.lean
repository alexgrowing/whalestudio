import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem eq_bot_of_trdeg_le (k A k' : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field k'] [Algebra k k'] (q : Ideal A) [q.IsPrime]
    (ψ : q.ResidueField →+* k') (hψ : ψ.IsIntegral)
    (hc : (ψ.comp (algebraMap A q.ResidueField)).comp (algebraMap k A) = algebraMap k k')
    (h : Algebra.trdeg k A ≤ Algebra.trdeg k k') : q = ⊥ := by
  by_contra hq
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨d, hd, hd'⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  obtain ⟨e, he, he'⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (A ⧸ q)
  have hlt := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q)
    Ideal.Quotient.mk_surjective (r := r) (mem_nonZeroDivisors_of_ne_zero hr0)
    (Ideal.Quotient.eq_zero_iff_mem.2 hr)
  rw [hd, he] at hlt
  have hlt' : e + 1 ≤ d := by exact_mod_cast hlt
  letI : Algebra q.ResidueField k' := ψ.toAlgebra
  haveI : IsScalarTower k q.ResidueField k' := IsScalarTower.of_algebraMap_eq fun a => by
    rw [← hc, IsScalarTower.algebraMap_apply k A q.ResidueField]
    rfl
  haveI : Algebra.IsIntegral q.ResidueField k' := ⟨hψ⟩
  haveI : Algebra.IsAlgebraic (A ⧸ q) q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  haveI : FaithfulSMul k (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k (A ⧸ q)).injective
  haveI : FaithfulSMul (A ⧸ q) q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k q.ResidueField k',
    GlobalTheory.trdeg_eq_of_isAlgebraic_top k (A ⧸ q) q.ResidueField, hd', he'] at h
  have : d ≤ e := by exact_mod_cast h
  omega

private theorem trdeg_functionField_eq (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (d : ℕ)
    (hd : topologicalKrullDim X = d) :
    letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom.toAlgebra
    Algebra.trdeg k X.functionField = d := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := GlobalTheory.exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨e, he⟩ := GlobalTheory.exists_trdeg_eq_natCast k (A := A)
  rw [hA] at he
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq f he
  have h2 : (f ⁻¹' {genericPoint (Spec (CommRingCat.of k))} : Set X) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rw [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hd] at h1
  obtain rfl : d = e := by exact_mod_cast h1
  exact he

theorem UpperTheory.eq_genericPoint_of_integral_dim :
    ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Sp k) (sY : Y ⟶ Sp k) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (d : ℕ), topologicalKrullDim X = d → topologicalKrullDim Y = d → ∀ (x : X) (k' : Type) [Field k'] (ψ : X.residueField x →+* k') (θ : Y.functionField →+* k'), ψ.IsIntegral → spMap ψ ≫ X.fromSpecResidueField x ≫ sX = spMap θ ≫ gpt Y ≫ sY → x = genericPoint X := by
  intro k _ X Y _ _ sX sY _ _ d hX hY x k' _ ψ θ hψ h
  have tX := trdeg_functionField_eq k X sX d hX
  have tY := trdeg_functionField_eq k Y sY d hY
  obtain ⟨A, _, _, _, _, _, j, _, ⟨q, rfl⟩, hj, hA⟩ := GlobalTheory.exists_affine_chart_trdeg_eq sX x
  rw [tX] at hA
  haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let φ := Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ sY)
  letI : Algebra k Y.functionField := φ.hom.toAlgebra
  letI : Algebra k k' := (θ.comp φ.hom).toAlgebra
  let θ' : Y.functionField →ₐ[k] k' := { θ with commutes' := fun _ => rfl }
  have hle : Algebra.trdeg k Y.functionField ≤ Algebra.trdeg k k' :=
    trdeg_le_of_injective θ' θ.injective
  rw [tY, ← hA] at hle
  let e : CommRingCat.of q.asIdeal.ResidueField ≅ X.residueField (j q) :=
    (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (CommRingCat.of A) q).symm
  have he : Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField)) ≫ j =
      X.fromSpecResidueField (j q) := by
    rw [← cancel_epi (Spec.map (j.residueFieldMap q)),
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp_assoc]
    simp [e]
  have hq : q.asIdeal = ⊥ := by
    refine eq_bot_of_trdeg_le k A k' q.asIdeal (ψ.comp e.hom.hom)
      (RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso e.hom).2) hψ) ?_ hle
    let ψ₀ : X.residueField (j q) ⟶ CommRingCat.of k' := CommRingCat.ofHom ψ
    let θ₀ : Y.presheaf.stalk (genericPoint Y) ⟶ CommRingCat.of k' := CommRingCat.ofHom θ
    have h' : Spec.map (CommRingCat.ofHom (algebraMap k A) ≫
        CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) ≫ e.hom ≫ ψ₀) =
        Spec.map (φ ≫ θ₀) := by
      simp only [Spec.map_comp, Category.assoc]
      rw [← hj, reassoc_of% he, Spec.map_preimage]
      exact h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  have hq' : q = genericPoint (Spec (CommRingCat.of A)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [hq']
  exact genericPoint_eq_of_isOpenImmersion j
