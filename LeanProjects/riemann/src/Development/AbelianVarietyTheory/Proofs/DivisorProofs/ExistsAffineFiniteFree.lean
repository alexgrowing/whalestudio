import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.GenDeg

namespace GlobalTheory.GenFree

theorem exists_free_away (A M : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] : ∃ g : A, g ≠ 0 ∧ Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨g, nonZeroDivisors.ne_zero hg, hfree⟩

theorem free_basicOpen {X Y : Scheme.{0}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (g : Γ(Y, V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free (Localization.Away g) (LocalizedModule.Away g Γ(X, f ⁻¹ᵁ V))) :
    letI := (f.app (Y.basicOpen g)).hom.toAlgebra
    Module.Free Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have hpre : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen _ _
  let A := Γ(Y, V)
  let M := Γ(X, f ⁻¹ᵁ V)
  let R := Γ(Y, Y.basicOpen g)
  let N := Γ(X, f ⁻¹ᵁ Y.basicOpen g)
  letI : Algebra A R := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g R := hV.isLocalization_basicOpen g
  have hle : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ V := f.preimage_mono (Y.basicOpen_le g)
  letI : Algebra M N := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI : IsLocalization.Away (algebraMap A M g) N :=
    hV'.isLocalization_of_eq_basicOpen (f.app V g) (homOfLE hle) hpre
  letI : Algebra R N := (f.app (Y.basicOpen g)).hom.toAlgebra
  letI : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A M N := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.app _).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom a) =
      (X.presheaf.map (homOfLE hle).op).hom ((f.app V).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers g)) N := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom A M N).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (IsScalarTower.toAlgHom A M N).toLinearMap
  let b₀ := Module.Free.chooseBasis (Localization.Away g) (LocalizedModule.Away g M)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) R
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars A ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) R
  exact Module.Free.of_basis (Module.Basis.ofRepr Ψ')

theorem exists_dim_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp F) [LocallyOfFiniteType q] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (genericPoint Y))
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ q)
  have hφ : Spec.map φ = hU.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  obtain ⟨d, h₁, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F q U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem exists_affine_finite_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Sp k) (f : X ⟶ Y), IsProjOver (f ≫ sY) → IsProjOver sY → f (genericPoint X) = genericPoint Y → topologicalKrullDim X ≤ topologicalKrullDim Y → ∀ n : ℕ, f.residueDegree (genericPoint X) = n → ∃ V : Y.Opens, genericPoint Y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧ (letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n) := by
  intro k _ X Y _ _ sY f hX hY hη hdim n hn
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hX
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hY
  have : IsProper f := IsProper.of_comp f sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have hs := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  obtain ⟨d, hdY⟩ := exists_dim_eq k sY
  have hdX : topologicalKrullDim X = d :=
    (le_antisymm hdim (PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective)).trans hdY
  have hd : f.residueDegree (genericPoint X) ≠ 0 :=
    GenFinite.residueDegree_genericPoint_ne_zero k X Y sY f d inferInstance inferInstance hs hdX hdY
  obtain ⟨V₀, hV₀, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint Y) ((Set.finite_singleton (genericPoint X)).subset
      fun y hy => GenFiniteEtale.eq_genericPoint f hη hd hy)
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV₀
  replace hV : IsAffineOpen V := hV
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨hW, hf⟩ := GenFiniteEtale.finite_app_of_le f hV hle
  letI := (f.app V).hom.toAlgebra
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hf
  obtain ⟨g, hg, hfree⟩ := exists_free_away Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  have hU := hV.basicOpen g
  have hxU := GenFiniteEtale.genericPoint_mem_basicOpen hg
  obtain ⟨hW', hf'⟩ := GenFiniteEtale.finite_app_of_le f hU ((Y.basicOpen_le g).trans hle)
  refine ⟨Y.basicOpen g, hxU, hU, hW', free_basicOpen f hV hW g hfree, hf', ?_⟩
  have := (GenFiniteEtale.affine_pair f hη hd hU hW' le_rfl (show f _ ∈ Y.basicOpen g from hη ▸ hxU)).2.2.1
  rw [← f.app_eq_appLE] at this
  exact this.trans hn

end GlobalTheory.GenFree
