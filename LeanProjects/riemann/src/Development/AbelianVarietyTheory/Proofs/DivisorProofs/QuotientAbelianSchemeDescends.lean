import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointAlgebraicModelStatement
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogModel

theorem exists_model_of_surjective : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  intro A₀ _ A X _ _ p g hA₀ hg₀ hp hX hgX ψ hψ hpts
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg₀
  haveI : Surjective ψ.left := GlobalTheory.T.surjective_of_surjective_on_points A X ψ hA hX hpts
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.isogeny_finite_flat A X g hA hX hgA hgX ψ
  obtain ⟨n, hn, hkn⟩ := GlobalTheory.HolUnifEnd.exists_pow_eq_one_of_surjective A X g hA hX hgA hgX ψ
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : (𝟙_ (Over (Sp Qb)) ⟶ A₀) →* (Over.mk t ⟶ A₀) :=
    { toFun := fun c => toUnit (Over.mk t) ≫ c
      map_one' := MonObj.comp_one _
      map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  have hr : Function.Injective r := fun a b h => Over.OverMorphism.ext ((cancel_epi t).1 (by
    have := congrArg (fun q => q.left) h
    simpa only [r, MonoidHom.coe_mk, OneHom.coe_mk, Over.comp_left, hl] using this))
  let ψp : (Over.mk (𝟙 (Sp ℂ)) ⟶ A) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ X) :=
    { toFun := fun x => x ≫ ψ
      map_one' := MonObj.one_comp _
      map_mul' := fun a b => MonObj.mul_comp _ _ _ }
  let C₀ : Subgroup (𝟙_ (Over (Sp Qb)) ⟶ A₀) := (ψp.comp (e.symm.toMonoidHom.comp r)).ker
  have hC : ∀ c, c ∈ C₀ ↔ e.symm (r c) ≫ ψ = 1 := fun c => Iff.rfl
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hfinT := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA₀ hg₀ hnQ
  have hC₀ : Finite C₀ := by
    refine Finite.of_injective (β := {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1})
      (fun c => ⟨c.1, ?_⟩) (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h1 := hkn (e.symm (r c.1)) ((hC c.1).1 c.2)
    apply hr
    rw [map_pow, map_one, ← e.apply_symm_apply (r c.1), ← map_pow, h1, map_one]
  obtain ⟨X₀, _, π₀, hX₀, hπ₀, hfin₀, het₀, hsurj₀, hker₀⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points Qb A₀ hA₀ C₀ hC₀
  haveI := hπ₀
  have hgX₀ : SmoothOfRelativeDimension g X₀.hom := by
    have := hX₀.smooth
    exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover Qb A₀.left X₀.left π₀.left X₀.hom g het₀
      hsurj₀ inferInstance (by rw [Over.w]; exact hg₀)
  let X' : Over (Sp ℂ) := (Over.pullback t).obj X₀
  letI : GrpObj X' := Functor.grpObjObj
  have hX' : IsGrpPullback X' X₀ t (pullback.fst X₀.hom t) := isGrpPullback_pullback X₀ t
  have hXa' : IsAbelianScheme X' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hX₀ hX'
  obtain ⟨e', he'⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hX' (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  obtain ⟨π, hπ, hπp⟩ := GlobalTheory.HomDescent.exists_isMonHom_pull hp hX' π₀
  haveI := hπ
  have hsq : IsPullback p π.left π₀.left (pullback.fst X₀.hom t) :=
    IsPullback.of_bot (by rw [Over.w π, Over.w π₀]; exact hp.1) hπp.symm hX'.1
  have hπe : Etale π.left := MorphismProperty.of_isPullback (P := @Etale) hsq het₀
  have hπs : Surjective π.left := MorphismProperty.of_isPullback (P := @Surjective) hsq hsurj₀
  have hπf : IsFinite π.left := MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin₀

  have key : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, e' (x ≫ π) = e x ≫ π₀ := fun x => by
    refine Over.OverMorphism.ext ?_
    rw [he', Over.comp_left, Over.comp_left, he, Category.assoc, hπp, Category.assoc]
  have hsep : IsSeparated X.hom := by have := hX.proper; infer_instance
  have hsep' : IsSeparated X'.hom := by have := hXa'.proper; infer_instance

  obtain ⟨Zπ, _, iπ, _, _, hkπ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel π
  have hZπ : Etale Zπ.hom := by
    have h1 : Etale (toUnit Zπ).left :=
      MorphismProperty.of_isPullback (P := @Etale) (hkπ.map (Over.forget _)) hπe
    have h2 : (toUnit Zπ).left = Zπ.hom := by simpa using Over.w (toUnit Zπ)
    rwa [h2] at h1
  haveI : IsReduced Zπ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zπ.hom
  have hkill1 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ π = 1 → x ≫ ψ = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X' X Zπ π ψ iπ hkπ fun x hx => ?_
    have h1 : e x ≫ π₀ = 1 := by rw [← key, hx, map_one]
    obtain ⟨c, hc, hcx⟩ := (hker₀ ℂ t (e x)).1 h1
    have : x = e.symm (r c) := by rw [show r c = e x from hcx.symm]; simp
    rw [this]
    exact (hC c).1 hc
  obtain ⟨⟨β, hβ, hβc⟩, hepiπ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X' X π ψ hπ hψ
    inferInstance hπs inferInstance hkill1

  obtain ⟨Zψ, _, iψ, _, _, hkψ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel ψ
  have hZψf : IsFinite Zψ.hom := by
    have h1 : IsFinite (toUnit Zψ).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) (hkψ.map (Over.forget _)) hfin
    have h2 : (toUnit Zψ).left = Zψ.hom := by simpa using Over.w (toUnit Zψ)
    rwa [h2] at h1
  letI : GrpObj (Over.mk Zψ.hom) := ‹GrpObj Zψ›
  have hZψ : Etale Zψ.hom := GlobalTheory.etale_of_grpObj_of_isFinite (k := ℂ) Zψ.hom
  haveI : IsReduced Zψ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zψ.hom
  have hkill2 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ≫ π = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X X' Zψ ψ π iψ hkψ fun x hx => ?_
    obtain ⟨c, hc⟩ := GlobalTheory.T.torsion_point_algebraic_model A₀ A p g n hA₀ hg₀ hp hn x (hkn x hx)
    have hxc : e x = r c := Over.OverMorphism.ext (by
      rw [he, hc]
      show t ≫ c.left = (toUnit (Over.mk t) ≫ c).left
      rw [Over.comp_left, hl])
    have hcC : c ∈ C₀ := by
      rw [hC, ← hxc, e.symm_apply_apply]; exact hx
    have h1 : e x ≫ π₀ = 1 := (hker₀ ℂ t (e x)).2 ⟨c, hcC, hxc⟩
    rw [← key] at h1
    exact (map_eq_one_iff e' e'.injective).1 h1
  obtain ⟨⟨κ, hκ, hκc⟩, hepiψ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X X' ψ π hψ hπ
    hflat inferInstance inferInstance hkill2
  have h1 : β ≫ κ = 𝟙 X' := (cancel_epi π).1 (by rw [← Category.assoc, hβc, hκc, Category.comp_id])
  have h2 : κ ≫ β = 𝟙 X := (cancel_epi ψ).1 (by rw [← Category.assoc, hκc, hβc, Category.comp_id])
  let iso : X ≅ X' := ⟨κ, β, h2, h1⟩
  haveI : IsMonHom iso.hom := hκ
  refine ⟨X₀, inferInstance, κ.left ≫ pullback.fst X₀.hom t, hX₀, hgX₀, ?_⟩
  exact ((isGrpPullback_of_iso iso).comp hX').congr (Category.id_comp t) rfl

end GlobalTheory.IsogModel
