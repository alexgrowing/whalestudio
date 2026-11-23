import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrSubringEqTopStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem formallyUnramified_of_dvr_of_essFiniteType : ∀ (R T V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T] [Algebra R T] [Algebra.FormallyUnramified R T] [Algebra.EssFiniteType R T] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] (μ : T →ₐ[R] V), (∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R V r ∈ IsLocalRing.maximalIdeal V) → Function.Injective (algebraMap R V) → (∀ v : V, ∃ a b : T, μ b ≠ 0 ∧ v * μ b = μ a) → Algebra.FormallyUnramified R V := by
  intro R T V _ _ _ _ _ _ _ _ _ _ _ μ hm hinj hfrac
  let Q : Ideal T := (IsLocalRing.maximalIdeal V).comap μ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime Q
  haveI : Algebra.FormallyUnramified T D := .of_isLocalization Q.primeCompl
  haveI : Algebra.FormallyUnramified R D := .comp R T D
  haveI : Algebra.EssFiniteType T D := .of_isLocalization D Q.primeCompl
  haveI : Algebra.EssFiniteType R D := .comp R T D
  have hQ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R T r ∈ Q := fun r hr => by
    show μ (algebraMap R T r) ∈ IsLocalRing.maximalIdeal V
    rw [μ.commutes]; exact hm r hr
  haveI : IsLocalHom (algebraMap R D) := ⟨fun r hr => by
    by_contra hnu
    rw [IsScalarTower.algebraMap_apply R T D, IsLocalization.AtPrime.isUnit_to_map_iff D Q] at hr
    exact hr (hQ r ((IsLocalRing.mem_maximalIdeal _).2 hnu))⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hunit : ∀ y : Q.primeCompl, IsUnit (μ y) := fun y => by
    by_contra h; exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let ν : D →ₐ[R] V := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := μ) hunit
  have hν : ∀ t, ν (algebraMap T D t) = μ t := fun t => IsLocalization.lift_eq _ _
  have hνu : ∀ d, IsUnit (ν d) → IsUnit d := by
    intro d hd
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl d
    have e : IsLocalization.mk' D x s * algebraMap T D s = algebraMap T D x :=
      IsLocalization.mk'_spec D x s
    have hx : IsUnit (μ x) := by
      have := congrArg ν e
      rw [map_mul, hν, hν] at this
      rw [← this]; exact hd.mul (hunit s)
    have hxQ : x ∈ Q.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
    have : IsUnit (algebraMap T D x) := IsLocalization.map_units D (⟨x, hxQ⟩ : Q.primeCompl)
    rw [← e] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmD : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D ϖ} := by
    rw [← hmax, hmR, Ideal.map_span, Set.image_singleton]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hS := GlobalTheory.T.subring_eq_univ_of_uniformizer_generates V (ν : D →+* V).range (algebraMap R V ϖ) ⟨algebraMap R D ϖ, ν.commutes ϖ⟩
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (hm ϖ hϖm) ?_ ?_ ?_
  · refine Algebra.FormallyUnramified.of_surjective ν fun v => ?_
    have hv : v ∈ (ν : D →+* V).range := hS ▸ Subring.mem_top v
    obtain ⟨d, hd⟩ := hv
    exact ⟨d, hd⟩
  · rintro _ ⟨d, rfl⟩ hs
    have hu : IsUnit (ν d) := by
      by_contra h; exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu'⟩ := hνu d hu
    refine ⟨ν ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
    change ν d * ν ↑u⁻¹ = 1
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  · rintro _ ⟨d, rfl⟩ hs
    have hd : d ∈ IsLocalRing.maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).2 fun h =>
      (IsLocalRing.mem_maximalIdeal _).1 hs (h.map ν)
    rw [hmD] at hd
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hd
    refine ⟨ν a, ⟨a, rfl⟩, ?_⟩
    change ν (a * algebraMap R D ϖ) = _
    rw [map_mul, ν.commutes, mul_comm]
  · intro v
    obtain ⟨a, b, hb, hab⟩ := hfrac v
    exact ⟨μ a, ⟨_, hν a⟩, μ b, ⟨_, hν b⟩, hb, hab⟩

end GlobalTheory

namespace GlobalTheory

theorem trace_dvr_formallyUnramified_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  intro M W _ _ f _ U hU z hz V _ _ hV
  obtain ⟨-, hfe, hess⟩ :=
    stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU z hz
  set φ := functionFieldMap f with hφ
  set R := V.comap φ
  let A := W.presheaf.stalk (f z)
  let B := M.presheaf.stalk z
  let g : A →+* B := (f.stalkMap z).hom
  letI : Algebra A B := g.toAlgebra
  haveI : Algebra.FormallyEtale A B := hfe
  haveI : Algebra.EssFiniteType A B := hess
  have hcomp : ∀ a : A, φ (algebraMap A W.functionField a) = algebraMap B M.functionField (g a) :=
    fun a => functionFieldMap_algebraMap f z a
  have hαR : ∀ a : A, algebraMap A W.functionField a ∈ R := fun a => by
    change φ _ ∈ V
    rw [hcomp]; exact hV.1 _
  let αR : A →+* R := (algebraMap A W.functionField).codRestrict R hαR
  let βV : B →+* V := (algebraMap B M.functionField).codRestrict V hV.1
  letI algRV : Algebra R V := (φ.restrict R V fun _ hx => hx).toAlgebra
  letI : Algebra A R := αR.toAlgebra
  letI : Algebra A V := (βV.comp g).toAlgebra
  haveI : IsScalarTower A R V := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hcomp a).symm
  let gV : B →ₐ[A] V := { βV with commutes' := fun _ => rfl }
  let μ : TensorProduct A R B →ₐ[R] V :=
    Algebra.TensorProduct.lift (Algebra.ofId R V) gV fun _ _ => Commute.all _ _
  haveI : Algebra.FormallyUnramified R (TensorProduct A R B) := Algebra.FormallyUnramified.base_change R
  haveI : Algebra.EssFiniteType R (TensorProduct A R B) := Algebra.EssFiniteType.baseChange A B R
  refine formallyUnramified_of_dvr_of_essFiniteType R (TensorProduct A R B) V μ ?_ ?_ ?_
  · intro r hr
    by_contra hnu
    have hu : IsUnit (algebraMap R V r) := by
      by_contra h; exact hnu ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw' : φ (r : W.functionField) * (w : M.functionField) = 1 := congrArg Subtype.val hw
    have hr0 : (r : W.functionField) ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hw'; exact zero_ne_one hw'
    have hinv : (r : W.functionField)⁻¹ ∈ R := by
      change φ _ ∈ V
      rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hw']
      exact w.2
    exact (IsLocalRing.mem_maximalIdeal _).1 hr
      (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hr0)⟩)
  · intro x y hxy
    exact Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (v : M.functionField)
    have hμ : ∀ c : B, ((μ (1 ⊗ₜ c) : V) : M.functionField) = algebraMap B M.functionField c := by
      intro c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_, ?_⟩
    · intro h0
      apply nonZeroDivisors.ne_zero hb
      apply IsFractionRing.injective B M.functionField
      rw [map_zero]
      rw [← hμ, h0]; rfl
    · apply Subtype.ext
      rw [Subring.coe_mul, hμ, hμ]
      rw [← hab, div_mul_cancel₀]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

end GlobalTheory
