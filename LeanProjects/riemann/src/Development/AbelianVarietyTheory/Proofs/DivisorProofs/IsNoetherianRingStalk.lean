import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TraitCen

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]

theorem isNoetherianRing_stalk (M : RatModel o' Ω) (x : M.Z) : IsNoetherianRing (M.Z.presheaf.stalk x) := by
  have : IsDedekindDomain o' := ArithBase.ded (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  infer_instance

theorem isDomain_stalk (M : RatModel o' Ω) (x : M.Z) : IsDomain (M.Z.presheaf.stalk x) :=
  (M.stalkHom_injective x).isDomain _

theorem charZero_stalk (M : RatModel o' Ω) (x : M.Z) : CharZero (M.Z.presheaf.stalk x) := by
  have : CharZero Ω := ArithBase.char (o := o')
  exact ⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩

theorem exists_cdvr (M : RatModel o' Ω) (U₀ : M.Z.Opens) (hU : (U₀ : Set M.Z).Nonempty) (x : M.Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ M.Z),
      a (closedPoint W) = x ∧ ∀ t, (jK W ≫ a) t ∈ U₀ := by
  let O := M.Z.presheaf.stalk x
  have : IsNoetherianRing O := isNoetherianRing_stalk M x
  have : IsDomain O := isDomain_stalk M x
  have : CharZero O := charZero_stalk M x

  have hη : genericPoint M.Z ∈ U₀ := by
    obtain ⟨z, hz⟩ := hU
    exact (genericPoint_specializes z).mem_open U₀.isOpen hz
  have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨q, hq⟩ := h1
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη)
    (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)
  have hf₀ : f₀ ≠ 0 := fun h => hqf (by simp [h])

  let κ := ResidueField (PowerSeries O)
  let p := ringChar κ
  let c : PowerSeries O := if p = 0 then 1 else (p : PowerSeries O)
  have hc0 : c ≠ 0 := by
    by_cases hp : p = 0
    · simp [c, hp]
    · simp only [c, hp, if_false]
      rw [← map_natCast (PowerSeries.C (R := O))]
      exact (map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)
  let f : PowerSeries O := PowerSeries.X * PowerSeries.C f₀ * c
  have hfm : f ∈ maximalIdeal (PowerSeries O) := by
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hf0 : f ∉ (⊥ : Ideal (PowerSeries O)) := by
    rw [Ideal.mem_bot]
    exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0
  let φ : PowerSeries O →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))
  obtain ⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩ :=
    GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ
  let ψ' : O →+* W := ψ.comp PowerSeries.C
  have hψloc : IsLocalHom ψ := ⟨fun a ha => isUnit_of_map_unit φ a (by
    have h := (ha.map (residue W)).map ιk
    rw [← hψ]
    exact h)⟩
  have hCloc : IsLocalHom (PowerSeries.C (R := O)) := ⟨fun a ha => by
    simpa using ha.map (PowerSeries.constantCoeff (R := O))⟩
  have hψ'loc : IsLocalHom ψ' := RingHom.isLocalHom_comp ψ _
  have hψ'f₀ : ψ' f₀ ≠ 0 := fun h => hψf (by
    simp only [f, map_mul]
    rw [show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])
  have hcz : CharZero W := by
    obtain ⟨q, hq⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W q with hqp | hq0
    · exfalso
      have hqW : (q : W) = 0 := CharP.cast_eq_zero W q
      have hqκ : (q : κ) = 0 := by
        have h := congrArg (ιk.comp (residue W)) hqW
        rw [map_natCast, map_zero] at h
        refine (map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_
        rw [map_natCast]
        exact h
      have : CharP κ q := (CharP.charP_iff_prime_eq_zero hqp).2 hqκ
      have hpq : p = q := ringChar.eq κ q
      have hp : p ≠ 0 := hpq ▸ hqp.ne_zero
      apply hψf
      have hc : c = (q : PowerSeries O) := by simp only [c, if_neg hp, hpq]
      show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0
      rw [hc, map_mul, map_natCast, hqW, mul_zero]
    · subst hq0
      exact CharP.charP_to_charZero W
  let a : Sp W ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩
  · have h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O := IsLocalRing.comap_closedPoint ψ'
    show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · have ht : (jK W) t = (⊥ : PrimeSpectrum W) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    have hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O)) := by
      show f₀ ∉ Ideal.comap ψ' ⊥
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact hψ'f₀
    have := hf hm
    simp only [a, Scheme.Hom.comp_apply, ht]
    exact this

theorem exists_trait_cen : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o']
    [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty →
    ∀ (X : Scheme.{0}) (u₀ : U₀.toScheme ⟶ X) (u : X ⟶ F.X) (x : M.Z), IsClosed ({x} : Set M.Z) →
      ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ u T ξ ∧ ξ (IsLocalRing.closedPoint T.V) = x := by
  intro g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [hy, Category.assoc]
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.Poinc.TraitCen
