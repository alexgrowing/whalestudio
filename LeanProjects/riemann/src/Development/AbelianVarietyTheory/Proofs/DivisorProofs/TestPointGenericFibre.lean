import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_base_generic : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ φ : V →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧ yb ≫ s = Spec.map (CommRingCat.ofHom φ) ∧ ∃ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb := by
  intro F _ _ V _ p _ hp X s Xw _ yb _

  obtain ⟨φ, hφ⟩ : ∃ φ : V →+* 𝓞_ℂ_[p], yb ≫ s = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage (yb ≫ s)).hom, (Spec.map_preimage (yb ≫ s)).symm⟩

  have hpV0 : ((p : V) : F) ≠ 0 := by
    push_cast; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := (V.valuation_eq_one_iff (p : V)).1 hu
    have h2 := (V.mem_nonunits_iff).1 hp
    have : ((p : V) : F) = (p : F) := by push_cast; rfl
    rw [this] at h1
    exact (ne_of_lt h2) h1
  have hpV0' : (p : V) ≠ 0 := fun h => hpV0 (by rw [h]; rfl)
  have hφp : φ (p : V) = (p : 𝓞_ℂ_[p]) := map_natCast φ p
  have hpO : ¬ IsUnit (p : 𝓞_ℂ_[p]) := Formalism.BasicNotions.Loc.OC_l_not_unit p
  have hpO0 : (p : 𝓞_ℂ_[p]) ≠ 0 := by
    intro h
    have : ((p : 𝓞_ℂ_[p]) : ℂ_[p]) = 0 := by rw [h]; rfl
    push_cast at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)

  have hmax : ∀ P : Ideal V, P.IsPrime → P ≠ ⊥ → P = IsLocalRing.maximalIdeal V := fun P hP hne =>
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hne)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    by_contra hne
    push_neg at hne
    obtain ⟨a, ha, ha0⟩ := hne
    have hker : RingHom.ker φ ≠ ⊥ := fun h => ha0 (by
      have : a ∈ RingHom.ker φ := ha
      rw [h] at this; exact this)
    have := hmax _ (RingHom.ker_isPrime φ) hker
    have hp' : (p : V) ∈ RingHom.ker φ := this ▸ hpV
    exact hpO0 (hφp ▸ hp')
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hP := hmax (Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p])) (Ideal.comap_isPrime _ _) (by
      intro h
      have : (p : V) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
        rw [Ideal.mem_comap, hφp, IsLocalRing.mem_maximalIdeal]; exact hpO
      rw [h, Ideal.mem_bot] at this
      exact hpV0' this)
    have : a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
      rw [hP, IsLocalRing.mem_maximalIdeal]; exact hna
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] at this
    exact this ha
  refine ⟨φ, hinj, hloc, hφ, ?_⟩

  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (FaithfulSMul.algebraMap_injective _ _).comp hinj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FractionRing V →+* ℂ_[p],
      ψ.comp (algebraMap V (FractionRing V)) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing V) hg,
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := FractionRing V) hg x⟩
  have w : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb) ≫ s =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hψ]
  let y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s := pullback.lift _ _ w
  refine ⟨y, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι
  exact pullback.lift_fst _ _ w

end GlobalTheory.FlatModel
