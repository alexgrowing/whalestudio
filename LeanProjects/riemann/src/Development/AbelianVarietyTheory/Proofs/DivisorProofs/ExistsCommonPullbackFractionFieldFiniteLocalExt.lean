import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.CommonCover

theorem exists_cover_field (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (K' : Type) [Field K']
    (io : FractionRing R →+* K') (hfin : io.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'),
      FinExt ρ ∧ IsLocalHom ρ ∧ τ.comp (io.comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  obtain ⟨⟨hN, -, hIC, hC⟩, hc0⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : Algebra.IsSeparable (FractionRing R) K' := inferInstance
  let C := integralClosure R K'
  haveI : Module.Finite R C := IsIntegralClosure.finite R (FractionRing R) K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension (FractionRing R) K'
  have hφ : Function.Injective (algebraMap R C) := fun a b h => by
    have h' : io (algebraMap R (FractionRing R) a) = io (algebraMap R (FractionRing R) b) := congrArg Subtype.val h
    exact IsFractionRing.injective R (FractionRing R) (io.injective h')
  obtain ⟨R', _, _, _, ρ, σ, hCN, hρ, hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) ⟨hN, hIC, hC, hc0⟩ hφ (RingHom.finite_algebraMap.2 inferInstance)
  have hσi : Function.Injective σ := by
    refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    rw [RingHom.comap_ker, hσ]
    exact (RingHom.injective_iff_ker_eq_bot ρ).1 hρ
  have hg : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσi
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, IsFractionRing.lift (A := C) hg,
    ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hρ, hfin'⟩, hloc, ?_⟩
  ext r
  have e : io (algebraMap R (FractionRing R) r) = algebraMap C K' (algebraMap R C r) := rfl
  simp only [RingHom.comp_apply]
  rw [e, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply σ, hσ]

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  intro R _ _ _ hR D₁ D₂ E₁ E₂ p₁ p₂ K' _ io E₃ hfin q₁ q₂
  obtain ⟨R', _, _, _, ρ, τ, hE, hloc, hτ⟩ := exists_cover_field R hR K' io hfin
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨E, t, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hL.polBaseChange K' (FractionRing R') τ E₃ ⊤
    (GlobalTheory.FieldPull.nonempty_psiOn_field E₃) trivial
  have ha : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hio : Function.Injective (io.comp (algebraMap R (FractionRing R))) := io.injective.comp ha
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, E, hE, hloc, ?_, ?_⟩
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₁ q₁
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₂ q₂
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t

end GlobalTheory.CommonCover
