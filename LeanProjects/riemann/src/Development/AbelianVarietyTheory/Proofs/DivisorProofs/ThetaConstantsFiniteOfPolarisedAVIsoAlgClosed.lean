import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

noncomputable section

namespace GlobalTheory.ThetaFiniteIso

theorem thetaPts_finite : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  intro G N' J K _ _ b Q ho _
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ ho.pos.ne'⟩
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let T₀ : Over (Sp K) := Over.mk (T.hom ≫ 𝟙 (Sp K))
  let fn : K → Γ(T.left, ⊤) := fun c => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c
  let Tor := {y : T₀ ⟶ Q.A // y ^ (N' ^ 2) = 1}
  have e : T₀ ≅ 𝟙_ (Over (Sp K)) :=
    (CartesianMonoidalCategory.isTerminalTensorUnit).uniqueUpToIso
      (IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom (by simp [T₀, T]))
        (fun Y m => Over.OverMorphism.ext (by simpa [T₀, T] using Over.w m))) |>.symm
  haveI hTor : Finite Tor := by
    have := GlobalTheory.AbTorsionFinite.finite_torsion K Q.A Q.isAb (N' ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ ho.pos.ne'))
    refine Finite.of_injective (fun y : Tor => (⟨e.inv ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩ :
      {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q.A // x ^ (N' ^ 2) = 1})) ?_
    intro y y' h
    exact Subtype.ext ((cancel_epi e.inv).1 (congrArg Subtype.val h))
  let ch : (Ix G (N' ^ 2) → Tor) → (Ix G (N' ^ 2) → K) := fun l =>
    if h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) then h.choose else 0
  refine ⟨Set.range ch, Set.finite_range ch, fun t ⟨φ, hφ, hw⟩ => ?_⟩
  haveI := hφ
  let x : Ix G (N' ^ 2) → (T ⟶ t.pol.A) := fun a => (Over.homMk (𝟙 (Sp K)) (by simp [T]) : T ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hk : ∀ a, x a ^ (N' ^ 2) = 1 := fun a => by
    exact (MonObj.comp_pow _ _ _).symm.trans ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t a)).trans (MonObj.comp_one _))
  let x₀ : Ix G (N' ^ 2) → (T₀ ⟶ Q.A) := fun a => Over.homMk ((x a).left ≫ φ.hom.left) (by
    exact (Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) (Over.w φ.hom)).trans
      ((Over.w (x a)).trans (Category.comp_id _).symm)))
  have hx : ∀ a, (x₀ a).left = (x a).left ≫ φ.hom.left := fun a => rfl
  have hp : IsGrpPullback t.pol.A Q.A (𝟙 (Sp K)) φ.hom.left := isGrpPullback_of_iso φ
  have key : ∀ v : Ix G (N' ^ 2) → K, t.HasTh (𝟙 _) v ↔ IsThetaPt Q N' x₀ (fun a => fn (v a)) := fun v =>
    GlobalTheory.ThetaPtUp.isThetaPt_iff (P := t.pol) (P₀ := Q) (T := T) hp hw hx hk _
  let r : T₀ ⟶ T := Over.homMk (𝟙 (Sp K)) (by simp [T₀, T])
  have hk₀ : ∀ a, x₀ a ^ (N' ^ 2) = 1 := fun a => by
    have e₁ : x₀ a = r ≫ x a ≫ φ.hom := Over.OverMorphism.ext (Category.id_comp _).symm
    have h2 : (x a ≫ φ.hom) ^ (N' ^ 2) = 1 := by
      have := map_pow (IsMonHom.monoidHom φ.hom T) (x a) (N' ^ 2)
      have h1 : IsMonHom.monoidHom φ.hom T (x a ^ (N' ^ 2)) = 1 := by
        erw [hk a]; exact map_one _
      exact this.symm.trans h1
    rw [e₁, ← MonObj.comp_pow, h2, MonObj.comp_one]
  let l : Ix G (N' ^ 2) → Tor := fun a => ⟨x₀ a, hk₀ a⟩
  obtain ⟨v, hv⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 ho t K (𝟙 _)
  have h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) := ⟨v, (key v).1 hv⟩
  refine ⟨ch l, ⟨l, rfl⟩, (key _).2 ?_⟩
  simp only [ch, dif_pos h]
  exact h.choose_spec

end GlobalTheory.ThetaFiniteIso

end
