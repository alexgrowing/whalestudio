import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.SecComb

theorem equiv_sum {K M J : Type} [CommRing K] [AddCommGroup M] [Module K M] [Fintype J] (ρ : M ≃ₗ[K] M)
    (c : J → K) (v w : J → M) (h : ∀ i, ρ (v i) = w i) : ρ (∑ i, c i • v i) = ∑ i, c i • w i := by
  simp only [map_sum, map_smul, h]

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

omit [IsDomain R] in
theorem ofSec_inj {t t' : SecA A F k}
    (h : (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) = SecM.ofSec A.A t') : t = t' := by
  have h' : t.f = t'.f := congrArg Subtype.val h
  cases t; cases t'; cases h'; rfl

theorem isComb_iff {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) :
    IsComb A s b t ↔ (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) =
      ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
  have e : ∀ j, ((∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)).1 j) =
      ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun H => Subtype.ext (funext fun j => (H j).trans (e j).symm),
    fun H j => (congrFun (congrArg Subtype.val H) j).trans (e j)⟩

omit [IsDomain R] in
theorem exists_rho (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ ρ : SecM A.A A.L (k : ℤ) (TFK (R := R) F) ≃ₗ[Γ((TFK (R := R) F).left, ⊤)]
      SecM A.A A.L (k : ℤ) (TFK (R := R) F), ∀ s s' : SecA A F k,
      IsActOf A.A A.L k θ s s' ↔ ρ (SecM.ofSec A.A s) = SecM.ofSec A.A s' := by
  have hL := A.isLB
  obtain ⟨ρ, hρ⟩ := ThetaAct.exists_equiv hL θ
  refine ⟨ρ, fun s s' => ?_⟩
  rw [ThetaAct.isActOf_iff hL]
  exact ⟨fun H => ThetaAct.sv_ext hL fun y J hJ => (hρ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ hJ⟩

end GlobalTheory.SecComb

namespace GlobalTheory

open SecComb in

theorem secComb_thetaAct : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  intro R _ _ A F _ _ k J _ s b
  refine ⟨⟨SecM.toSec A.A (∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)),
    (isComb_iff A _ _ _).2 rfl⟩, fun t t' h h' => ?_, fun θ s' t t' hs h => ?_, fun θ t => ?_,
    fun I _ M r a t hr h => ?_⟩
  · exact ofSec_inj A (((isComb_iff A _ _ _).1 h).trans ((isComb_iff A _ _ _).1 h').symm)
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    have e := (congrArg ρ ((isComb_iff A _ _ _).1 h)).trans
      (equiv_sum ρ (fun l => cF R (b l)) _ _ fun i => (hρ _ _).1 (hs i))
    exact ⟨fun H => (isComb_iff A _ _ _).2 (((hρ _ _).1 H).symm.trans e),
      fun H => (hρ _ _).2 (e.trans ((isComb_iff A _ _ _).1 H).symm)⟩
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    refine ⟨SecM.toSec A.A (ρ (SecM.ofSec A.A t)), (hρ _ _).2 rfl, fun t' h => ofSec_inj A ?_⟩
    exact ((hρ _ _).1 h).symm
  · rw [isComb_iff] at h ⊢
    rw [h]
    simp only [fun i => (isComb_iff A _ _ _).1 (hr i), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have e : cF R (∑ i, M i j * a i) = ∑ i, cF R (M i j * a i) := map_sum _ _ _
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_comm _ _).trans (map_mul _ _ _).symm

end GlobalTheory
