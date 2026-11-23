import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntegralShift

theorem trF_prB {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) :
    (DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R)).left =
      (DegPre.prB Q (FractionRing R)).left ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left := by
  rw [← Over.comp_left]
  congr 1
  have e₁ : DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R) =
      DegPre.prB Q (FractionRing R) * (toUnit _ ≫ Q.c y) := lift_snd _ _
  have e₂ : (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]) = (toUnit Q.P.A ≫ Q.c y) * 𝟙 Q.P.A := rfl
  rw [e₁, e₂, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (DegPre.prB Q (FractionRing R) ≫ toUnit _) (toUnit _), mul_comm]

theorem sval_constFn_smul {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R) (s : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (constFn p ⊤ a • s) r z J =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval s r z J := by
  have hm := hJ.mem φ r
  refine (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans ((GlobalTheory.HeatMod.gs_constFn_eq_germConstHom p r z a).trans ?_)) rfl)
  exact (gs_eq (r ≫ p) z ⊤ trivial _).symm

theorem exists_shift_of_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  intro R _ _ Q y N c uR huR H
  have ex : ∀ x : Q.SecB N 0, ∃ s₁ : Q.SecB N (0 + N • y),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Q.P.A.left) (z : Z) (J), Good Q.P.L z J →
        sval s₁ r z J = sval x (r ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left) z J *
          (val uR r z J).val := fun x => by
    obtain ⟨s₁, h⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (0 + N • y)) (ε' := DegPre.famε N) (fun U _ h => by
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left uR huR)
    exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩
  choose Sh hSh using ex
  refine ⟨fun z J => val uR (𝟙 _) z J, Sh, fun x => ⟨fun z J hJ => ?_, constFn Q.P.A.hom ⊤ c • Sh x, ?_,
    fun Z X z J hJ => sval_constFn_smul _ _ _ _ _ hJ⟩⟩
  · rw [hSh x _ _ z J hJ, Category.id_comp]
  · intro u hu hc z J hJ
    rw [GlobalTheory.HeatMod.gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero, sval_constFn_smul _ _ _ _ _ hJ,
      hSh x _ _ z J hJ, H u hu hc z J hJ, trF_prB]
    ring

end GlobalTheory.IntegralShift
