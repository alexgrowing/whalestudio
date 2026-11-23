import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFac

theorem formEq_empty_dε {X Y : Scheme.{0}} (φ φ' : Fin 5 → (Y ⟶ X)) (e : φ' = φ) (n j : ℤ) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (Sum.elim φ φ') (dε n j) := by
  subst e
  intro U _ h
  simp only [dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]

theorem val_tau_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult)
    (z : (TF (R := R) (FractionRing R)).left) (J) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (jFK (R := R) (FractionRing R)) z J = 1 ∧
      val (D.psi 0) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J = 1 := by
  have C : IsCub (DVR.th D (T := TF (R := R) (FractionRing R)) z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hτ := DVR.tau_mul (𝟙 (TF (R := R) (FractionRing R))) hJ hB 0 0 0
  have hψ := DVR.UUA.psi_add (𝟙 (TF (R := R) (FractionRing R))) hJ (0 : D.X) 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.psi a) r z J = val (D.psi b) r z J := by rintro a b rfl r; rfl
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ
  have t00 := (mul_left_cancel hτ).symm
  rw [hpp _ _ z0, t00, _root_.one_mul] at hψ
  rw [Over.id_left, Category.id_comp] at t00 hψ
  refine ⟨t00, mul_left_cancel (a := val (D.psi 0) (jFK (R := R) (FractionRing R)) z J) ?_⟩
  rw [_root_.mul_one, ← _root_.mul_assoc]
  exact hψ.symm

theorem trel_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (s₀ : SecT D.toPre a N (-1) 0) (s' : SecT D.toPre a N (-1) (shift h h' N (-1) 0)), (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval s' x z J = sval s₀ x z J) → TRel h 0 s₀ s' := by
  intro R _ _ _ hR D a a' h h' hE N _ s₀
  have hs : shift h h' N (-1) 0 = 0 := by simp [shift]
  generalize shift h h' N (-1) 0 = β' at hs
  subst hs
  intro s' hv u hu Z x z J hJ
  have hL := D.toPre.P.isLB
  have htr : (DegPre.trF D.toPre (FractionRing R) 0).left = 𝟙 _ := by rw [DVR.UUA.trF_zero, Over.id_left]
  have hc0 : D.toPre.c 0 = 1 := by
    have h := D.toPre.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hp : padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) = 𝟙 _ := by
    rw [hc0, MonObj.comp_one]
    exact _root_.mul_one (𝟙 D.toPre.P.A)
  obtain ⟨u₀, hu₀, -⟩ := exists_gen hL (formEq_empty_dε (tφ D.toPre a 0)
    (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).left ≫ tφ D.toPre a 0 k)
    (funext fun k => by rw [hp, Over.id_left, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  obtain ⟨u', hu', hv'⟩ := exists_gen hL (φ' := dφ D.toPre a 0 0 0) (formEq_empty_dε _ _
    (funext fun k => by rw [htr, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  have hf : IsFac D.toPre a h N (-1) 0 0 0 u' := by
    refine ⟨hu', fun y I hI => ?_⟩
    obtain ⟨t0, p0⟩ := val_tau_psi_zero D.tau_bimult y I hI
    have hh : val (D.toPre.psi (h 0)) (jFK (R := R) (FractionRing R)) y I =
        val (D.toPre.psi 0) (jFK (R := R) (FractionRing R)) y I :=
      congrArg (fun w => val (D.toPre.psi w) (jFK (R := R) (FractionRing R)) y I) (map_zero h)
    rw [hv' _ _ y I hI, val_one, hh, t0, _root_.mul_one, ← zpow_add, ← mul_zpow, p0, one_zpow]
  have key := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 N (-1) 0 0 0 u₀ hu₀).2.1 u u' hu hf Z x z J hJ
  rw [key, hv' _ _ z J hJ, val_one, htr, Category.id_comp, Units.val_one, _root_.mul_one]
  exact hv Z _ z J hJ

end GlobalTheory.TwFac
