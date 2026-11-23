import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.FODef

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem sqZero : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0 := by
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Submodule.mem_bot]
  ext
  · simp [hr, hs]
  · simp [hr, hs]

theorem constMorV (A₀ : Over (Sp k)) [GrpObj A₀] :
    GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
      congr 1) (𝟙 A₀)

variable {k V}

def IsFilLiftV {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (TrivSqZeroExt k V))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) i)
    (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) : Prop :=
  ∃ d ∈ liftFil (divided₂ (sqZero k V)) h, ∀ c : primDR A₀,
    d ((constMorV k V A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c)

end GlobalTheory.FODef

namespace GlobalTheory.HTUniv

theorem coord {k : Type} [Field k] {d : ℕ} (c : (Fin d → k) →ₗ[k] k) (v : Fin d → k) :
    c v = ∑ j, v j * c (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • (Pi.single j (1 : k) : Fin d → k) := by
    ext i; simp [Pi.single_apply]
  rw [e, map_smul, smul_eq_mul]

theorem comp_pi {k : Type} [Field k] {d : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (c : (Fin d → k) →ₗ[k] k) (y : Fin d → (P →ₗ[k] k)) :
    c ∘ₗ LinearMap.pi y = ∑ j, c (Pi.single j 1) • y j := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_apply, coord c, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply, smul_eq_mul, mul_comm]

theorem sum_proj_single {k : Type} [Field k] {d : ℕ} (c₀ : Fin d → k) (j : Fin d) :
    (∑ i, c₀ i • LinearMap.proj (R := k) (φ := fun _ : Fin d => k) i) (Pi.single j 1) = c₀ j := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try exact mul_one _

end GlobalTheory.HTUniv
