import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem polyDeriv_comp_linear_equiv {σ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (P : MvPolynomial σ ℂ) (u : σ → V)
    (G : W → ℂ) (x : V) :
    I2.polyDeriv P u (fun z => G (e z)) x = I2.polyDeriv P (fun ℓ => e (u ℓ)) G (e x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := e.iteratedFDerivWithin_comp_right G (s := Set.univ) uniqueDiffOn_univ (x := x)
    (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' : (fun z => G (e z)) = G ∘ e := rfl
  rw [h', h]
  rfl

theorem lintor_hf_neg_right {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf v (-w) = -I2.Hf v w := by
  simp [I2.Hf]

theorem lintor_hf_neg_left {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf (-v) w = -I2.Hf v w := by
  simp [I2.Hf]

theorem polyDeriv_prod_fock_eq_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (g : ℕ) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp X.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ), (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) → Differentiable ℂ θ → ∀ (n N : ℕ) (a : Fin n → Fin g → ℂ) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → Fin g → ℂ), I2.polyDeriv P u (fun z => ∏ b, fock Hm ((N : ℤ) ^ 2) (a b) (fun w => θ ((N : ℂ) • w)) (z b)) 0 = I2.polyDeriv P (fun ℓ b => ψ (u ℓ b)) (X.U (N ^ 2) (fun b => -ψ (a b)) (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0 := by
  intro E _ _ _ X g ψ Hm θ hH _ n N a Io P u
  let e : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp X.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  have he : ∀ z, e z = fun b => ψ (z b) := fun _ => rfl
  have key := polyDeriv_comp_linear_equiv e P u (X.U (N ^ 2) (fun b => -ψ (a b))
    (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0
  rw [map_zero] at key
  refine Eq.trans ?_ key
  congr 1
  funext z
  rw [he]
  simp only [fock, I2.PT.U, I2.s0, I2.HC, lintor_hf_neg_right, lintor_hf_neg_left, hH, neg_neg,
    Finset.prod_mul_distrib, ← Complex.exp_sum, Pi.sub_apply, sub_neg_eq_add,
    LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, mul_neg]
  push_cast
  rfl

end GlobalTheory.AnVal
