import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem tensorLift_mulByNatConvPower_comul_eq_succ {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (i : ℕ) (a : D) :
    (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul a) = mulBy R D (i + 1) a := by
  have h1 := comp_mulBy_pts (AlgHom.id R D) i
  have h2 := comp_mulBy_pts (AlgHom.id R D) (i + 1)
  rw [AlgHom.id_comp] at h1 h2
  have h3 : mulBy R D (i + 1) a = (toConv (AlgHom.id R D) ^ (i + 1)).ofConv a := DFunLike.congr_fun h2 a
  rw [h3, pow_succ]
  have h4 := AlgHom.convMul_apply (toConv (AlgHom.id R D) ^ i) (toConv (AlgHom.id R D)) a
  refine Eq.trans ?_ h4.symm
  rw [← h1]

theorem diagSum_cobOne_eq {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (m : ℕ) (a : D) :
    diagSum R D m (cobOne R D a) = mulBy R D m a - algebraMap R D (Coalgebra.counit a) - m • a := by
  induction m with
  | zero =>
    have h := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R D) 0) a
    rw [AlgHom.id_comp, pow_zero] at h
    have h' : mulBy R D 0 a = algebraMap R D (Coalgebra.counit a) := h
    simp [diagSum, h']
  | succ m ih =>
    have e : diagSum R D (m + 1) (cobOne R D a) = diagSum R D m (cobOne R D a) +
        (Algebra.TensorProduct.lift (mulBy R D m : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
          (cobOne R D a) := by
      simp [diagSum, Finset.sum_range_succ, LinearMap.add_apply]
    rw [e, ih, cobOne_apply, map_sub, map_sub, tensorLift_mulByNatConvPower_comul_eq_succ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_one, map_one, _root_.mul_one, _root_.one_mul, AlgHom.id_apply, succ_nsmul]
    have hc : ((mulBy R D m : D →ₐ[R] D) a) = mulBy R D m a := rfl
    rw [hc]
    abel

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.diagSum_cobOne_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ), (p : R) ^ N = 0 → ∀ a : G.A N, diagSum R (G.A N) (p ^ N) (cobOne R (G.A N) a) = 0 := by
  intro p R _ G N hN a
  rw [GlobalTheory.PtExt.diagSum_cobOne_eq, G.mulBy_pow_self N a, sub_self, zero_sub, neg_eq_zero,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]
