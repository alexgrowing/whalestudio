import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem isCrys_transport {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have key := PI.CoefExt.finrank_iInf_ker_equiv
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)) (actVB PD ρ) (actVB PD ρ') (fun g x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul v c => simp [actVB, he])
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h]
  exact key

theorem isCrys_matrix_ext (f : LL →ₐ[Qp] LL') {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    IsCrys PD (CJ.rep ((f.mapMatrix : Matrix (Fin k) (Fin k) LL →ₐ[Qp]
      Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ))) := by
  letI : TopologicalSpace G := ⊥
  have h1 : IsCrys PD (CJ.rep ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)) := by
    refine isCrys_transport PD b.equivFun (fun g v => ?_) h
    change _ = (LinearMap.toMatrix b b (ρ g)).mulVec (b.repr v)
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  exact PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange PD f _ h1

end Gen

theorem isPotCrys_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb hT
  exact isCrys_matrix_ext (pc Pl h hN hF hS).PD' (incl hL) b ((pc Pl h hN hF hS).resH T.ρ) hT

end GlobalTheory.BaseCoef
