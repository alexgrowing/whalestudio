import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol GlobalTheory.DeRhamSymbolBasis

theorem colHT_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI J K LL m r' u k hu g hg
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply, colHT, Matrix.of_apply]
  set M := (r' g : Matrix (Fin m) (Fin m) ↥LL.1) with hM
  set t : P.R.BdR := ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) with ht
  set q : ℚ_[l] := ((P.χQ (g : GQ l) ^ k i : ℚ_[l]ˣ) : ℚ_[l]) with hq
  have key : ∀ x, t * u i x ∈ (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i x))
  have hmem : ∀ x, algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x) ∈
      (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
    exact om_mul_mem _ (act_mem _ (key x))
  have h1 := congrFun (hg i) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, embF_apply] at h1
  have h2 : t * u i j = ∑ x, algebraMap (Om l) P.R.BdR ((M j x : ↥LL.1) : Om l) *
      (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) := by
    conv_lhs => rw [← h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, shift_act]
  have h3 : ∀ x, J.θ (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) =
      (q : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR,
      J.θ_mul _ (om_mem _) _ (act_mem _ (key x)), J.θ_Om, J.θ_act _ _ (key x),
      GlobalTheory.MemLoc.TiedTheta.actC_eq]
  have hunit : (q : ℂ_[l]) * ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    have e : q * (((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
      rw [hq, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    have e2 := congrArg (fun z : ℚ_[l] => (z : ℂ_[l])) e
    rw [map_mul, UniformSpace.Completion.coe_mul, map_one, UniformSpace.Completion.coe_one] at e2
    exact e2
  rw [h2, theta_comb J _ _ hmem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h3]
  linear_combination (-((((M j x : ↥LL.1) : Om l) : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)))) * hunit

end GlobalTheory.HTBasis
