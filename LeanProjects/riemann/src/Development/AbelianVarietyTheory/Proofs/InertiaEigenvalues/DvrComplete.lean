import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.FinExtIntegers

theorem dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro l _ LL
  unfold OL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsScalarTower ℤ_[l] ℚ_[l] ↥LL.1 := inferInstance
  have hfin : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : FaithfulSMul ℤ_[l] ↥LL.1 := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥LL.1
  have hdvr : IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥LL.1) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥LL.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥LL.1
  refine ⟨hdvr, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _, ?_⟩
  intro hu
  have hl : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  apply hl
  apply (isUnit_map_iff (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) _).mp
  simpa using hu

end GlobalTheory.FinExtIntegers
