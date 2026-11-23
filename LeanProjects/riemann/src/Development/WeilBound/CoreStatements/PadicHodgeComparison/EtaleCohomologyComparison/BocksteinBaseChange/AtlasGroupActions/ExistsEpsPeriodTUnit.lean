import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import GroundTheory.PAdicHodge.FontaineLemmaPeriod

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.GlueBE

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_epsilon : IsUnit (epsilon l : Ob l) := by
  have h := (AInf.isUnit_teichmuller_of_untilt_eq_one (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))).map
    (WittVector.constantCoeff (p := l) (R := Ob l))
  rwa [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h

def eU (k : ℕ) : (Ob l)ˣ :=
  (Units.map ((frobeniusEquiv (Ob l) l).symm : Ob l →+* Ob l).toMonoidHom)^[k] (isUnit_epsilon l).unit

theorem eU_succ (k : ℕ) : eU l (k + 1) = Units.map ((frobeniusEquiv (Ob l) l).symm : Ob l →+* Ob l).toMonoidHom (eU l k) := by
  rw [eU, Function.iterate_succ_apply']
  rfl

theorem eU_zero : (eU l 0 : Ob l) = epsilon l := rfl

theorem eU_one : (eU l 1 : Ob l) = (frobeniusEquiv (Ob l) l).symm (epsilon l) := rfl

def eps : B.Eps l where
  e := eU l
  succ k := by
    ext
    rw [eU_succ, Units.val_pow_eq_pow_val, Units.coe_map]
    exact (frobenius_apply_frobeniusEquiv_symm (Ob l) l _)
  one := by
    rw [eU_zero, WittVector.fontaineTheta_teichmuller]
    exact untilt_epsilon
  prim := by
    rw [eU_one, WittVector.fontaineTheta_teichmuller]
    exact untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem eps_μ : (eps l).μ = algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (AInf.mu (epsilon l)) := by
  rw [B.Eps.μ, B.Eps.qk, AInf.mu, map_sub, map_one]
  rfl

theorem exists_eps_period_t_unit (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : ∃ ε : B.Eps l, ∃ u : (per l K).A, IsUnit u ∧ (per l K).t = (show (per l K).A from ε.μ) * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨eps l, u, hu, by rw [eps_μ]; exact e⟩

end CrystallineSemistableComparison.GlueBE
