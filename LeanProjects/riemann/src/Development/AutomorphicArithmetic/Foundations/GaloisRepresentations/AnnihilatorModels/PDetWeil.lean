import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL V : Type} [Field LL] [Algebra ℚ_[l] LL]
  [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem phiV_pow_tmul (n : ℕ) (v : V) (b : Bst P) :
    (phiV P LL V ^ n) (v ⊗ₜ[ℚ_[l]] b) = v ⊗ₜ[ℚ_[l]] (phiSt P ^ n) b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, phiV_tmul, ih, pow_succ, AlgHom.mul_apply]

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

private theorem coe_phiD_pow (n : ℕ) (x : ↥(Dpst P ρ)) :
    (((phiD P ρ ^ n) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n) (x : V ⊗[ℚ_[l]] Bst P) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, coe_phiD, pow_succ, Module.End.mul_apply]

private theorem stRep_phiV_pow (γ : ↥(GK K)) (n : ℕ) (y : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρ γ ((phiV P LL V ^ n) y) =
      AlgebraTensorModule.map (ρ γ) ((actSt P (γ : GQ l)).comp (phiSt P ^ n)).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [phiV_pow_tmul, stRep_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end

theorem UpperTheory.Gal.crystallineComparison.detWeil_of :
    WeilCo := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw LL V _ _ _ _ ρ _ g hg x
  have e : -alpha l g = (resDeg l w : ℤ) := by simp [alpha, hg]
  rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD,
    coe_phiD_pow, stRep_phiV_pow]
