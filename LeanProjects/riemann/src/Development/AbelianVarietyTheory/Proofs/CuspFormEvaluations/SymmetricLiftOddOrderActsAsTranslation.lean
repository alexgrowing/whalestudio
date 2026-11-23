import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacterStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaConstantOfThetaGroupStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingOfThetaGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstSymmetricSquareEqOneStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstantPowEqOneOfPowerTrivialStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem rd_fock_of_symLift : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  intro S A _ _ L x0 g Φ hχ k n U x δ s s' θ hn hδ hnx hU hact hrd

  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_thetaConstant_of_thetaGroup S A L x0 g Φ k U x hU.1
  have hread := GlobalTheory.T.reading_of_thetaGroup_action S A L x0 g Φ k U x c s s' θ hc hact hrd

  have hsq : c ^ 2 = 1 := GlobalTheory.T.thetaConst_symmetric_square_eq_one S A L x0 g Φ k U x c hc hU.3

  have hmem : (n : ℂ) • x ∈ Φ.lat := by
    rw [hnx, two_smul]
    exact add_mem hδ hδ
  have hχδ : Φ.χ ((2 : ℂ) • δ) = 1 := (GlobalTheory.T.appellHumbert_frame_semicharacter S A L x0 g Φ).2.2 hχ δ hδ
  have hpow := GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial S A L x0 g Φ k n U x c hc hmem hU.2
  rw [hnx, hχδ, one_zpow, _root_.mul_one] at hpow

  have hc1 : c = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, hsq, one_pow, _root_.one_mul] at hpow
    exact hpow
  subst hc1
  simpa only [_root_.one_mul] using hread

end GlobalTheory.AnVal
