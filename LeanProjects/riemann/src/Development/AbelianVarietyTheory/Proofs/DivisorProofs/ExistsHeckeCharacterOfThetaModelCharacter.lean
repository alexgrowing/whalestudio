import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeckeCharacterFinitePartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharRestrictsEtaPowOfSignStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar
variable {D : D7}

theorem coe_chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) (x : (AE D)ˣ) :
    ((chi c θ e x : Circle) : ℂ) = (((c.f (finY D x) : ℂˣ) : ℂ) *
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ c.n τ) ^ e := by
  rw [chi, MonoidHom.zpow_apply, Circle.coe_zpow, MonoidHom.mul_apply, Circle.coe_mul, coe_finChar, coe_infChar]

theorem exists_hecke_of_heckeU : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ), (e = 1 ∨ e = -1) →
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ N ∧ HasFinPart χ c e := by
  intro D N c e he
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : Continuous (chi c θ e) := by
    have h : ((chi c θ e : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (finChar c x * infChar θ c.n x) ^ e := by
      funext x; rw [chi, MonoidHom.zpow_apply, MonoidHom.mul_apply]
    rw [h]
    exact ((GlobalTheory.T.continuous_heckeCharacterFinitePart c).mul (continuous_infChar hθ c.n)).zpow e
  have haut : ∀ a : D.host.Eˣ, chi c θ e (Units.map (incA D).toMonoidHom a) = 1 := by
    intro a
    refine Circle.ext ?_
    rw [coe_chi, finY_incA]
    have h1 : ∀ τ, θ τ (infPart D ((Units.map (incA D).toMonoidHom a : (AE D)ˣ) : AE D)) = embT D τ (a : D.host.E) :=
      fun τ => GlobalTheory.FockCompare.comp_incA hθ τ _
    simp only [h1]
    rw [c.aut a, one_zpow, Circle.coe_one]
  refine ⟨chi c θ e, ⟨hcont, haut⟩, ?_, fun x y hxy => ?_⟩
  · refine GlobalTheory.T.heckeChar_restricts_eta_pow_of_sign D _ N ⟨hcont, haut⟩ (fun x y hy => Circle.ext ?_) θ hθ fun τ x h1 h2 h3 => ?_
    · rw [coe_chi, finY_mul_conj x y hy, c.norm, Units.val_one, one_mul, Circle.coe_one]
      have h4 : ∀ τ, θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ) = 1 := by
        intro τ
        have e1 : θ τ (infPart D (y : AE D)) = (Complex.normSq (θ τ (infPart D (x : AE D))) : ℂ) := by
          rw [hy, RingHom.map_mul, map_mul, GlobalTheory.FockCompare.comp_cA hθ, Complex.mul_conj]
        have hne : θ τ (infPart D (x : AE D)) ≠ 0 := by
          intro h0
          have := congrArg (fun z => θ τ (infPart D z)) (Units.mul_inv x)
          simp only [RingHom.map_mul, map_mul, h0, zero_mul, RingHom.map_one, map_one] at this
          exact zero_ne_one this
        have hp : 0 < Complex.normSq (θ τ (infPart D (x : AE D))) := Complex.normSq_pos.2 hne
        rw [e1, Complex.norm_real, Real.norm_of_nonneg hp.le]
        exact div_self (by exact_mod_cast hp.ne')
      simp only [h4, one_zpow, Finset.prod_const_one, one_zpow]
    · have hf : finY D x = 1 := Units.ext (by
        rw [coe_finY, h1, map_one, map_one, Units.val_one])
      rw [coe_chi, hf, map_one, Units.val_one, one_mul, Finset.prod_eq_single τ (fun τ' _ hτ' => by
        rw [h3 τ' hτ']; simp) (fun h => absurd (Finset.mem_univ τ) h), h2]
      have hn : (-1 : ℂ) / (‖(-1 : ℂ)‖ : ℂ) = -1 := by simp
      rw [hn, ← zpow_mul]
      obtain ⟨k, hk⟩ := c.par τ
      have hodd : Odd e := by rcases he with rfl | rfl <;> decide
      obtain ⟨j, hj⟩ := hodd
      have : c.n τ * e = (N : ℤ) + 2 * (k * e + j * (N : ℤ) - (N : ℤ) * 0) := by
        have : c.n τ = k + k + N := by linarith
        rw [this, hj]; ring
      rw [this, zpow_add₀ (by norm_num), zpow_mul, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, mul_one,
        zpow_natCast]
  · obtain ⟨h1, h2⟩ := hxy
    have hy : finY D x = y := Units.ext (by rw [coe_finY, h2, RingEquiv.symm_apply_apply])
    rw [coe_chi, hy, h1]
    simp only [map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one, mul_one]
    rw [Units.val_zpow_eq_zpow_val]

end GlobalTheory.HeckeUChar
