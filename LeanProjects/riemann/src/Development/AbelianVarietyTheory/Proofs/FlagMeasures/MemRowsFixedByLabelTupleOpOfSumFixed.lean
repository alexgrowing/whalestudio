import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffChosenRedEqRedHom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ESSingleCoeffCentral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvUniqueAddSmulMulComm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCoeff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabFix

theorem mem_VT_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  intro D X red sec hred hsec t ht f hf hsum
  classical
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  let ρ : GlobalTheory.RowLev.Red X.B.I X.B.g (G0g D.nd) :=
    { toFun := red, map_mul := hred.2.1, ker := hred.2.2.2, surj := hred.2.2.1 }
  obtain ⟨hcoef, hcent⟩ := GlobalTheory.LabIdem.ES_single_coeff_central D t ht
  have hegA : egA X (ES {t}) = ρ.lift X.B.μf (ES {t}) := by
    funext x
    rw [egA, GlobalTheory.coeff_chosenRed_eq_redHom D X red hred _ hcent x]
    by_cases hx : x ∈ X.B.I.Kset
    · rw [if_pos hx, GlobalTheory.RowLev.Red.lift_of_mem ρ _ _ hx]
    · rw [if_neg hx, GlobalTheory.RowLev.Red.lift_of_notMem ρ _ _ hx]
  obtain ⟨h1R, hm, hn, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  obtain ⟨huniq, -, -, hprod, -⟩ := GlobalTheory.WeakConv.rightConv_unique_add_smul_mul_comm X.B.I X.B.μf X.B.fund X.B.R
    X.B.fund_spec X.B.R_spec
  obtain ⟨hQ, -, -, -, -, hinfl, -, -, -⟩ := GlobalTheory.InflBasic.inflation_basic X.B.I X.B.g (G0g D.nd) ρ X.B.μf hg
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨hlint, hlloc, -⟩ := hinfl (ES {t})
  obtain ⟨Ta, hTa⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R
    X.B.R_spec).1 _ hlint
  have he := X.B.e_adm
  have hecont : Continuous X.B.e := he.1.continuous
  have hReRe : X.B.Re.comp X.B.Re = X.B.Re := by
    have h := hprod _ _ _ _ hecont hecont X.B.Re_spec X.B.Re_spec
    rw [he.2.1] at h
    exact huniq _ _ _ h X.B.Re_spec
  have hRT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) (X.B.Re.comp Ta) := by
    unfold eT
    rw [hegA]
    exact hprod _ _ _ _ hecont hlloc.continuous X.B.Re_spec hTa
  have hReT : ReT X {t} = X.B.Re.comp Ta := by
    have hex : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) T := ⟨_, hRT⟩
    unfold ReT
    rw [dif_pos hex]
    exact huniq _ _ _ (Classical.choose_spec hex) hRT
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hf
  have hRef : X.B.Re f = f := by
    rw [← hz]
    show X.B.Re (X.B.Re (X.Rph z)) = X.B.Re (X.Rph z)
    rw [← ContinuousLinearMap.comp_apply X.B.Re X.B.Re, hReRe]
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := h1R
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b
    rw [ContinuousLinearMap.mul_def, ← hm]
    simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => hn _ v
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, X.B.I.Lf.zero_mem, ?_⟩⟩
    have : X.B.I.fmat 1 = 1 := rfl
    simp [this]
  haveI : SecondCountableTopology X.B.I.Gf := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints X.B.I
  have hfix : ∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) f = f := by
    intro k hk
    have h := GlobalTheory.IdemProj.op_fixed X.B.μf (fun g => X.B.R (1, g)) p1 pm pn X.B.e X.B.Re X.B.Re_spec.2 k
      (fun x => by simpa using he.2.2.2.2.2.1 x k hk 1 hone)
    rw [← hRef, ← ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun h f
  have hTaf : Ta f = f := by
    apply ext_inner_left ℂ
    intro v
    rw [hTa.2, GlobalTheory.LevelIdem.integral_lift ρ X.B.μf hg (ES {t}) sec hsec (fun x => ⟪v, X.B.R (1, x) f⟫_ℂ) ?_]
    · conv_rhs => rw [← hsum]
      rw [finsum_eq_sum_of_fintype, inner_sum]
      simp only [inner_smul_right, hcoef]
    · intro x k hk
      show ⟪v, X.B.R (1, x * k) f⟫_ℂ = ⟪v, X.B.R (1, x) f⟫_ℂ
      rw [show ((1 : X.B.I.Ginf), x * k) = ((1, x) : X.B.I.GA) * (1, k) by simp, hm,
        ContinuousLinearMap.comp_apply, hfix k hk]
  refine Submodule.mem_inf.2 ⟨hf, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  show ReT X {t} f = f
  rw [hReT, ContinuousLinearMap.comp_apply, hTaf, hRef]

end GlobalTheory.LabFix
