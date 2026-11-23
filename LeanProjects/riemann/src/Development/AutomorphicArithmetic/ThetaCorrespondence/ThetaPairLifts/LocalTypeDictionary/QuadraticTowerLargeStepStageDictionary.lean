import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGoodGeometryOverCarriedFrames
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BaseSplitPrimeInLocalPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactorStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
theorem quadratic_tower_large_step_stage_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  intro hP hK hM
  refine GlobalTheory.SqStepBig.gbig_two (_root_.GlobalTheory.T.exists_good_geometry_over_carried_frames hP) (_root_.GlobalTheory.T.pivot_reduction_divisibility hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hψ i j p q A A' WW X lam t Bs hX hF hB
  obtain ⟨FA, FA', FW, Γ, hO, hp, hq, hg, hs⟩ := q1 W hψ i j p q A A' WW X lam t Bs hX hF hB
  refine ⟨Γ, hO, hp, hq, hg, ?_⟩
  intro R om om' Rf om₀ om₀' Rf₀ c c₀ m1 m0 k1 k0
  obtain ⟨h0, Pim, pp, pp', J, hsurj, hJ, hi, hI, hI', P', hP'0, hi'⟩ := id hF
  obtain ⟨P, k, H⟩ := q2 W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P'
    (fun s _ h => hi' s h)
  have key : ∀ s, (s = t ∨ s = μ₀) → ∀ om om' Rf (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
      ((((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * lam s) • pp P) = c • pp' P' := by
    intro s hs' om om' Rf c m kc
    apply hJ s
    rw [map_smul, map_smul, mul_smul, ← hI, ← hI' s P' (hi' s)]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact H s hs' om om' Rf c m kc h
  have e1 := key t (Or.inl rfl) om om' Rf c m1 k1
  have e0 := key μ₀ (Or.inr rfl) om₀ om₀' Rf₀ c₀ m0 k0
  have e2 : ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P' =
      ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := by
    calc ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P'
        = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • (c • pp' P') := mul_smul _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • pp P) := by
          rw [e1]
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • pp P) :=
          smul_comm _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • (c₀ • pp' P') := by rw [e0]
      _ = ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := (mul_smul _ _ _).symm
  have e3 := sub_eq_zero.2 e2
  rw [← sub_smul] at e3
  have hz := (smul_eq_zero.1 e3).resolve_right hP'0
  have hn : (((GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  refine ⟨k, ?_⟩
  rw [Circle.coe_div, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination hz
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_fit_factor_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  first | exact @_root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | exact _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | (intros; apply _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary <;> assumption)
end
