import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
namespace ResidueCardinalityNilpotence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.CompanionTheory.ResCardPlace
end GlobalTheory.CompanionTheory.ResCardPlace
end
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
noncomputable section
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
section Unip
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Unip
section Sym
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
end Sym
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
section Root
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Root
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
open Formalism.BasicNotions Formalism.L2.DIV IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Place
variable {D : D7}
end Place
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.DivisionValues (vw lw)
open IsDedekindDomain NumberField
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Val
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Factors
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
end Factors
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Coef
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
end Coef
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Loss
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
end Loss
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.L2.DIV
theorem finCoefK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  have hL := s.core.lev
  have hde := Test.pde_ne_q s
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : 1 ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    omega
  refine ⟨dlF ch.G, loss_dlF ch.G hC hb hf, fun t w hA Φ β hβ => ?_⟩
  have hq := coef_QL hL ch.S.toGridChoice t Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard t) hA hβ
  refine ⟨((∏ v, (ch.S.term t Φ β v).coef : ℚ) : D.what₂.LL), ?_, ?_⟩
  · rw [map_ratCast]
    push_cast
    rfl
  · rcases hq with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h
end GlobalTheory.CompanionTheory.VolVal
end
end
end ResidueCardinalityNilpotence
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := by
  first | exact @_root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt | exact _root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt | (intros; apply _root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt <;> assumption)
end
end
