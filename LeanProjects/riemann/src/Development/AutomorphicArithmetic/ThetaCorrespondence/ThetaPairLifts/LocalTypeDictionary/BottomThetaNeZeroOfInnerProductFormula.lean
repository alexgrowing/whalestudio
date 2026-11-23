import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomNonvanishingFromInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaSmallRank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomBasisChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomNonvanishingFromInputsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula
set_option maxHeartbeats 4000000 in
theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hA := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hB' := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hC := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hR := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine GlobalTheory.SqTop.BotConstPf.gBig_imp (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hL hB)
    (GlobalTheory.SqTop.Model.gBig_and hN hT)) (GlobalTheory.SqTop.Model.gBig_and hA (GlobalTheory.SqTop.Model.gBig_and hB' (GlobalTheory.SqTop.Model.gBig_and hC hR)))) ?_
  intro D T Lc sc G μ₀ C x b hLc ⟨⟨⟨l1, l2⟩, l3, l5⟩, a1, a2, a3, a4⟩
  intro δ t0 Q P P' i j hbot
  have hmod : modT G μ₀ = SqNum.condE G.pl := by simp [modT, l2.2.1]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (l1 i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨Aa, hAa, hAn⟩ := l3 δ t0 i j
  have hP : P.norm ≠ 0 := by
    intro h0'
    have e := hAn μ₀ Q P P' Λ hbot hΛ
    rw [h0', Complex.ofReal_zero] at e
    refine mul_ne_zero hAa (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
    rw [Finset.mem_Icc] at hs
    exact hnz s hs.1 (hs.2.trans hh)
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  refine ⟨⟨h, Tt, hne⟩, ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := l5 W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := a4 W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := a1 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := a2 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := a3 W hψW i j A A' WW X _ hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    refine Finset.sum_eq_zero fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  first | exact @_root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | (intros; apply _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula <;> assumption)
end
