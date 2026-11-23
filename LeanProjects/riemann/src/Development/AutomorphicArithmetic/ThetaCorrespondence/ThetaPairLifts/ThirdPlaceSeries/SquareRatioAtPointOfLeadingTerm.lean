import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRangeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2 Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1600000 in
theorem square_ratio_at_point_of_leading_term_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  intro hP hAg hMa hSet hdl hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hAg hMa hLN
  obtain ⟨c3, h3⟩ := hSet.atPt hC
  obtain ⟨c5, h5⟩ := Model.gBig_and (Model.gBig_and hLN hTX) (Model.gBig_and hTW hBF)
  refine ⟨max c3 c5, fun CF hCF => ?_⟩
  have k3 : c3 ≤ CF := le_trans (by simp) hCF
  have k5 : c5 ≤ CF := le_trans (by simp) hCF
  obtain ⟨e0, he0, H⟩ := (h3 CF k3).and (hdl.and hSet)
  refine ⟨e0, he0, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  obtain ⟨C0, x₀, hg⟩ := h5 eps CF k5
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨y3, g3⟩, ⟨y5, g5⟩, ⟨y6, g6⟩⟩ := hK Fm CH hc hL
  refine ⟨max (max y3 y5) (max y6 x₀), fun x hx hle i p hp G W n a ha => ?_⟩
  have l3 : y3 ≤ x := le_trans (by simp) hle
  have l5 : y5 ≤ x := le_trans (by simp) hle
  have l6 : y6 ≤ x := le_trans (by simp) hle
  have l7 : x₀ ≤ x := le_trans (by simp) hle
  have hset := g6 x hx l6 i p hp ha.eser
  have hrec : Rec (Fm.L x i) := ⟨hset.size, hset.host, hset.hF, g5 x hx l5 i p hp⟩
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := hg C0 le_rfl _ (Fm.L x i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact l7) hrec _ _ _ hset.core.lev G
  have hc := g3 x hx l3 i p hp G W n a ha
  have hstd : IsStdChar (Fm.D x i) W.ψ (-1) := (ha.is.weil.ψ : a.ch.W.ψ = _) ▸ hset.std
  exact fun i' j' t => sqRatio_mem_of G _ W a.S.toGridChoice a.rm a.c hstd ha.field hc ha.is.const
    (fun i j => (hLN' i j).1) (hTX' W hstd) (hTW' W a.S.toGridChoice a.rm hstd ha.field) (hBF' W hstd) i' j' t
end GlobalTheory.BigTop.Fun
end
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_ratio_mem_range_emb_ll : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt | exact _root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.square_ratio_at_point_of_leading_term_alt <;> assumption)
end
end
