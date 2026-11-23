import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_operator_spectrum : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  first | exact @GlobalTheory.Mem.SJ.PairMain.pair_step | exact GlobalTheory.Mem.SJ.PairMain.pair_step | (intros; apply GlobalTheory.Mem.SJ.PairMain.pair_step <;> assumption)
