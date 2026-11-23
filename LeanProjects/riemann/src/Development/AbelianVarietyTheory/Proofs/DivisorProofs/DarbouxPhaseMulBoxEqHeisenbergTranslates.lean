import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BoxPhaseW

open GlobalTheory.RouteCoords GlobalTheory.RouteCoordsW GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

set_option maxHeartbeats 1000000 in

theorem sympW : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (i j : ℕ) (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
                 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' =
      symplO (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x')ᵀ) +
        symplO (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x') := by
  intro D T L sc G i j e Γ hW hWW x x'
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (incM (spV G i j).gramᵀ) (incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, incM_smul]
      congr 1
      exact blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J = (spW G i j).gram.map (incA D) := by
    have k : incM Γ.V.J = incM (spW G i j).gram := by rw [hW, incM_smul, map_one, one_smul]
    exact k
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO (negSp (spW G i j)) (spV G i j) (mulG (negSp (spW G i j)) (colV e x)ᵀ)
      (mulG (negSp (spW G i j)) (colV e x')ᵀ) = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spW G i j)).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO (spV₁ G i j) (spW G i j) (adjV₁ e x) (adjV₁ e x') = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spV₁ G i j).gram⁻¹).map (incA D)) ((spW G i j).gram.map (incA D)) _ _
  unfold symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add]
  congr 1
  have hg : (((-((spW G i j).gram.map (incA D))).map (cA D))ᵀ) = -((spW G i j).gram.map (incA D)) := by
    rw [Matrix.map_neg _ (map_neg _), transpose_neg, gram_conj_transpose]
  have hgi : -(((spW G i j).gram⁻¹).map (incA D)) * -((spW G i j).gram.map (incA D)) = 1 := by
    rw [neg_mul_neg, inv_mul_gram]
  have h1 := trace_first (cA D) (-((spW G i j).gram.map (incA D))) (-(((spW G i j).gram⁻¹).map (incA D)))
    ((spV G i j).gram.map (incA D)) hg hgi (colV e x) (colV e x')
  have h2 := trace_second_pos (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) adeleConj_incl_skewElement_eq_neg ((spW G i j).gram.map (incA D))
    ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D)) (gram_conj_transpose _)
    (gram_conj_transpose _) (inv_mul_gram _) (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [negSp_gram_inv, Matrix.map_neg _ (map_neg _)]
  have hm : ∀ (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)), mulG S y = HMul.hMul y (S.gram.map (incA D)) :=
    fun _ _ _ => rfl
  have hadj : ∀ y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      adjV₁ e y = -mulG (spV₁ G i j) ((y.submatrix id fun k => e (.inr k)).map (cA D)) :=
    fun _ => rfl
  have hcol : ∀ y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      colV e y = y.submatrix id fun k => e (.inl k) := fun _ => rfl
  simp only [hadj, hm]
  rw [negSp_gram, Matrix.map_neg _ (map_neg _)]
  simp only [hcol] at h1
  erw [h2, h1]
  rw [hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    mul_blk_mul_transpose, trace_smul, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  simp only [transpose_neg, Matrix.mul_neg, trace_neg]
  ring

theorem mulG_colV_addW {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (x w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (x + w))ᵀ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ +
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV
  rw [← Matrix.add_mul]
  rfl

theorem adjV₁_addW {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (x w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (x + w) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x + GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG
  rw [← neg_add, ← Matrix.add_mul]
  congr 2
  ext a b
  simp

theorem invOf_two_eq (F : Type) [Field F] [NumberField F] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  apply invOf_eq_right_inv
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

end GlobalTheory.BoxPhaseW

namespace GlobalTheory.BoxPhase

theorem phase_box_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j), Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ (ψ : AddChar (AF D.host.F) ℂ) (F₁ : WO (negSp (spW G i j)) (spV G i j) → ℂ) (F₂ : WO (spV₁ G i j) (spW G i j) → ℂ) (v w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)), ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e w).2 - (Γ.M.co.e w).1 ⬝ᵥ (Γ.M.co.e v).2)) * (F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (v + w))ᵀ) * F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (v + w))) = heisO ψ (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ) F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ) * heisO ψ (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w) F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v) := by
  intro D T L sc G i j e Γ hW hWW ψ F₁ F₂ v w
  rw [← Γ.M.co.form v w, GlobalTheory.BoxPhaseW.sympW i j e Γ hW hWW v w, GlobalTheory.BoxPhaseW.mulG_colV_addW,
    GlobalTheory.BoxPhaseW.adjV₁_addW, GlobalTheory.BoxPhaseW.invOf_two_eq]
  simp only [heisO, symplOH]
  rw [mul_add, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.BoxPhase
