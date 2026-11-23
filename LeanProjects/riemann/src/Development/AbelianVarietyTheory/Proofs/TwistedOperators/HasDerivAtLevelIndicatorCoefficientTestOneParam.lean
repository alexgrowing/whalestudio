import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TermDeriv

theorem hasDerivAt_coef_oneP : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  intro D hHC θ hθ V S M K v b τ hb X hX x
  have hfin : ∀ s : ℝ, Lev.finE V (x * oneP θ V τ X s) = Lev.finE V x := by
    intro s
    have h : finHom V (oneP θ V τ X s) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
    show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X s) = _
    rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X s), h, map_one, mul_one]
    rfl
  by_cases hK : Lev.finE V x ∈ K
  swap
  · have e : (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun _ => 0 := by
      funext s
      simp only [coef, hfin s, hK, if_false]
    rw [e]
    have e2 : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x = 0 := by
      simp only [coef, hK, if_false]
    rw [e2]
    exact hasDerivAt_const _ _
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (b τ) :=
    hHC.smoothVec hstd.1 hstd.2.1 hb (M.fr_unit τ) (M.fr_gram τ)
  have hd0 := Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_hasDerivAt hsv hX 0
  rw [zero_smul, NormedSpace.exp_zero, Formalism.IndefR.SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] at hd0
  set c : ℂ := ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' x) (b τ')⟫_ℂ with hc
  have hfun : ∀ s : ℝ, coef θ M K v b (x * oneP θ V τ X s) =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ := by
    intro s
    simp only [coef, hfin s, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
    congr 1
    · refine Finset.prod_congr rfl fun τ' hτ' => ?_
      have hne := Finset.ne_of_mem_erase hτ'
      have h := (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.2 τ' hne
      show ⟪v τ', M.rep τ' (infMat D.sp.cm.sig V.gram (θ τ') (x * oneP θ V τ X s)) (b τ')⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.mul_one]
    · show ⟪v τ, M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (x * oneP θ V τ X s)) (b τ)⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.1,
        Formalism.IndefR.SchurOrthogonalityAlt.rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ) (GlobalTheory.Mem.Lift.exp_mem hX s)]
      rfl
  have hval : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (dRep (M.rep τ) X (b τ))⟫_ℂ := by
    simp only [coef, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ' hτ' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ')]
  rw [hval, show (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun s : ℝ =>
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ from funext hfun]
  refine HasDerivAt.const_mul c ?_
  exact (((innerSL ℂ (v τ)).comp (M.rep τ (cmp θ τ x))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd0

end GlobalTheory.TermDeriv

end
