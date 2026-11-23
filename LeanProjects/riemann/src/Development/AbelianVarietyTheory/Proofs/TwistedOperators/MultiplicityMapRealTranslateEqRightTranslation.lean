import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothTranslate

open Classical in

theorem mult_equiv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => funext x; simp [rTr]
  | add T T' _ _ h h' =>
    funext x
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem translate : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  intro D V S θ M J χ T hT g
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V),
      T (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
        GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
        else v τ) x = T v (x * P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun v x => by simp⟩
    | insert a s ha ih =>
      obtain ⟨P, hP, hPe⟩ := ih
      refine ⟨atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) * P, mul_mem (Formalism.IndefR.TopMult.atTau_mem_GinfC θ a _) hP,
        fun v x => ?_⟩
      have hupd : (fun τ => if τ ∈ insert a s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) = Function.update (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) a ⟨M.rep a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) (v a),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ (v a).2⟩ := by
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd, mult_equiv θ M J χ T hT a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ _ (by simp [ha])]
      show T _ (x * atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a))) = _
      rw [hPe, mul_assoc]
  obtain ⟨P, hP, hPe⟩ := key Finset.univ
  exact ⟨P, hP, fun v x => by simpa using hPe v x⟩

end GlobalTheory.SmoothTranslate
