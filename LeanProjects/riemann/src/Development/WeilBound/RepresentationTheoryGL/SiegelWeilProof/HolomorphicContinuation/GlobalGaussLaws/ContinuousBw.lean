import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiInnerSIns
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FibFact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (a b : Mx D m n) :
    compAt θ τ (a + b) = compAt θ τ a + compAt θ τ b := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add]

set_option synthInstance.maxHeartbeats 400000 in
theorem finMap_add (a b : Mx D m n) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
  ext i j; simp only [Matrix.map_apply, Matrix.add_apply, RingHom.map_add]

theorem away_add {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (y : Mx D m n) (u : Fin m → Fin n → ℂ) :
    Ψ (y + sIns τ fr u) = Ψ y := by
  refine hΨ.1 _ _ (fun τ' hne => ?_) ?_
  · rw [compAt_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, compAt_insT hθ, if_neg hne,
      add_zero]
  · rw [finMap_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, finMap_insT, add_zero]

theorem cont_of_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) : Continuous Ψ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hc := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨_, hmem⟩
  have hg : Continuous fun x : Mx D m n => gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    have h1 : Continuous fun x : Mx D m n => (S (piF θ τ fr x)) := S.continuous.comp (continuous_piF hθ τ fr)
    refine h1.congr fun x => ?_
    rw [hS]; rfl
  have hne : ∀ x : Mx D m n, gs (n := n) 1 (fr⁻¹ * compAt θ τ x) ≠ 0 := fun x => Complex.exp_ne_zero _
  have e : Ψ = fun x => tens θ τ fr (gs 1) Ψ x / gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    funext x
    simp only [tens]
    field_simp [hne x]
  rw [e]
  exact hc.div hg hne

def Bw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) : ℂ :=
  Ψ y * ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y)))))

theorem Bw_add {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (x y : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    Bw ψ V θ τ fr Ψ x (y + sIns τ fr u) = Bw ψ V θ τ fr Ψ x y := by
  have e : y + sIns τ fr u - sIns τ fr (piF θ τ fr (y + sIns τ fr u)) = y - sIns τ fr (piF θ τ fr y) := by
    rw [(piF θ τ fr).map_add, piF_sIns hθ τ hdet, (sIns τ fr).map_add]
    abel
  unfold Bw
  rw [away_add hθ hΨ, e]

set_option synthInstance.maxHeartbeats 800000 in
theorem continuous_Bw {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (x : Mx D V.rank n) :
    Continuous (Bw ψ V θ τ fr Ψ x) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : ContinuousSub (Mx D V.rank n) := inferInstance
  refine (cont_of_away hθ hΨ).mul ?_
  have h := GlobalTheory.CompanionTheory.EisUnfold.Core.continuous_lin ψ hψ V x
  exact h.comp (continuous_id.sub ((continuous_sIns τ fr).comp (continuous_piF hθ τ fr)))

theorem norm_Bw {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    ‖Bw ψ V θ τ fr Ψ x y‖ = ‖Ψ y‖ := by
  unfold Bw; rw [norm_mul, hψ.2.1, mul_one]

end PositivityTheory.Rg.Sw.Glob.FTH
