import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

section Tempered

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem tempered_mul_entry {l m n : Type*} [Fintype m] {M : W → Matrix l m ℂ} {N : W → Matrix m n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j)
    (hN : ∀ i j, Function.HasTemperateGrowth fun x => N x i j) (i : l) (j : n) :
    Function.HasTemperateGrowth fun x => (M x * N x) i j := by
  simp only [Matrix.mul_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => (hM i k).mul (hN k j)

theorem tempered_trace {n : Type*} [Fintype n] {M : W → Matrix n n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j) :
    Function.HasTemperateGrowth fun x => (M x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => hM k k

end Tempered

variable {D : D7} {r : ℕ}

def quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) (X : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ :=
  -∑ τ, (tauE D τ c * Matrix.trace (a.map (tauE D τ) *
    ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ))))).re

theorem tempered_quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) :
    Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => ((quadForm D c G a X : ℝ) : ℂ) := by
  have hc : ∀ (τ : D.what₂.Tau) (i : Fin m) (j : Fin n),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => Matrix.of (X τ) i j := fun τ i j =>
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))).hasTemperateGrowth)
  have hs : ∀ (τ : D.what₂.Tau) (i : Fin n) (j : Fin m),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => (Matrix.of (X τ))ᴴ i j := fun τ i j =>
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ)))).hasTemperateGrowth)
  have hg : ∀ τ : D.what₂.Tau, Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ =>
      tauE D τ c * Matrix.trace (a.map (tauE D τ) *
        ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ)))) := fun τ =>
    (Function.HasTemperateGrowth.const _).mul (tempered_trace
      (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _)
        (tempered_mul_entry (hs τ)
          (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _) (hc τ)))))
  have hsum := Function.HasTemperateGrowth.sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    ((-(Complex.ofRealCLM.comp Complex.reCLM)).hasTemperateGrowth).comp (hg τ)
  convert hsum using 1
  funext X
  simp [quadForm]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e :=
  (hθ τ).1 e

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D l n) = compAt θ τ x * compAt θ τ y := by
  have := Matrix.map_mul (L := x) (M := y) (f := (θ τ).comp (infPart D))
  exact this

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (y : Mx D m n) :
    compAt θ τ (adj y) = (compAt θ τ y)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.Mem.VolExists.infEmb_sigR (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (hθ τ)]
  rfl

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (rat M) = M.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  exact theta_incA hθ τ _

theorem multM_eq_quadForm {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (V : HSp D) (a : HermE D r)
    (y : Mx D V.rank r) :
    multM θ α V a y = quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1
      (fun τ i j => compAt θ τ y i j) := by
  unfold multM lam quadForm
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, map_mul, theta_incA hθ, GlobalTheory.PhaseReal.theta_pair θ hθ]
  congr 3
  show _ * compAt θ τ (inner V y y) = _
  congr 1
  unfold GlobalTheory.StdUnn.inner
  rw [compAt_mul', compAt_mul', compAt_adj hθ, gA, compAt_rat hθ]
  rfl

theorem multM_tempered : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  intro D r θ hθ α V a
  refine ⟨fun X => ((quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1 X : ℝ) : ℂ),
    tempered_quadForm D _ _ _, fun y => ?_⟩
  rw [multM_eq_quadForm hθ]

end GlobalTheory.CompanionTheory.WSum
