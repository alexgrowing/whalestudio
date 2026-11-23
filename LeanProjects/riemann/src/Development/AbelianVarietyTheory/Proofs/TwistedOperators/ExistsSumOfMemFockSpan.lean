import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

variable {D : D7}

theorem cart_frSgn (ε : Bool) (S : GlobalTheory.Grid.Node D) :
    (frSgn ε (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS ε S := by
  funext τ
  cases ε
  · show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (S.M.ε τ a)) * S.M.fr τ = (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ
    simp only [Bool.false_xor]
  · have e' : Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) = -Formalism.REAL.Jm (S.M.ε τ) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : S.M.ε τ a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) * S.M.fr τ = -((S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ)
    rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem ptF_eq_fock (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f P = GlobalTheory.Grid.fock ψ θ ε S T f P := by
  unfold ptF GlobalTheory.Grid.fock
  rw [cart_frSgn]
  rfl

theorem isVacF_iff (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f ↔ GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  unfold IsVacF GlobalTheory.Grid.IsFinVec
  rw [cart_frSgn]
  rfl

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

theorem exists_sum_of_mem_fockSpan {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (U : AddSubgroup (WO S.V T.V)) {g : WO S.V T.V → ℂ}
    (hg : g ∈ fockSpan ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) U) :
    ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T),
      (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ g = ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l) := by
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hg
  choose f₀ P h1 _ h3 using fun l => (x l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => (isVacF_iff ψ θ ε S T _).1 (h1 l), ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, map_smul, ptF_eq_fock]

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open Formalism.IndefR.Mult GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity
open scoped ENNReal

theorem dense_level {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (A : Fr V) (B : Fr W)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    (hm : IsCovolOne (ratL W V) μ 𝓕) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U) (d : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ fockSpan ψ θ A B U, g ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ V W (toB hψ f hf.1) = f := coe_toB hψ f hf.1
  have hF : toB hψ f hf.1 ∈ (GlobalTheory.Size.thetaLevel ψ V W U).comap (coeL ψ V W) := by
    rw [Submodule.mem_comap, e0]
    exact hf
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ A B hU (toL2 _ _ (μ.restrict 𝓕))
    (fun v G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ G)
    (fun a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF hδ
  refine ⟨coeL ψ V W g, h1, h2, lt_of_eq_of_lt ?_ h3⟩
  have e1 : ∀ G : BB ψ V W, l2O μ 𝓕 (coeL ψ V W G) = ‖toL2 _ _ (μ.restrict 𝓕) G‖ₑ := fun G =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ G.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : f - coeL ψ V W g = coeL ψ V W (toB hψ f hf.1 - g) := by rw [LinearMap.map_sub, e0]
  simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

end

end GlobalTheory.FockApprox

open scoped ENNReal in

theorem GlobalTheory.FockApprox.theta_approx_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ := by
  intro D ψ θ hθ hψ ε S T U hU Φ hΦ μ 𝓕 hm d δ hδ
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.FockApprox.dense_level (ψ := ψ) (θ := θ) (V := GlobalTheory.Grid.sgn ε S.V) (W := T.V)
    (GlobalTheory.SquareComm.frSgn ε (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) hψ hθ hm hU hΦ d
    (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, f, p, hf, hg⟩ := GlobalTheory.FockApprox.exists_sum_of_mem_fockSpan ψ θ ε S T U h1
  refine ⟨n, f, p, hf, ?_, ?_⟩
  · rw [← hg]
    exact sub_mem hΦ h2
  · rw [← hg]
    exact h3

end
