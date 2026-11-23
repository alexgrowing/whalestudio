import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.WittDec

variable {D : D7}

theorem isoFrame_le {W : HSp D} {r : ℕ} {C : Matrix (Fin W.rank) (Fin r) D.host.E} (h : IsIsoFrame W C) :
    r ≤ W.rank := by
  have := h.2.1.fintype_card_le_finrank
  simpa using this

theorem isoFrame_extend {W W₀ : HSp D} {r s : ℕ} (d : HypDec W W₀ r)
    {C₀ : Matrix (Fin W₀.rank) (Fin s) D.host.E} (hC₀ : IsIsoFrame W₀ C₀) :
    ∃ C : Matrix (Fin W.rank) (Fin (r + s)) D.host.E, IsIsoFrame W C := by
  classical
  set M : Matrix (Fin W.rank) (Fin r ⊕ Fin s) D.host.E := Matrix.fromCols d.e (d.i₀ * C₀) with hM
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hi₀e : d.eᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have he'i₀ : d.e'ᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e'
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have hC₀iso : C₀ᴴ * HSpace.gram W₀ * C₀ = 0 := hC₀.2.2
  have hiso : Mᴴ * HSpace.gram W * M = 0 := by
    rw [hM, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    have h1 : d.eᴴ * HSpace.gram W * d.e = 0 := d.ee
    have h2 : d.eᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by rw [← Matrix.mul_assoc, hi₀e, Matrix.zero_mul]
    have h3 : (d.i₀ * C₀)ᴴ * HSpace.gram W * d.e = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e,
        Matrix.mul_zero]
    have h4 : (d.i₀ * C₀)ᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by
      rw [Matrix.conjTranspose_mul, show C₀ᴴ * d.i₀ᴴ * HSpace.gram W * (d.i₀ * C₀) =
        C₀ᴴ * (d.i₀ᴴ * HSpace.gram W * d.i₀) * C₀ by simp only [Matrix.mul_assoc], d.iso, hC₀iso]
    rw [h1, h2, h3, h4, Matrix.fromBlocks_zero]
  have hker : ∀ v, M *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [hM, Matrix.fromCols_mulVec] at hv
    have ha : v ∘ Sum.inl = 0 := by
      have h := congrArg (fun x => (d.e'ᴴ * HSpace.gram W) *ᵥ x) hv
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rwa [d.e'e, ← Matrix.mul_assoc, he'i₀, Matrix.zero_mul, Matrix.zero_mulVec, add_zero,
        Matrix.one_mulVec] at h
    have hb' : d.i₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [ha, Matrix.mulVec_zero, zero_add] at hv
      rw [Matrix.mulVec_mulVec]; exact hv
    have hb'' : HSpace.gram W₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [← d.iso, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_zero]
    have hc : C₀ *ᵥ (v ∘ Sum.inr) = 0 := Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne W₀) hb''
    have hinj₀ : Function.Injective C₀.mulVec := Matrix.mulVec_injective_iff.2 hC₀.2.1
    have hb : v ∘ Sum.inr = 0 := hinj₀ (by rw [hc, Matrix.mulVec_zero])
    funext x
    cases x with
    | inl i => exact congrFun ha i
    | inr j => exact congrFun hb j
  refine ⟨M.submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · have := hC₀.1; omega
  · apply Matrix.mulVec_injective_iff.1
    intro v w h
    have hsub : M.submatrix id finSumFinEquiv.symm *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at hsub
    have h0 := hker _ (by simpa using hsub)
    have h1 : v - w = 0 := by
      funext i
      have := congrFun h0 (finSumFinEquiv.symm i)
      simpa using this
    exact sub_eq_zero.1 h1
  · show (M.submatrix id finSumFinEquiv.symm)ᴴ * HSpace.gram W * M.submatrix id finSumFinEquiv.symm = 0
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun hiso (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem aniso_or_hypDec (W : HSp D) :
    IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r' := by
  classical
  by_cases hA : IsAniso W
  · exact Or.inl hA
  right
  have hex : ∃ r, ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C := by
    by_contra h
    push_neg at h
    exact hA fun r C => h r C
  obtain ⟨r₁, C₁, hC₁⟩ := hex
  let P : ℕ → Prop := fun r => ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C
  have hPr : P (Nat.findGreatest P W.rank) := Nat.findGreatest_spec (isoFrame_le hC₁) ⟨C₁, hC₁⟩
  have hmax : ∀ s, P s → s ≤ Nat.findGreatest P W.rank := fun s hs =>
    Nat.le_findGreatest (isoFrame_le hs.choose_spec) hs
  obtain ⟨C, hC⟩ := hPr
  obtain ⟨W₀, ⟨hrk, ι, hι, C', hC', horth⟩, -⟩ :=
    GlobalTheory.WittLow.wittLowEx D W (Nat.findGreatest P W.rank) ⟨C, hC.2.1, hC.2.2⟩
  have hpos : 0 < Nat.findGreatest P W.rank := hC.1
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hsplit : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W₀ C' (frameMat W W₀ ι) := by
    refine ⟨⟨hpos, hC'.1, hC'.2⟩, GlobalTheory.AutFunCounterexample.gram_pull W W₀ ι hι, ?_, by omega⟩
    show C'ᴴ * HSpace.gram W * frameMat W W₀ ι = 0
    have h : (frameMat W W₀ ι)ᴴ * HSpace.gram W * C' = 0 := horth
    have h2 := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h2
  obtain ⟨d, -, -, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W₀ _ C' _ hsplit
  refine ⟨W₀, _, d, fun s C₀ hC₀ => ?_, hpos⟩
  obtain ⟨C₂, hC₂⟩ := isoFrame_extend d hC₀
  have h1 := hmax _ ⟨C₂, hC₂⟩
  have h2 := hC₀.1
  omega

theorem maj_and_witt : ∀ (D : D7) (W : HSp D), HSpace.SigOK W →
    (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧
      (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') :=
  fun _ W _ => ⟨GlobalTheory.Doubling.exists_isMaj W, aniso_or_hypDec W⟩

end GlobalTheory.Core.Rk.WittDec
