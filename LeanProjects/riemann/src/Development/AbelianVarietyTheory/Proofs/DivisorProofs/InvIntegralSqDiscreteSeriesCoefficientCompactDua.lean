import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

section Perm

variable {p q n : ℕ} {ε : Fin n → Bool}

def permFrame (e : Fin p ⊕ Fin q ≃ Fin n) : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
  (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix id e.symm

theorem mul_permFrame (e : Fin p ⊕ Fin q ≃ Fin n) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    X * permFrame e = X.submatrix id e.symm := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply]

theorem permFrame_conjTranspose_mul (e : Fin p ⊕ Fin q ≃ Fin n) (Y : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (permFrame e)ᴴ * Y = Y.submatrix e.symm id := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem permFrame_herm {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e) :
    (permFrame e)ᴴ * Formalism.UG.Jpq p q * permFrame e = Formalism.REAL.Jm ε := by
  rw [Matrix.mul_assoc, mul_permFrame, permFrame_conjTranspose_mul, ← h.reindex_Jpq, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  rfl

theorem frameInv_permFrame {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    frameInv ε (permFrame e) * X * permFrame e = Matrix.reindex e e X := by
  have : frameInv ε (permFrame e) * X * permFrame e =
      Formalism.REAL.Jm ε * ((permFrame e)ᴴ * (Formalism.UG.Jpq p q * X * permFrame e)) := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, mul_permFrame, permFrame_conjTranspose_mul, Matrix.submatrix_submatrix,
    show (e.symm ∘ id : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    show (id ∘ e.symm : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    ← Matrix.submatrix_mul_equiv (Formalism.UG.Jpq p q) X e.symm e.symm e.symm,
    ← Matrix.reindex_apply, h.reindex_Jpq, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul,
    Matrix.reindex_apply]

end Perm

theorem map_frameEquiv_cd (cd : CDHaar) {p q n : ℕ} {ε : Fin n → Bool} (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (cd.cd p q).map (frameEquiv B hB hn) = (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
  classical
  let e₀ : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let ε₀ : Fin n → Bool := fun i => (e₀.symm i).isLeft
  have h₀ : Sorts ε₀ e₀ := ⟨fun i => by simp [ε₀], fun j => by simp [ε₀]⟩
  have hC : (B.submatrix e₀.symm id)ᴴ * Formalism.REAL.Jm ε₀ * B.submatrix e₀.symm id = Formalism.REAL.Jm ε := by
    rw [← h₀.reindex_Jpq, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hB]
    rfl
  have hcount : Nat.card {a // ε a = true} = p := (GlobalTheory.SignCount.card_true_eq _ hC).symm.trans h₀.card_true
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  have hP : P = p := he.card_true.symm.trans hcount
  have hQ : Q = q := by have := Sorts.add_eq e; omega
  subst hP hQ
  have hBp := permFrame_herm he
  have hfun : (frameEquiv (permFrame e) hBp hn : UpqT P Q → Formalism.REAL.UJ ε) = he.equiv := funext fun b =>
    umat_injective (by rw [umat_frameEquiv, frameInv_permFrame he, he.umat_equiv])
  have hmap0 : (cd.cd P Q).map (frameEquiv (permFrame e) hBp hn) =
      (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
    rw [hfun]
    ext A hA
    rw [Measure.map_apply he.measurable_equiv hA, ← he.set_eq]
    exact (cdScaleIs_trueScale cd n ε P Q e he.1 he.2 A hA).symm
  exact map_frameEquiv hBp hB hn (cd.cd P Q) _ hmap0

end GlobalTheory.LowRow.CompactDualCoef

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

theorem inv_integral_coef_sq : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  intro hHC cd D W S M Fr hFr hsig ρ hanti hhalf w hw
  classical
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  have hn := hsig ρ
  have hmap := map_frameEquiv_cd cd _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding (frameEquiv _ (frame_herm M hFr ρ) hn) :=
    (frameEquiv _ (frame_herm M hFr ρ) hn).toHomeomorph.measurableEmbedding
  have hk : (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) =
      (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘ frameEquiv _ (frame_herm M hFr ρ) hn :=
    funext fun b => by simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpr := hHC cd (trueScale cd) (cdScaleIs_trueScale cd) W.rank (M.ε ρ) (M.lam ρ) ⟨hanti, hhalf⟩ (M.H ρ)
    (M.σ ρ) w (M.ds ρ) hw0
  rw [hw, one_pow, one_div] at hpr
  have hpos : 0 < (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) /
      ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    · exact abs_pos.2 (sub_ne_zero.2 (hanti.injective.ne (ne_of_lt (Finset.mem_filter.1 hb).2)))
    · have := (Finset.mem_filter.1 hb).2
      exact sub_pos.2 (by exact_mod_cast this)
  have hint : Integrable (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2)
      ((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) := by
    by_contra hni
    rw [integral_undef hni, _root_.inv_zero] at hpr
    exact hpos.ne hpr
  rw [← hmap] at hint
  rw [hk]
  refine ⟨hme.integrable_map_iff.1 hint, ?_⟩
  rw [show (∫ b, ((fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘
      frameEquiv _ (frame_herm M hFr ρ) hn) b ∂(cd.cd _ _)) =
      ∫ g, ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2 ∂((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) by
    rw [← hmap, hme.integral_map]; rfl]
  exact hpr

end GlobalTheory.LowRow.CompactDualCoef
