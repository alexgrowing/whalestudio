import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.CartFrames

open Matrix
open scoped ComplexOrder

theorem herm_eig {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ * (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 ∧
    (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ = 1 ∧
    A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← Matrix.star_eq_conjTranspose]
    exact h

theorem posDef_factor {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ} (hP : P.PosDef) :
    ∃ B C : Matrix (Fin k) (Fin k) ℂ, Bᴴ * B = P ∧ B * C = 1 ∧ C * B = 1 := by
  obtain ⟨h1, h2, h3⟩ := herm_eig hP.isHermitian
  set U : Matrix (Fin k) (Fin k) ℂ := (hP.isHermitian.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set d := hP.isHermitian.eigenvalues with hd
  have hpos : ∀ i, 0 < d i := hP.eigenvalues_pos
  let r : Fin k → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simpa [r] using (Real.sqrt_pos.2 (hpos i)).ne'
  have hrr : ∀ i, star (r i) * r i = (d i : ℂ) := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
  have hdiag : diagonal r * diagonal (fun i => (r i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hr0 i)
  have hdiag' : diagonal (fun i => (r i)⁻¹) * diagonal r = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hr0 i)
  refine ⟨diagonal r * Uᴴ, U * diagonal (fun i => (r i)⁻¹), ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    calc U * diagonal (star r) * (diagonal r * Uᴴ) = U * (diagonal (star r) * diagonal r) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => (d i : ℂ)) * Uᴴ := by
          rw [diagonal_mul_diagonal]; congr 3; funext i; exact hrr i
      _ = P := h3.symm
  · calc diagonal r * Uᴴ * (U * diagonal fun i => (r i)⁻¹)
        = diagonal r * (Uᴴ * U) * diagonal (fun i => (r i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hdiag]
  · calc U * diagonal (fun i => (r i)⁻¹) * (diagonal r * Uᴴ)
        = U * (diagonal (fun i => (r i)⁻¹) * diagonal r) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdiag', Matrix.mul_one, h2]

theorem exists_frame {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    ∃ (ε : Fin k → Bool) (f : GL (Fin k) ℂ),
      (f.1)ᴴ * G * f.1 = diagonal (PositivityTheory.Rg.Sw.sgn ε) ∧ (f.1)ᴴ * (G * s) * f.1 = 1 := by
  obtain ⟨hss, hiso, hP⟩ := h
  obtain ⟨B, C, hBB, hBC, hCB⟩ := posDef_factor hP

  have hPs : (G * s) * s = G := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  have hsP : sᴴ * (G * s) = G := by rw [← Matrix.mul_assoc]; exact hiso
  have hCtBt : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]

  have hHh : (B * s * C).IsHermitian := by
    have e : (B * s * C)ᴴ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by
      rw [conjTranspose_mul, conjTranspose_mul]
      calc Cᴴ * (sᴴ * Bᴴ) = Cᴴ * (sᴴ * Bᴴ) * (B * C) := by rw [hBC, Matrix.mul_one]
        _ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by simp only [Matrix.mul_assoc]
    show (B * s * C)ᴴ = B * s * C
    rw [e, hBB, hsP, ← hPs, ← hBB]
    calc Cᴴ * (Bᴴ * B * s) * C = (Cᴴ * Bᴴ) * (B * s * C) := by simp only [Matrix.mul_assoc]
      _ = B * s * C := by rw [hCtBt, Matrix.one_mul]
  have hHH : (B * s * C) * (B * s * C) = 1 := by
    calc (B * s * C) * (B * s * C) = B * s * (C * B) * s * C := by simp only [Matrix.mul_assoc]
      _ = B * (s * s) * C := by rw [hCB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hss, Matrix.mul_one, hBC]
  obtain ⟨h1, h2, h3⟩ := herm_eig hHh
  set V : Matrix (Fin k) (Fin k) ℂ := (hHh.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hV
  set l := hHh.eigenvalues with hl
  set H := B * s * C with hH

  have hHV : H * V = V * diagonal (fun i => (l i : ℂ)) := by
    conv_lhs => rw [h3]
    calc V * diagonal (fun i => (l i : ℂ)) * Vᴴ * V = V * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

  have hsq : diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ)) = 1 := by
    calc diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ))
        = (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) := by
          rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (l i : ℂ)) * Vᴴ) * (V * diagonal (fun i => (l i : ℂ))) := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * H * (H * V) := by rw [← h3, hHV]
      _ = Vᴴ * (H * H) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, h1]
  have hl2 : ∀ i, l i = 1 ∨ l i = -1 := fun i => by
    have e := congrFun (congrFun hsq i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, Matrix.one_apply_eq] at e
    have e' : l i * l i = 1 := by exact_mod_cast e
    exact mul_self_eq_one_iff.mp e'
  have hsgn : PositivityTheory.Rg.Sw.sgn (fun i => decide (0 < l i)) = fun i => (l i : ℂ) := by
    funext i
    rcases hl2 i with e | e <;> simp [PositivityTheory.Rg.Sw.sgn, e]
  let f : GL (Fin k) ℂ := ⟨C * V, Vᴴ * B, by
    calc C * V * (Vᴴ * B) = C * (V * Vᴴ) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hCB], by
    calc Vᴴ * B * (C * V) = Vᴴ * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, Matrix.mul_one, h1]⟩
  have hf : f.1 = C * V := rfl
  have hfP : (f.1)ᴴ * (G * s) * f.1 = 1 := by
    rw [hf, conjTranspose_mul, ← hBB]
    calc Vᴴ * Cᴴ * (Bᴴ * B) * (C * V) = Vᴴ * (Cᴴ * Bᴴ) * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCtBt, hBC, Matrix.mul_one, Matrix.mul_one, h1]
  have hsf : s * f.1 = f.1 * diagonal (fun i => (l i : ℂ)) := by
    rw [hf]
    calc s * (C * V) = (C * B) * s * C * V := by rw [hCB, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = C * (H * V) := by rw [hH]; simp only [Matrix.mul_assoc]
      _ = C * V * diagonal (fun i => (l i : ℂ)) := by rw [hHV, Matrix.mul_assoc]
  refine ⟨fun i => decide (0 < l i), f, ?_, hfP⟩
  rw [hsgn]
  calc (f.1)ᴴ * G * f.1 = (f.1)ᴴ * ((G * s) * s) * f.1 := by rw [hPs]
    _ = (f.1)ᴴ * (G * s) * (s * f.1) := by simp only [Matrix.mul_assoc]
    _ = ((f.1)ᴴ * (G * s) * f.1) * diagonal (fun i => (l i : ℂ)) := by
        rw [hsf]; simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => (l i : ℂ)) := by rw [hfP, Matrix.one_mul]

theorem exists_frames : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ), PositivityTheory.SiegelWeilFormula.Gen.IsFrames (HSpace.gram V) θ ε fr ∧ ∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1 := by
  intro D V θ s hθ hs
  choose ε fr h1 h2 using fun τ => exists_frame (hs τ)
  refine ⟨ε, fr, fun τ => ?_, h2⟩
  have e : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) (HSpace.gram V)).map (θ τ) = gramAt D V τ := by
    ext a b
    exact (hθ τ).1 _
  rw [e]
  exact h1 τ

end GlobalTheory.CompanionTheory.CartFrames
