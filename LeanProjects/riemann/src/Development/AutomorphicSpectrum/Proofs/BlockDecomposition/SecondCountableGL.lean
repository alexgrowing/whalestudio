import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open Matrix MeasureTheory Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.Tf.Loc
open GlobalTheory.BCT Formalism.BasicNotions

namespace GlobalTheory.CompanionTheory.LefPair

variable {n : ℕ}

local notation "θ" => thetaR (starRingEnd ℂ)

theorem tw_eq (x d : GL (Fin n) ℂ) : PositivityTheory.RgTw.tw x d = twConj (θ n) x d := by
  have h : PositivityTheory.RgTw.th x = θ n x := by
    apply Units.ext
    rfl
  simp only [PositivityTheory.RgTw.tw, twConj, h]

theorem theta_theta (g : GL (Fin n) ℂ) : θ n (θ n g) = g := by
  apply Units.ext
  show (((g.val.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ))ᵀ = g.val
  ext i j
  simp

theorem twConj_twConj (g x d : GL (Fin n) ℂ) :
    twConj (θ n) x (twConj (θ n) g d) = twConj (θ n) (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem theta_diag (d : GL (Fin n) ℂ) (z : Fin n → ℂ) (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    (θ n d).val = diagonal z := by
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by simpa [h] using hz i
  have hinv : (d⁻¹).val = diagonal fun i => (z i)⁻¹ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hz0 i)
  rw [thetaR_val, hinv]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [transpose_apply, map_apply, diagonal_apply_eq]
    rw [Complex.inv_eq_conj (hz i), Complex.conj_conj]
  · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem charpoly_norm (g d : GL (Fin n) ℂ) (z : Fin n → ℂ) (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    (twConj (θ n) g d * θ n (twConj (θ n) g d)).val.charpoly = (diagonal fun i => z i ^ 2).charpoly := by
  have h : twConj (θ n) g d * θ n (twConj (θ n) g d) = g⁻¹ * (d * θ n d) * g := by
    simp only [twConj, map_mul, map_inv, theta_theta]
    group
  have h2 : (d * θ n d).val = diagonal fun i => z i ^ 2 := by
    rw [Units.val_mul, theta_diag d z hd hz, hd, diagonal_mul_diagonal]
    congr 1
    funext i
    exact (pow_two _).symm
  rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', h2]

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem sigmaFinite_haar [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (ν : Measure (GL (Fin n) ℂ)) [ν.IsHaarMeasure] : SigmaFinite ν := by
  have := locallyCompact_GL n
  have := secondCountable_GL n
  have : SigmaCompactSpace (GL (Fin n) ℂ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact Measure.IsHaarMeasure.sigmaFinite ν

theorem lefOne_eval (hD : EllDiag) (hW : WeylAt) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (ν : Measure (GL (Fin n) ℂ)) [ν.IsHaarMeasure] (l : DomWeight n) (v : ℂ) (f : GL (Fin n) ℂ → ℂ)
    (h : LefOne ν l v f) (d : GL (Fin n) ℂ) (hd : EllC d) :
    ∫ x, f (twConj (θ n) x d) ∂ν = v * starRingEnd ℂ (chAt l (d * θ n d).val.charpoly) := by
  obtain ⟨g, d', z, hd', hz, hinj, rfl⟩ := hD n d hd
  have hz0 : ∀ i, z i ^ 2 ≠ 0 := fun i h0 => by
    have : z i = 0 := by simpa using h0
    simpa [this] using hz i
  simp_rw [twConj_twConj]
  rw [integral_mul_left_eq_self (fun y => f (twConj (θ n) y d')) g, charpoly_norm g d' z hd' hz,
    hW n l (fun i => z i ^ 2) hz0 hinj]
  have := h.2.2 d' z hd' hz hinj
  simp_rw [tw_eq] at this
  exact this

end GlobalTheory.CompanionTheory.LefPair

open GlobalTheory.CompanionTheory.LefPair in

theorem GlobalTheory.CompanionTheory.LefPair.lefPairOf : LefPairOf := by
  intro hD hW _ a b _ _ _ _ ν₁ _ ν₂ _ l₁ l₂ v₁ v₂ f₁ f₂ h₁ h₂
  have := sigmaFinite_haar ν₁
  have := sigmaFinite_haar ν₂
  refine ⟨(h₁.1.comp continuous_fst).mul (h₂.1.comp continuous_snd), ?_, fun d₁ d₂ e₁ e₂ => ?_⟩
  · refine HasCompactSupport.intro (h₁.2.1.prod h₂.2.1) fun x hx => ?_
    rw [Set.mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · rw [integral_prod_mul (fun x => f₁ (twConj (thetaR (starRingEnd ℂ) a) x d₁))
      (fun x => f₂ (twConj (thetaR (starRingEnd ℂ) b) x d₂)),
      lefOne_eval hD hW ν₁ l₁ v₁ f₁ h₁ d₁ e₁, lefOne_eval hD hW ν₂ l₂ v₂ f₂ h₂ d₂ e₂]
    ring

end
