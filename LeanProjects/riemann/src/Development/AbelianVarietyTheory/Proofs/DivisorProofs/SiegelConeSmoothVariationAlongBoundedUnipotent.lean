import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegmentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapVari

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem nilM_smul {r : ℕ} (τ : ℝ) (x : BlockIx a r → Cinf E) :
    (nilM (τ • x) : Matrix (Fin a) (Fin a) (Cinf E)) = τ • nilM x := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem norm_toL_nilM_le {r : ℕ} (x : BlockIx a r → Cinf E) :
    ‖toL (nilM x : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  change ‖(nilM x : Matrix (Fin a) (Fin a) (Cinf E)) i j‖ ≤ ‖x‖
  simp only [nilM, Matrix.of_apply]
  split_ifs with h
  · exact norm_le_pi_norm x _
  · simp

theorem continuous_unip_inf {r : ℕ} :
    Continuous (fun x : BlockIx a r → Cinf E => (unip x : GL (Fin a) (Cinf E))) := by
  have hN : Continuous (fun x : BlockIx a r → Cinf E => (nilM x : Matrix (Fin a) (Fin a) (Cinf E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hN, continuous_const.sub hN⟩

theorem exists_bound_compact {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Ω, ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A ∧
      ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A := by
  have h1 : Continuous (fun c : GL (Fin a) (Cinf E) => toL (c : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  have h2 : Continuous (fun c : GL (Fin a) (Cinf E) =>
      toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  obtain ⟨A1, hA1⟩ := hΩ.exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨A2, hA2⟩ := hΩ.exists_bound_of_continuousOn h2.continuousOn
  exact ⟨max (max A1 A2) 0, le_max_right _ _, fun c hc =>
    ⟨(hA1 c hc).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hA2 c hc).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

theorem norm_conj_le (A : ℝ) (c : GL (Fin a) (Cinf E)) (N : Matrix (Fin a) (Fin a) (Cinf E))
    (h1 : ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A)
    (h2 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A) :
    ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N * c.val)‖ ≤ a * a * A * A * ‖toL N‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans h1
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 := norm_toL_mul_le ((c⁻¹ : GL (Fin a) (Cinf E)).val * N) c.val
  have p2 := norm_toL_mul_le (c⁻¹ : GL (Fin a) (Cinf E)).val N
  have p2' : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ ≤ a * (A * ‖toL N‖) :=
    p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) ha)
  have p3 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ * ‖toL c.val‖ ≤ (a * (A * ‖toL N‖)) * A :=
    mul_le_mul p2' h1 (norm_nonneg _) (mul_nonneg ha (mul_nonneg hA (norm_nonneg _)))
  exact (p1.trans (mul_le_mul_of_nonneg_left p3 ha)).trans (le_of_eq (by ring))

end GlobalTheory.RapVari

open GlobalTheory.RapVari in

theorem GlobalTheory.rap_vari : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t →
    ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ R : ℝ, 0 ≤ R →
    ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧
    ∀ ψ : Sm E a, ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
    (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
    ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω,
    ∀ z : BlockIx a j → Cinf E, ‖z‖ ≤ R →
    ‖ψ.1 (infGL E a (unip z * (d * c))) - ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a t ht i j hij Ω hΩ R hR
  obtain ⟨C0, hC0, hconj⟩ := GlobalTheory.T.blockUnipotent_conj_coneDiagonal_bound E a t ht i j hij
  obtain ⟨B, Cb, hCb, hbasis⟩ := GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections E a
  obtain ⟨A, hA, hAc⟩ := exists_bound_compact hΩ
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have haA : (0 : ℝ) ≤ a * a * A * A := mul_nonneg (mul_nonneg (mul_nonneg ha ha) hA) hA
  refine ⟨(fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
      (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω), B, Cb * (a * a * A * A) * (C0 * R), ?_, ?_, ?_⟩
  · exact ((isCompact_closedBall 0 (C0 * C0 * R)).prod hΩ).image
      ((continuous_unip_inf.comp continuous_fst).mul continuous_snd)
  · exact mul_nonneg (mul_nonneg hCb haA) (mul_nonneg hC0 hR)
  intro ψ r d hr hrat hd M hM hB c hc z hz
  obtain ⟨hq, hz'⟩ := hconj r d hr hrat hd
  obtain ⟨z', hz'n, hcomm⟩ := hz' z
  have hq0 : 0 ≤ r j / r i := div_nonneg (hr j).le (hr i).le
  have hz'R : ‖z'‖ ≤ C0 * (r j / r i) * R := hz'n.trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hC0 hq0))
  have hz'R' : ‖z'‖ ≤ C0 * C0 * R :=
    hz'R.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC0) hR)
  have hu : ∀ τ : ℝ, ((c⁻¹ * unip (τ • z') * c : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + τ • ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) := by
    intro τ
    rw [Units.val_mul, Units.val_mul]
    change (c⁻¹ : GL (Fin a) (Cinf E)).val * (1 + nilM (τ • z')) * c.val = _
    rw [nilM_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hNN : ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) *
      ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) = 0 := by
    calc _ = (c⁻¹ : GL (Fin a) (Cinf E)).val *
          (nilM z' * (c.val * (c⁻¹ : GL (Fin a) (Cinf E)).val) * nilM z') * c.val := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Units.mul_inv, Matrix.mul_one, nilM_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hNnorm : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val)‖ ≤
      a * a * A * A * (C0 * (r j / r i) * R) :=
    (norm_conj_le A c _ (hAc c hc).1 (hAc c hc).2).trans
      (mul_le_mul_of_nonneg_left ((norm_toL_nilM_le z').trans hz'R) haA)
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, unip (τ • z') * c ∈
      (fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
        (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω) := by
    intro τ hτ
    refine ⟨(τ • z', c), ⟨?_, hc⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hτ.2).trans hz'R'
  have key := GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment E a ψ (infGL E a (d * c)) _ (fun τ => c⁻¹ * unip (τ • z') * c)
    (Cb * (a * a * A * A * (C0 * (r j / r i) * R)) * M) hNN hu (by
      intro τ hτ
      have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip (τ • z') * c) =
          infGL E a (d * (unip (τ • z') * c)) := by
        rw [← map_mul]; congr 1; group
      rw [e]
      refine (hbasis ψ.1 _ _ M (fun Y hY => hB Y hY _ (hmem τ hτ)) hM).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNnorm hCb) hM)
  have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip ((1 : ℝ) • z') * c) = infGL E a (unip z * (d * c)) := by
    rw [← map_mul]; congr 1
    have h1 := hcomm 1
    rw [one_smul, one_smul] at h1
    rw [one_smul, ← mul_assoc (unip z) d c, h1]
    group
  rw [e] at key
  exact key.trans (le_of_eq (by ring))
