import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseATwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantOperatorBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeDecay

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (a n N : ℕ), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (h : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (l : (AE F E)ˣ), l ∈ idelesAt E (evI F) →
      (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N * SchwartzMap.seminorm ℂ a n (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) h)) ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) h := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev _ hev hpure a n N
  obtain ⟨m, y, K, hK⟩ := GlobalTheory.T.triple_pair_period_identity_case_a_two F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁
  have hinv := GlobalTheory.T.triple_pair_period_identity_case_a F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hev hpure
  let U : Fin m → _ := fun j => GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (y j) (incV F H'.x))
  have hU : ∀ (j : Fin m) (s : ℝ) (f g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      ⇑g = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) (s • U j) ⇑f → ei g = ei f := by
    intro j s f g hg
    refine hinv (realAd F s • y j) f g ?_
    rw [hg]
    congr 1
    simp only [U]
    rw [← GlobalTheory.ArchUniq.Coord.coordI_smul, Matrix.smul_vecMulVec]
  obtain ⟨M, hM⟩ := GlobalTheory.T.schrodinger_invariant_operator_bound _ (GlobalTheory.ArchUniq.Coord.isPairing_trP _) ei U hU a n
  obtain ⟨s, C, hsC⟩ := hM (N + M)
  refine ⟨s, C * K ^ (N + M), fun h l hl => ?_⟩
  have hg := (locOpInf_rho G.M.co hT.base.std (shiftA H H' l) h).2
  have key := hsC (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l)) h _ hg
  have hK' := hK l hl
  set A := 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ with hA
  set O := 1 + ∑ j, |GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l)) (U j)| with hO
  set Wn := 1 + ‖GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l)‖ with hWn
  set p := SchwartzMap.seminorm ℂ a n (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) h))
  set S := (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) h
  have hS0 : 0 ≤ ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hO1 : 1 ≤ O := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hp : 0 ≤ p := apply_nonneg _ _
  have hWpos : 0 < Wn := by positivity
  have h1 : A ≤ K * O := by linarith [norm_nonneg (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l))]
  have h2 : Wn ≤ K * O := by linarith
  have hA0 : 0 ≤ A := by linarith
  have h3 : A ^ N * Wn ^ M ≤ K ^ (N + M) * O ^ (N + M) := by
    rw [← mul_pow, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hA0 h1 N) (pow_le_pow_left₀ hWpos.le h2 M) (pow_nonneg hWpos.le M)
      (pow_nonneg (hA0.trans h1) N)
  have h4 : A ^ N * p * Wn ^ M ≤ C * K ^ (N + M) * S * Wn ^ M := by
    calc A ^ N * p * Wn ^ M = (A ^ N * Wn ^ M) * p := by ring
      _ ≤ (K ^ (N + M) * O ^ (N + M)) * p := by gcongr
      _ = K ^ (N + M) * (O ^ (N + M) * p) := by ring
      _ ≤ K ^ (N + M) * (C * Wn ^ M * S) := by
          have hKp : 0 ≤ K := by
            by_contra hneg
            push_neg at hneg
            nlinarith
          exact mul_le_mul_of_nonneg_left key (pow_nonneg hKp _)
      _ = C * K ^ (N + M) * S * Wn ^ M := by ring
  exact le_of_mul_le_mul_right h4 (pow_pos hWpos M)

end GlobalTheory.ConeDecay
