import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.unfolding_bounded_integral

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n' c' n c : ℕ}

def extZ (c' c : ℕ) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F) :=
  Loc.inX F n c ∘ₗ z ∘ₗ LinearMap.funLeft F F (Fin.castAdd c')

theorem extZ_apply (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (v : Fin (n' + c') → F) :
    extZ c' c z v = Loc.inX F n c (z fun a => v (Fin.castAdd c' a)) := rfl

theorem unfoldingAffineLinearMap_add_eq_add_frM (xj z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) (t : Loc.FC n' c' n c → F) :
    Loc.xx1 (xj + a • z) t = Loc.xx1 xj t + a • extZ c' c z := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  change Loc.xx1 (xj + a • z) t (Pi.single s 1) l =
    Loc.xx1 xj t (Pi.single s 1) l + a * extZ c' c z (Pi.single s 1) l
  rw [linearMap_unfolding_apply_single, linearMap_unfolding_apply_single, extZ_apply, inX_apply]
  by_cases hs : s.1 < n'
  · have hf : ¬ Loc.IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
    have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) =
        Pi.single (⟨s.1, hs⟩ : Fin n') 1 := by
      funext b
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    rw [dif_neg hf, dif_neg hf, dif_pos hs, dif_pos hs, e]
    split_ifs with hl
    · simp
    · simp
  · have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) = 0 := by
      funext b
      have := b.2
      rw [Pi.single_apply, if_neg]
      · rfl
      · intro h
        apply hs
        rw [← h]
        simp
    rw [e, map_zero, dif_neg hs, dif_neg hs]
    simp

theorem chArg_add (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) :
    Loc.chArg (x + a • extZ c' c z) = Loc.chArg x := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul, extZ_apply,
    atN_of_mem_Ufl (inX_mem_Ufl i _), mul_zero, add_zero]

end SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {v : Fin n → E} (hv : IntV P v) : IntV P (Loc.inX E n c v) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hv _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfold_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (N A B : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), HomBdd P N Psi → (∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj ≠ 0 → IntHom P (((qOf P : E) ^ N) • xj)) ∧ ∀ xj z : (Fin n' → E) →ₗ[E] (Fin n → E), IntHom P z → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi (xj + ((qOf P : E) ^ N) • z) = GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj := by
  intro E _ _ K _ P n' c' n c psi N A B Psi hPsi
  refine ⟨fun xj hx => ?_, fun xj z hz => ?_⟩
  · unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1 at hx
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    have h := hPsi.1 _ (left_ne_zero_of_mul ht)
    intro v hv a
    have h2 := h _ (intV_inX (c := c') hv) (Fin.castAdd c a)
    rw [LinearMap.smul_apply, unfoldingAffinePointMap_apply_inclusion, Pi.smul_apply, inX_castAdd] at h2
    exact h2
  · have hy : IntHom P (extZ c' c z) := fun v hv => by
      rw [extZ_apply]
      exact intV_inX (hz _ fun a => hv _)
    unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [unfoldingAffineLinearMap_add_eq_add_frM, chArg_add, hPsi.2 _ _ hy]

end GlobalTheory.Proof.unfolding_bounded_integral
