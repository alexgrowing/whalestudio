import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.NegDS

variable {n : ℕ} {ε ε' : Fin n → Bool}

theorem sign_eq_iff (he : ∀ a, ε' a = !ε a) (a b : Fin n) : ε' a = ε' b ↔ ε a = ε b := by
  rw [he a, he b]
  cases ε a <;> cases ε b <;> simp

theorem Jm_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Jm ε' = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_neg]
  congr 1
  funext a
  rw [he a]
  cases ε a <;> simp

theorem UJset_flip (he : ∀ a, ε' a = !ε a) : Formalism.MainNotions.S.UJset ε' = Formalism.MainNotions.S.UJset ε := by
  ext g
  show Formalism.REAL.inUJ ε' g ↔ Formalism.REAL.inUJ ε g
  unfold Formalism.REAL.inUJ
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem Kset_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Kset ε' = Formalism.REAL.Kset ε := by
  ext g
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε' = Formalism.REAL.Jm ε' * g ↔
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoC ε' = Formalism.REAL.rhoC ε := by
  funext a
  simp only [Formalism.REAL.rhoC, sign_eq_iff he]

theorem rhoN_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoN ε' = Formalism.REAL.rhoN ε := by
  funext a
  simp only [Formalism.REAL.rhoN, ne_eq, sign_eq_iff he]

theorem lowK_flip (he : ∀ a, ε' a = !ε a) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε' lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK
  rw [rhoC_flip he, rhoN_flip he]

theorem vNormSq_flip (he : ∀ a, ε' a = !ε a) (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq ε' μ = Formalism.MainNotions.S.vNormSq ε μ := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [rhoC_flip he]

theorem cdom_flip (he : ∀ a, ε' a = !ε a) (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom ε' μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp only [Formalism.MainNotions.S.CDom, sign_eq_iff he]

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kstable_flip (he : ∀ a, ε' a = !ε a) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε' σ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ S := by
  simp only [Formalism.MainNotions.S.IsKStableOn, Kset_flip he]

theorem ktype_flip (he : ∀ a, ε' a = !ε a) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε' σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, kstable_flip he, Kset_flip he, cdom_flip he]

end Rep

def flipU (he : ∀ a, ε' a = !ε a) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).1 g.2⟩
  invFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem flipU_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he) := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem flipU_symm_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he).symm := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem memLp_flip (he : ∀ a, ε' a = !ε a) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU he) 2 (Formalism.REAL.muG ε') := by
  have hc := flipU_cont he
  have hcs := flipU_symm_cont he
  let eH : Formalism.REAL.UJ ε' ≃ₜ Formalism.REAL.UJ ε := ⟨(flipU he).toEquiv, hc, hcs⟩
  have hme : MeasurableEmbedding (flipU he) := eH.measurableEmbedding
  haveI : (Measure.map (flipU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (flipU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (flipU he) (Formalism.REAL.muG ε') =
      MeasureTheory.Measure.haarScalarFactor (Measure.map (flipU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  rw [← hme.memLp_map_measure_iff, hmap, ENNReal.smul_def]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem sqInt_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : ∀ a, ε' a = !ε a) (h : Formalism.MainNotions.S.IsSqIntOn ε σ) : Formalism.MainNotions.S.IsSqIntOn ε' σ := by
  intro v w
  have e : Formalism.MainNotions.S.coefOn (ε := ε') σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU he := by
    funext g
    rfl
  rw [e]
  exact memLp_flip he (h v w)

theorem isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ h
  have he : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl
  unfold Formalism.MainNotions.S.IsDS at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, sqInt_flip he h5, ?_, ?_⟩
  · rw [UJset_flip he]
    exact h3
  · rw [UJset_flip he]
    exact h4
  · obtain ⟨S, hS⟩ := h6
    exact ⟨S, by rw [lowK_flip he, ktype_flip he]; exact hS⟩
  · intro μ S hS
    rw [lowK_flip he, vNormSq_flip he, vNormSq_flip he]
    exact h7 μ S ((ktype_flip he μ S).1 hS)

end GlobalTheory.CompanionTheory.NegDS

end
