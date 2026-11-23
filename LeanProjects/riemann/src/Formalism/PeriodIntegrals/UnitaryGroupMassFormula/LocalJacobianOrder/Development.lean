import Mathlib
import Formalism.PeriodIntegrals.LocJacOrd

noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v

def SdNormO : Prop :=
  (∀ (ι : Type) [Fintype ι] [Nonempty ι], sdE (E := E) ψ v ι = 0) ∨
  ∃ m : ℝ, 0 < m ∧ ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧
    (sdE (E := E) ψ v ι (Obox (E := E) v ι)).toReal = m ^ Fintype.card ι

def VolZZO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ ((r + 1) * (r + 1)) →
      (μ (ZZOrd (E := E) v r)).toReal =
        m ^ ((r + 1) * (r + 1)) *
          ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹

def VolUO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (UIdx r → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ Fintype.card (UIdx r) →
      ((μ.prod μ) (localVolumeOrdinary (E := E) v r)).toReal =
        ∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)

def VolPO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPOrd (E := E) v r l)).toReal =
          m * (absV v (alp v r l) ^ 4)⁻¹

def ArithO : Prop :=
  ∀ (typed : Prop) (g r : ℕ) (m : ℝ), ¬ typed →
    m ^ ((r + 1) * (r + 1)) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹) *
        jacS v typed g r =
      (∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)) *
        ∏ l : Fin (r + 1), (m * (absV v (alp v r l) ^ 4)⁻¹)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

theorem locJacOrd_of (h0 : SdNormO (E := E) ψ v) (hZ : VolZZO (E := E) v) (hU : VolUO (E := E) v)
    (hP : VolPO (E := E) v) (hA : ArithO (F := F) v) : LocJacOrd (E := E) ψ v := by
  intro typed g r hfin ht
  rcases h0 with h0 | ⟨m, -, h0⟩
  · have h1 : sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) = 0 := h0 _
    have h2 : sdE (E := E) ψ v Unit = 0 := h0 _
    have h3 : ∏ l : Fin (r + 1), volC (E := E) ψ v (PPOrd (E := E) v r l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [volC, h2])
    simp [volS, h1, h3]
  · obtain ⟨hZH, hZv⟩ := h0 (Fin (r + 1) × Fin (r + 1))
    obtain ⟨hUH, hUv⟩ := h0 (UIdx r)
    obtain ⟨hCH, hCv⟩ := h0 Unit
    have hZv' : (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (Obox (E := E) v _)).toReal =
        m ^ ((r + 1) * (r + 1)) := by rw [hZv]; simp [Fintype.card_prod]
    have hCv' : (sdE (E := E) ψ v Unit (Obox (E := E) v Unit)).toReal = m := by rw [hCv]; simp
    have eZ := hZ r m hfin _ hZH hZv'
    have eU := hU r m hfin _ hUH hUv
    have eP := hP r m hfin _ hCH hCv'
    unfold volS volU volC
    rw [eZ, eU]
    simp only [eP]
    exact hA typed g r m ht

end PI.LocJacOrd.W
