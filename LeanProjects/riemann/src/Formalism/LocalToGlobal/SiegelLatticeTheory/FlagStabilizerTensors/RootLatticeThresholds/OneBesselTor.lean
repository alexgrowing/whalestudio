import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.OBT

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.FrameBoundFromBesselTorus

section Defs

variable {k r : ℕ}

def coefH (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) :
    Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => P.comp ((L.σ x).comp Q)

def IsKFinPair (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) : Prop :=
  (∀ w, IsKFinHpk (k := k) (r := r) L.σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) L.σ (ContinuousLinearMap.adjoint P x))

def HasBData (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Λ : ℂ)
    (Φ : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Ψ : Mx k r → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp)) : Prop :=
  (∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb k * μ = Hb k → L.J F (bigCell k r c μ) = Λ • Φ (bigCell k r c μ)) ∧
    (∀ (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
      Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
      IsOrbQuot L g μR ν → OrbInt L F g ν = Λ • Ψ g ν)

end Defs

def RankOneTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (κ₀ : ℝ),
    0 < κ₀ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    ∃ (Φ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
      (Ψ : Mx D.R.k D.R.rS → Measure (PairSp D.R.k D.R.rS) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ)
      (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj D.R.k D.R.rS κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0)

section Zero

variable {k r : ℕ}

theorem isKFinHpk_zero (L : LocBessel k r) : IsKFinHpk (k := k) (r := r) L.σ (0 : L.Hs) := by
  exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx
    simp [hx]⟩

theorem J_zero (L : LocBessel k r) (g : Mx k r) : L.J (fun _ => 0) g = 0 := by
  simp [LocBessel.J, Formalism.QuantumDeterminants.besselJ]

theorem orbInt_zero (L : LocBessel k r) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt L (fun _ => 0) g ν = 0 := by
  simp [OrbInt, besselIntg]

end Zero

theorem oneBesselTor_of_rankOne (D : D7) (Cgf : ℝ) (h : RankOneTor D Cgf) : OneBesselTor D Cgf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hN hN' hε hgap hf
  obtain ⟨Φ, Ψ, Λ₀, Λ, h1, h2, h3⟩ := h L κ₀ hκ₀ hc hN hN' hε hgap
  obtain ⟨P, Q, hQ, hP, hfPQ⟩ := hf
  have hfeq : f = coefH L P Q := funext fun g => hfPQ g
  subst hfeq
  have hPQ : IsKFinPair L P Q := ⟨hQ, hP⟩
  by_cases h0 : Λ₀ P Q = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun w => by simpa using isKFinHpk_zero L,
      fun x => by simpa using isKFinHpk_zero L, fun g => by simp⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      show L.J (fun _ => 0) _ = _
      rw [(h1 P Q hPQ).1 c μ hc0 hμ, h0, J_zero]
      simp
    · intro γ g μR ν hG hrep hst hroot hq
      show OrbInt L (fun _ => 0) g ν = _
      rw [(h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, h0, orbInt_zero]
      simp
  · obtain ⟨P₁, Q₁, hPQ₁, hΛ⟩ := h3 κ τ hκ hτ P Q hPQ h0
    refine ⟨coefH L P₁ Q₁, Λ P₁ Q₁ κ τ / Λ₀ P Q, div_ne_zero hΛ h0,
      ⟨P₁, Q₁, hPQ₁.1, hPQ₁.2, fun g => rfl⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).1 c μ hc0 hμ, (h1 P Q hPQ).1 c μ hc0 hμ, smul_smul,
        div_mul_cancel₀ _ h0]
    · intro γ g μR ν hG hrep hst hroot hq
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).2 γ g μR ν hG hrep hst hroot hq,
        (h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, smul_smul, div_mul_cancel₀ _ h0]

end Formalism.L2.SG.Pf.OBT
