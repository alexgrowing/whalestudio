import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegIsFdegCayley

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal

def deg_DSUniq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsHCParam ν → IsDS ε ν σ → IsDS ε ν σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

def DegreeL2RangeHypothesis (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), IsHCParam ν →
    l1dist ν (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) ν σ → ∀ v w : H, IsKFin (epsSH D.R) σ v → IsKFin (epsSH D.R) σ w →
        MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG (epsSH D.R))

theorem deg_hc_add_single {n : ℕ} {μ : Fin n → ℝ} (h : IsHCParam μ) (hg : AllGaps μ 2) (s : Fin n) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h1 := h.1 hab
    have h2 := hg a b (ne_of_lt hab)
    rw [abs_of_pos (by linarith)] at h2
    have ha : (0 : ℝ) ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) a := by by_cases e : a = s <;> simp [Pi.single_apply, e]
    have hb : (Pi.single s (1 : ℝ) : Fin n → ℝ) b ≤ 1 := by by_cases e : b = s <;> simp [Pi.single_apply, e]
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨m, hm⟩ := h.2 a
    by_cases e : a = s
    · subst e
      exact ⟨m + 1, by simp only [Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m, by simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]; exact hm⟩

theorem deg_chain {n : ℕ} {ε : Fin n → Bool} (D : D7) (h18 : OnePlaceEstimates.adm18 D) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) {μ : Fin n → ℝ}
    (hμ : IsHCParam μ) (hgap : ∀ I : Finset (Fin n), AllGaps (μ + epsI I) 2)
    (hL2 : ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε (μ + epsI I) σ →
      ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
        MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε))
    (H0 : Type) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] [CompleteSpace H0]
    (σ0 : Matrix (Fin n) (Fin n) ℂ → (H0 →L[ℂ] H0)) (hDS0 : IsDS ε μ σ0) (v0 : H0) (hv0 : v0 ≠ 0)
    (hd0 : fdegOf (Formalism.REAL.muG ε) σ0 v0 ≠ 0) :
    ∀ I : Finset (Fin n), IsHCParam (μ + epsI I) →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), v ≠ 0 ∧ IsDS ε (μ + epsI I) σ ∧
          fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0 = fdegHC (μ + epsI I) / fdegHC μ := by
  have hf0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · refine ⟨H0, inferInstance, inferInstance, inferInstance, σ0, v0, hv0, ?_, ?_⟩
    · rw [deg_epsI_empty, add_zero]; exact hDS0
    · rw [deg_epsI_empty, add_zero, div_self hd0, div_self hf0.ne']
  · intro I a ha h1 h2 ih
    obtain ⟨H, i1, i2, i3, σ, v, hv, hDS, hr⟩ := ih
    obtain ⟨X, hX⟩ := h18 n ε (μ + epsI I) H σ h1 hDS (fun s => deg_hc_add_single h1 (hgap I) s)
    have haS : a ∈ X.Sm := (hX a).2 h2
    have hDSa := (X.ds a haS).2
    haveI : Nontrivial (X.Hs a) := hDSa.2.1
    obtain ⟨vs, hvs⟩ := exists_ne (0 : X.Hs a)
    have h9 := h90 n ε (μ + epsI I) H σ X h1 hDS (hL2 I h1 H σ hDS) a haS v vs hv hvs
    rw [← Formalism.QuantumDeterminants.fdegRatio n (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective] at h9
    have hp1 := deg_fdeg_pos h1
    have hp2 := deg_fdeg_pos h2
    have hne : fdegOf (Formalism.REAL.muG ε) σ v ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hr
      exact (div_pos hp1 hf0).ne hr
    refine ⟨X.Hs a, inferInstance, inferInstance, inferInstance, X.σs a, vs, hvs, ?_, ?_⟩
    · rw [deg_epsI_insert I a ha, ← add_assoc]; exact hDSa
    · rw [deg_epsI_insert I a ha, ← add_assoc]
      calc fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ0 v0
          = (fdegOf (Formalism.REAL.muG ε) (X.σs a) vs / fdegOf (Formalism.REAL.muG ε) σ v) *
              (fdegOf (Formalism.REAL.muG ε) σ v / fdegOf (Formalism.REAL.muG ε) σ0 v0) := by field_simp
        _ = (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) * (fdegHC (μ + epsI I) / fdegHC μ) := by
            rw [h9, hr]
        _ = fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ := by field_simp

theorem deg_datum (D : D7) {W : LocW D.R.k D.R.rS} {ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D ν A) : ∃ P : MatKR D.R.k D.R.rS, IsDS (epsSH D.R) ν (fun g => A.σ (P⁻¹ * g * P)) ∧
      ∀ v : A.H, v ≠ 0 → fdegOf (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) v =
        ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ) * A.deg := by
  obtain ⟨_, ⟨P', hP', hDS⟩, _, _, _, _, _, _, _, _, P, hP, hF⟩ := hA
  refine ⟨P', hDS, fun v hv => ?_⟩
  have h1 := deg_isFdeg_cayley _ A.σ P P' hP hP'.1 hDS.2.2.1 A.deg hF
  rw [deg_fdegOf_smul (D.s.cdScale _ (epsSH D.R)) (D.s.cdScale_pos _ _), deg_fdegOf _ _ A.deg v h1 hv]

end Formalism.MainNotions.BridgeLemma₂

end
