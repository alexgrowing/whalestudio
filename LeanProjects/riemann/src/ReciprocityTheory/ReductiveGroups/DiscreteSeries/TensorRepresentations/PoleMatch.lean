import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatchA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem pole_match (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ s, z = poleF dual lam s) ∧
      ∀ (s : Fin n) (P : Module.End ℂ (Fin n → D)), IsGKEndo dual ε σ E (genSub E V) P →
        (∀ f ∈ tensSub (genSub E V), P (P f) = P f) →
        (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g)) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = poleF dual lam s • P f) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → P f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ poleF dual lam s → eeF dual E f = z' • f → P f = 0) →
        ∀ x ∈ genSub E V, ptr P x = ((ratioF dual lam s : ℝ) : ℂ) • x := by
  obtain ⟨B, c, P, hev, -, -, hP1, -, hc0, hQ, hfib, -⟩ := pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  refine ⟨fun z f hf hf0 hz => ?_, fun s Q _ _ _ _ hQ1 hQ0 x hx => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hev z f hf hf0 hz
    have hcne : c b ≠ 0 := fun h0 => hf0 (by rw [← hP1 b f hf hz]; exact hc0 b h0 f hf)
    have h1 := hfib ((b : ℝ) : ℂ)
    rw [pm_sum_single hb] at h1
    by_contra hne
    simp only [not_exists] at hne
    rw [Finset.filter_eq_empty_iff.2 (fun s _ h => hne s h.symm), Finset.sum_empty] at h1
    exact hcne h1
  · rw [hQ Q _ hQ1 hQ0 x hx, hfib, pm_filter_pole dual hgap.1 s, Finset.sum_singleton]

theorem pole_zero (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) (s : Fin n) :
    ratioF dual lam s = 0 ↔ ∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → f = 0 := by
  obtain ⟨B, c, P, hev, hPM, hPz, hP1, hcb, hc0, -, hfib, x₀, hx₀, hx₀0⟩ :=
    pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  have h1 := hfib (poleF dual lam s)
  rw [pm_filter_pole dual hgap.1 s, Finset.sum_singleton] at h1
  constructor
  · intro h0 f hf hz
    by_contra hf0
    obtain ⟨b, hb, hzb⟩ := hev _ f hf hf0 hz
    have hcne : c b ≠ 0 := fun h => hf0 (by rw [← hP1 b f hf (hzb ▸ hz)]; exact hc0 b h f hf)
    rw [hzb, pm_sum_single hb, h0, Complex.ofReal_zero] at h1
    exact hcne h1
  · intro hno
    have hsum : (∑ b ∈ B, if ((b : ℝ) : ℂ) = poleF dual lam s then c b else 0) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      split_ifs with h
      · have hz : ∀ f ∈ tensSub (genSub E V), P b f = 0 := fun f hf =>
          hno _ (hPM b f hf) (by rw [hPz b f hf, h])
        have h2 : c b • x₀ = 0 := by
          rw [← hcb b x₀ hx₀, ptr_apply]
          exact sum_eq_zero fun i _ => by rw [hz _ (pm_single_mem _ hx₀ _)]; rfl
        exact (smul_eq_zero.1 h2).resolve_right hx₀0
      · rfl
    rw [hsum] at h1
    exact_mod_cast h1.symm

end ReciprocityTheory.ChartRestriction.DS
