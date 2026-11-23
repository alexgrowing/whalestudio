import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem continuous_aeval_comp {Γ k : Type} [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] (f : Γ → k) (hf : Continuous f) (P : MvPolynomial Γ ℤ) :
    Continuous fun u : Γ → Γ => MvPolynomial.aeval (f ∘ u) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Function.comp_apply]
    exact hp.mul (hf.comp (continuous_apply j))

theorem polyApprox_of_denseRange : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (T : Γ → PadicAlgCl l), Continuous T →
    ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) →
    PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) → PolyApprox T (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx T hT C hC h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  have hch : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! ρ hρC hρη using hch
  have inj : Set.InjOn (fun η => trc (ρ η)) (s : Set (J → PadicAlgCl l)) := by
    intro η₁ h₁ η₂ h₂ e
    rw [← hρη η₁ h₁, ← hρη η₂ h₂]
    simp only at e
    rw [e]
  refine ⟨s.image (fun η => trc (ρ η)), fun σ => c (fun j => σ (x j)), ?_, fun P => ?_⟩
  · intro σ hσ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hσ
    obtain ⟨η, hη, rfl⟩ := hσ
    exact ⟨ρ η, hρC η hη, rfl⟩
  rw [Finset.sum_image inj]
  have hc : ∀ η ∈ s, c (fun j => trc (ρ η) (x j)) = c η := fun η hη => by rw [hρη η hη]
  rw [Finset.sum_congr rfl (fun η hη => by rw [show (fun σ : Γ → PadicAlgCl l => c fun j => σ (x j)) (trc (ρ η)) = c η from hc η hη])]
  have htr : ∀ η ∈ s, Continuous (trc (ρ η)) := fun η hη =>
    (Units.continuous_val.comp (hC _ (hρC η hη))).matrix_trace
  let F : (Γ → Γ) → PadicAlgCl l := fun u =>
    MvPolynomial.aeval (T ∘ u) P - ∑ η ∈ s, c η * MvPolynomial.aeval (trc (ρ η) ∘ u) P
  have hF : Continuous F := by
    refine (continuous_aeval_comp T hT P).sub (continuous_finset_sum _ fun η hη => ?_)
    exact continuous_const.mul (continuous_aeval_comp _ (htr η hη) P)
  have key : ‖F id‖ ≤ ε := by
    refine (DenseRange.piMap (fun _ : Γ => hx)).induction_on (p := fun u => ‖F u‖ ≤ ε) id
      (isClosed_le (continuous_norm.comp hF) continuous_const) fun v => ?_
    have e1 : MvPolynomial.aeval (T ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval (fun j => T (x j)) (MvPolynomial.rename v P) := by
      rw [MvPolynomial.aeval_rename]; rfl
    have e2 : ∀ η ∈ s, MvPolynomial.aeval (trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval η (MvPolynomial.rename v P) := fun η hη => by
      have e3 : trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v = η ∘ v := by
        funext i
        simp only [Function.comp_apply, Pi.map_apply]
        exact congrFun (hρη η hη) (v i)
      rw [MvPolynomial.aeval_rename, e3]
    have := hP (MvPolynomial.rename v P)
    simp only [F]
    rw [e1, Finset.sum_congr rfl (fun η hη => by rw [e2 η hη])]
    exact this
  exact key

end GlobalTheory.Cong
