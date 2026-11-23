import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isVolMeasG_const (D : D7) (W : HSp D) (P Q : ℕ) (μ : Measure (GA D W)) :
    IsVolMeasG D W (fun _ => P) (fun _ => Q) μ ↔ IsVolMeas D W P Q μ := Iff.rfl

theorem volTie_of_volTieG (D : D7) (h : VolTieG D) : VolTie D := by
  intro W P Q hW hs
  have h1 := h W hW
  simp only [hs] at h1
  exact h1

theorem gq_smul (D : D7) (W : HSp D) (γ : GQ W) (g : GA D W) : γ • g = (γ : GA D W) * g := rfl

theorem top_AE (D : D7) : (inferInstance : TopologicalSpace (AE D)) = moduleTopology (AF D.host.F) (AE D) := rfl

theorem not_isVolMeasG_zero (D : D7) (W : HSp D) (P Q : D.what₂.Tau → ℕ) : ¬ IsVolMeasG D W P Q 0 := by
  intro h
  have := h.1
  have h2 := (isOpen_univ (X := GA D W)).measure_ne_zero (0 : Measure (GA D W)) ⟨1, trivial⟩
  simp at h2

theorem congr_of_isVolMeasG (D : D7) (W : HSp D) (P Q : D.what₂.Tau → ℕ) (μ : Measure (GA D W))
    (h : IsVolMeasG D W P Q μ) (ρ : D.what₂.Tau) :
    ∃ A : Matrix (Fin (P ρ) ⊕ Fin (Q ρ)) (Fin W.rank) ℂ, Aᴴ * Formalism.UG.Jpq (P ρ) (Q ρ) * A = gramAt D W ρ := by
  obtain ⟨-, ⟨θ, hθ⟩, h2⟩ := h
  obtain ⟨⟨A, hA⟩, -⟩ := h2 θ hθ
  exact ⟨A ρ, hA ρ⟩

theorem one_hecke (D : D7) : IsHeckeChar D 1 ∧ UnramEverywhere D 1 :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ => rfl⟩

theorem not_resEta_one (D : D7) : ¬ ResEta D 1 1 := by
  rintro ⟨⟨η, hη⟩, h⟩
  apply hη.2.2.2
  ext1 a
  simpa using (h η hη a).symm

theorem resEta_zero_iff (D : D7) (χ : (AE D)ˣ →* Circle) :
    ResEta D χ 0 ↔ (∃ η, IsEta D η) ∧ ∀ a, χ (idF D a) = 1 := by
  constructor
  · rintro ⟨⟨η, hη⟩, h⟩
    exact ⟨⟨η, hη⟩, fun a => by simpa using h η hη a⟩
  · rintro ⟨h1, h⟩
    exact ⟨h1, fun η _ a => by simpa using h a⟩

theorem not_hasInfExp_third (D : D7) (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) : ¬ HasInfExp D χ τ (1 / 3) := by
  rintro ⟨n, hn, -⟩
  have h3 : (3 * n : ℚ) = 2 := by rw [hn]; norm_num
  have h4 : 3 * n = 2 := by exact_mod_cast h3
  omega

theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

theorem isomEmb_inj (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (h : HSpace.IsIsomEmb V' V ι) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply V'.nondeg.1
  intro y
  rw [← h x y, hx]
  simp

end GlobalTheory.VolHeckeCheck

end
