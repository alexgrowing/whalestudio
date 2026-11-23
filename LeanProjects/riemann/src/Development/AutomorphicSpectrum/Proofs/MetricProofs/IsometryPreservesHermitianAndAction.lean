import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = star c * R.ip x y := by
  simp [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem real_smul_eq' (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem ip_period_im (R : RiemLat E g Λ) (x y : Λ) : (R.ip (R.P x) (R.P y)).im = R.form y x :=
  R.im y x

theorem isometry_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (x y : Fin g → ℂ) : R'.ip (φ x) (φ y) = R.ip x y := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z w => R'.ip (φ z) (φ w) - R.ip z w
  have hl : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [D, map_add, ip_add_left']
    ring
  have hr : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    simp only [D, map_add, ip_add_right']
    ring
  have hcl : ∀ (c : ℂ) z w, D (c • z) w = star c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_left']
    ring
  have hcr : ∀ (c : ℂ) z w, D z (c • w) = c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_right']
    ring
  have h0l : ∀ w, D 0 w = 0 := fun w => by
    simp [D, RiemLat.ip]
  have h0r : ∀ z, D z 0 = 0 := fun z => by
    simp [D, RiemLat.ip]
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    simp only [D, Complex.sub_im]
    rw [← hP, ← hP, ip_period_im, ip_period_im, hf, sub_self]
  have s1 : ∀ l w, (D (R.P l) w).im = 0 := fun l w => by
    have hw : w ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add w w' _ _ h h' => simp [hr, h, h']
    | smul r w _ h =>
      rw [real_smul_eq', hcr]
      simp [h]
  have s2 : ∀ z w, (D z w).im = 0 := fun z w => by
    have hz : z ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l w
    | zero => simp [h0l]
    | add z z' _ _ h h' => simp [hl, h, h']
    | smul r z _ h =>
      rw [real_smul_eq', hcl]
      simp [h]
  have s3 : (D x y).re = 0 := by
    have h := s2 x (Complex.I • y)
    rw [hcr] at h
    simpa using h
  have s4 : D x y = 0 := Complex.ext s3 (s2 x y)
  exact sub_eq_zero.mp s4

theorem commutes_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (a : 𝓞 E) (x : Fin g → ℂ) : φ (R.B a x) = R'.B a (φ x) := by
  have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, rfl⟩ := h
    rw [← R.act, ← hP, ← hP, map_smul, R'.act]
  | zero => simp
  | add x x' _ _ h h' => simp [h, h']
  | smul r x _ h =>
    rw [real_smul_eq', map_smul, map_smul, h, map_smul, map_smul]

theorem isometry_and_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) →
    (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  intro E _ _ _ g Λ _ _ R R' γ φ hf hP
  have hs := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  exact ⟨isometry_of_periods R R' hs γ φ hf hP, commutes_of_periods R R' hs γ φ hP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso
