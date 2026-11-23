import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma idempotent_corner_part_mul {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) :
    (E * g * E + (1 - E) * g * (1 - E)) * (E * h * E + (1 - E) * h * (1 - E)) =
      E * (g * h) * E + (1 - E) * (g * h) * (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, h2, sub_zero]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * (g * h) * E = E * g * E * h * E := by
    calc E * (g * h) * E = E * g * (E + F) * h * E := by rw [hs]; noncomm_ring
      _ = E * g * E * h * E + E * g * (F * h * E) := by noncomm_ring
      _ = _ := by rw [hh, mul_zero, add_zero]
  have a2 : F * (g * h) * F = F * g * F * h * F := by
    calc F * (g * h) * F = F * g * (E + F) * h * F := by rw [hs]; noncomm_ring
      _ = (F * g * E) * h * F + F * g * F * h * F := by noncomm_ring
      _ = _ := by rw [hg, zero_mul, zero_mul, zero_add]
  rw [a1, a2]
  calc _ = E * g * (E * E) * h * E + E * g * (E * F) * h * F + F * g * (F * E) * h * E
        + F * g * (F * F) * h * F := by noncomm_ring
    _ = _ := by rw [hE, h1, h2, h3]; noncomm_ring

private lemma idempotent_corner_sum_one {A : Type} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [this, hE, sub_self, mul_zero, add_zero]

private lemma idempotent_corner_part_inv {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) (hgh : g * h = 1) :
    g * (E * h * E + (1 - E) * h * (1 - E)) = 1 + E * (-(g * E * h) * (1 - E)) := by
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * g * E = g * E := by
    calc E * g * E = E * g * E + F * g * E := by rw [hg, add_zero]
      _ = (E + F) * g * E := by noncomm_ring
      _ = _ := by rw [hs, one_mul]
  have a2 : h = (E * h * E + F * h * F) + E * h * F := by
    calc h = (E + F) * h * (E + F) := by rw [hs, one_mul, mul_one]
      _ = (E * h * E + F * h * F) + E * h * F + F * h * E := by noncomm_ring
      _ = _ := by rw [hh, add_zero]
  have a3 : g * (E * h * E + F * h * F) + g * (E * h * F) = 1 := by
    rw [← mul_add, ← a2, hgh]
  calc g * (E * h * E + F * h * F) = 1 - g * E * h * F := by
        rw [← a3]; noncomm_ring
    _ = 1 - E * g * E * h * F := by rw [a1]
    _ = _ := by noncomm_ring

theorem isPre_blk_image :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  intro ι _ _ Γ e hΓ he htri
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hmul : ∀ g ∈ Γ, ∀ h ∈ Γ, blk e g * blk e h = blk e (g * h) := fun g hg h hh =>
    idempotent_corner_part_mul _ g h hE (htri g hg) (htri h hh)
  have hone : blk e (1 : Matrix ι ι ℂ) = 1 := idempotent_corner_sum_one _ hE
  have hga : ∀ g ∈ Γ, g * g.adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hΓ.det_eq g hg, one_smul]
  have hinv : ∀ g ∈ Γ, blk e g * blk e g.adjugate = 1 := fun g hg => by
    rw [hmul g hg _ (hΓ.adj_mem g hg), hga g hg, hone]
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => by
    have h1 := idempotent_corner_part_inv _ g g.adjugate hE (htri g hg) (htri _ (hΓ.adj_mem g hg)) (hga g hg)
    have h2 : (g * blk e g.adjugate).det = 1 := by
      unfold blk
      rw [h1, Matrix.det_one_add_mul_comm, mul_assoc, sub_mul, one_mul, hE, sub_self, mul_zero,
        add_zero, Matrix.det_one]
    rw [Matrix.det_mul, hΓ.det_eq g hg, one_mul] at h2
    have h3 := congrArg Matrix.det (hinv g hg)
    rwa [Matrix.det_mul, h2, mul_one, Matrix.det_one] at h3
  refine ⟨⟨1, hΓ.one_mem, hone⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h, hΓ.mul_mem g hg h hh, (hmul g hg h hh).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.adjugate, hΓ.adj_mem g hg, ?_⟩
    calc blk e g.adjugate = ((blk e g).adjugate * blk e g) * blk e g.adjugate := by
          rw [Matrix.adjugate_mul, hdet g hg, one_smul, one_mul]
      _ = _ := by rw [mul_assoc, hinv g hg, mul_one]
  · rintro _ ⟨g, hg, rfl⟩
    exact hdet g hg
  · rintro σ _ ⟨g, hg, rfl⟩
    refine ⟨g.map σ, hΓ.aut_mem σ g hg, ?_⟩
    have hσ : (σ : ℂ →+* ℂ).mapMatrix (e.map (algebraMap ℚ ℂ)) = e.map (algebraMap ℚ ℂ) := by
      ext i j
      simp
    change _ = (σ : ℂ →+* ℂ).mapMatrix (blk e g)
    unfold blk
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_sub, map_one, hσ]
    rfl

end GlobalTheory.ClassFin
