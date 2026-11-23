import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_complex_linear_of_pure_types_of_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ N hN hsp h₁ h₂
  obtain ⟨r, hr⟩ := exists_real_extension_of_lattice P hP.2.1 hP.2.2.1 hP.2.2.2.1
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  have hr' : ∀ a, r (P a) = P' (Φ a) := hr
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 ∧ H.rt0.im ≠ 0 := by
    have e₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have e₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at e₁ e₂
    have him : H.rt0.im ≠ 0 := fun h => by
      rw [h] at e₁; nlinarith [mul_self_nonneg H.rt0.re]
    refine ⟨?_, him⟩
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hρ : H.rt0 = (H.rt0.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre.1]
  have key : ∀ (ρ : ℂ) (a : D.La), a ∈ lat hP ρ → Φ a ∈ lat hP' ρ → r (ρ • P a) = ρ • r (P a) := by
    intro ρ a ha ha'
    rw [← period_rt_smul hP ha, hr', hr', map_smul, period_rt_smul hP' ha']
  have hPN : ∀ a, r (H.rt0 • P (N • a)) = H.rt0 • r (P (N • a)) := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hsp a)
    rw [← hxy]
    have k₁ := key _ x hx (h₁ x hx)
    have k₂ := key _ y hy (h₂ y hy)
    rw [neg_smul, neg_smul, map_neg, neg_inj] at k₂
    rw [map_add, smul_add, map_add, map_add, smul_add, k₁, k₂]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hP0 : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    have h := hPN a
    rw [map_nsmul, smul_comm H.rt0 N, map_nsmul, map_nsmul, smul_comm H.rt0 N,
      ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact smul_right_injective _ hNc h
  have h0 : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hP0 a
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, r.map_smul, r.map_smul, hx, smul_comm]
  have hI : ∀ v, r (Complex.I • v) = Complex.I • r v := by
    intro v
    have := h0 v
    rw [hρ, mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_smul] at this
    exact smul_right_injective _ hre.2 this
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← Complex.re_add_im c, add_smul, add_smul, mul_smul, mul_smul, Complex.coe_smul,
          Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul, hI] }
  have hsurj : Function.Surjective L := by
    show Function.Surjective r
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hP'.2.2.2.1, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨P (Φ.symm a), by rw [hr', Φ.apply_symm_apply]⟩
  exact ⟨LinearEquiv.ofBijective L ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun a => (hr' a).symm⟩

end GlobalTheory.CompRat
