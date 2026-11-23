import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteRepresentatives

namespace GlobalTheory

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors

namespace Published

def FinitenessOfHermitianClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∀ (c : FractionalIdeal (𝓞 E)⁰ E), c ≠ 0 → ∀ (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ →
    ∀ (ι : Type) [Finite ι] (𝓛 : Set (Submodule (𝓞 E) (Fin r → E) × (ι → Fin r → E))),
    (∀ p ∈ 𝓛, IsLattice p.1 ∧
      (∀ x, (∀ y ∈ p.1, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • p.1) ∧
      ∀ i, p.2 i ∈ p.1) →
    ∃ S ⊆ 𝓛, S.Finite ∧ ∀ p ∈ 𝓛, ∃ q ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ p.1 ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ q.1) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ p.2 i - q.2 i ∈ 𝔪 • q.1

end Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_sesquilinear_eq_herm (G : Matrix (Fin r) (Fin r) E) :
    ∃ h : (Fin r → E) →ₗ[E] (Fin r → E) →ₗ⋆[E] E, ∀ x y, h x y = herm G x y := by
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ _ _ (herm G) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro x x' y; simp [herm, add_mul, Finset.sum_add_distrib]
  · intro c x y; simp [herm, Finset.mul_sum, mul_assoc]
  · intro x y y'; simp [herm, hc, mul_add, Finset.sum_add_distrib]
  · intro c x y
    simp only [herm, hc, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_finite_unitary_classes (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) {N : ℤ} (hN : N ≠ 0)
    {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) {α : Type*} {ι : Type*} [Finite ι]
    (Λ : α → Submodule (𝓞 E) (Fin r → E)) (t : α → ι → Fin r → E)
    (hΛ : ∀ a, IsLattice (Λ a))
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ ((N : E) * herm G x y))
    (hdual : ∀ a x, (∀ y ∈ Λ a, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ Λ a ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ s) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t a i - t s i ∈ 𝔪 • Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  have hs : ∀ x y, h y x = star (h x y) := fun x y => by
    simp only [hh, herm, star_sum, star_mul', ← hc (G _ _), hG, hc, star_star]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnd : ∀ y, (∀ x, h y x = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_vecMul_eq_zero hdet (funext fun b => ?_)
    have := hy (Pi.single b 1)
    rw [hh, herm, Finset.sum_comm, Finset.sum_eq_single b] at this
    · simpa [hc, Matrix.vecMul, dotProduct] using this
    · intro b' _ hb; simp [hc, hb]
    · simp
  have hm : (Ideal.absNorm 𝔪 : ℤ) ≠ 0 := by
    exact_mod_cast fun h0 => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨S, hS, H⟩ := HermClass.exists_finite_classes ((N : E) • h)
    (fun x y => by simp [hs x y]) (fun y hy => hnd y fun x => by simpa [hN'] using hy x)
    (mul_ne_zero hN hN) hm (fun a => (Λ a).restrictScalars ℤ) t
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by simpa [hh] using hint a x hx y hy)
    (fun a x hx => by
      rw [Int.cast_mul, mul_smul]
      exact hdual a _ fun y hy => by simpa [← hh] using hx y hy) ht
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2, h3⟩ := H a
  let g : GL (Fin r) E := ⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ x, (g : Matrix (Fin r) (Fin r) E) *ᵥ x = γ x := fun x =>
    LinearMap.toMatrix'_mulVec γ.toLinearMap x
  refine ⟨s, hsS, g, fun x y => ?_, fun x => ?_, fun i => ?_⟩
  · simpa [hg, hh, hN'] using h1 x y
  · rw [hg]; exact h2 x
  · obtain ⟨y, hy, he⟩ := h3 i
    rw [hg, he, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hy

theorem exists_int_bound_of_dual_eq_smul (G : Matrix (Fin r) (Fin r) E)
    {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ Λ : Submodule (𝓞 E) (Fin r → E),
      (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((N : E) * herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ := by
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  obtain ⟨e, he0, he⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hc
  obtain ⟨d, hd0, hd⟩ := c.isFractional
  have he0' : algebraMap (𝓞 E) E e ≠ 0 := fun h0 => he0 (RingOfIntegers.ext h0)
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero hd0 (RingOfIntegers.ext h0)
  obtain ⟨N, hN, hNi⟩ := HermClass.exists_int_mul_isIntegral E
    (Set.toFinite {(algebraMap (𝓞 E) E e)⁻¹, (algebraMap (𝓞 E) E d)⁻¹})
  refine ⟨N, hN, fun Λ hΛ => ⟨fun x hx y hy => ?_, fun x hx => ?_⟩⟩
  · have h1 := (hNi _ (Or.inl rfl)).mul ((hΛ _).2 (Submodule.smul_mem_smul he hx) y hy)
    rwa [← hh, map_smul, LinearMap.smul_apply, smul_eq_mul, hh, mul_assoc,
      inv_mul_cancel_left₀ he0'] at h1
  · refine Submodule.smul_induction_on (p := fun x => (N : E) • x ∈ Λ) ((hΛ x).1 hx)
      (fun a ha z hz => ?_) (fun x y hx hy => by rw [smul_add]; exact add_mem hx hy)
    obtain ⟨b, hb⟩ := hd a ha
    have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E b) := b.isIntegral_coe
    have h1 := (hNi _ (Or.inr rfl)).mul h0
    rw [hb, Algebra.smul_def, mul_assoc, inv_mul_cancel_left₀ hd0'] at h1
    rw [smul_smul]
    exact Λ.smul_mem (⟨_, h1⟩ : 𝓞 E) hz

theorem Published.finitenessOfHermitianClasses_holds : Published.FinitenessOfHermitianClasses := by
  intro E _ _ _ r G hG hdet c hc 𝔪 h𝔪 ι _ 𝓛 h𝓛
  obtain ⟨N, hN, H⟩ := exists_int_bound_of_dual_eq_smul G hc
  obtain ⟨S, hS, HS⟩ := exists_finite_unitary_classes G hG hdet hN h𝔪 (fun p : 𝓛 => p.1.1)
    (fun p => p.1.2) (fun p => (h𝓛 p p.2).1) (fun p => (H _ (h𝓛 p p.2).2.1).1)
    (fun p => (H _ (h𝓛 p p.2).2.1).2) (fun p => (h𝓛 p p.2).2.2)
  refine ⟨Subtype.val '' S, by rintro _ ⟨p, -, rfl⟩; exact p.2, hS.image _, fun p hp => ?_⟩
  obtain ⟨s, hs, h⟩ := HS ⟨p, hp⟩
  exact ⟨s, ⟨s, hs, rfl⟩, h⟩

end GlobalTheory
