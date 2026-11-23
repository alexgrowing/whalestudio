import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory

namespace ThetaCosetSum

open Formalism.L2.Th1.H

theorem xiL_eq_kernel {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) *
      ∑ x ∈ SX, ∑ y ∈ SB, ∑ t ∈ SA, Φ (t - x) *
        (α x * ((SA.card : ℂ)⁻¹ * (brk H y t)⁻¹ * α y * opU H y e (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) := by
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [opU]
  simp only [xiS, sumU, hatS, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem sum_xiL {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (hv : 0 < vol)
    (SX SA SB : Finset V) (c : ι → ℂ) (Φ : ι → V → ℂ) (Ψ e : V → ℂ) (hΨ : ∀ t, Ψ t = ∑ i, c i * Φ i t) (z : V) :
    ∑ i, c i * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiL H α vol SX SA SB (Φ i) e z) = xiL H α 1 SX SA SB Ψ e z := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have h2 : ((vol : ℝ) : ℂ) = ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hv.le).symm
  have h3 : ∀ w : ℂ, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) * w) = w := by
    intro w
    generalize ((Real.sqrt vol : ℝ) : ℂ) = s at hs h2
    rw [h2]; field_simp
  simp only [xiL_eq_kernel, h3, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, hΨ, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

open Classical in

theorem eq_sum_coset {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A B : Submodule R M) (hBA : B ≤ A)
    [Fintype (↥A ⧸ B.comap A.subtype)] (Ξ : M → ℂ) (h1 : ∀ x, Ξ x ≠ 0 → x ∈ A) (h2 : ∀ x, ∀ y ∈ B, Ξ (x + y) = Ξ x)
    (r : (↥A ⧸ B.comap A.subtype) → ↥A) (hr : ∀ q, Submodule.Quotient.mk (r q) = q) (t : M) :
    Ξ t = ∑ q, Ξ (r q) * (if t - (r q : M) ∈ B then 1 else 0) := by
  by_cases ht : t ∈ A
  · have key : ∀ q, t - (r q : M) ∈ B ↔ q = Submodule.Quotient.mk (⟨t, ht⟩ : ↥A) := by
      intro q
      rw [eq_comm]
      conv_rhs => rw [← hr q]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_eq_single (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A))]
    · have hm := (key _).mpr rfl
      rw [if_pos hm, mul_one, ← h2 (r (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A)) : M) _ hm, add_sub_cancel]
    · intro q _ hq
      rw [if_neg (fun h => hq ((key q).mp h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : Ξ t = 0 := by
      by_contra h
      exact ht (h1 t h)
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply ht
    have := A.add_mem (hBA h) (r q).2
    simpa using this

end ThetaCosetSum

open ThetaCosetSum in

theorem latSum_thInd_eq_thC : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndTieD a b S (cA * cB) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → 0 < volC A.AA S N N' → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → ∀ z, latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) (fun x => Ξ x * A.thInd S N N' cB x z) = thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) Ξ (A.e a b N N') z := by
  intro X A a b S N N' cA cB Ξ hT hN hN' hA hB hv hfin h1 h2 z
  classical
  let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  have hle : mulLat cB (homAt S N N') ≤ divLat cA (homAt S N N') := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy)
  have hdiv : ∀ x ∈ divLat cA (homAt S N N'), x ∈ divLat (cA * cB) (homAt S N N') := by
    intro x hx
    have h : (cB : 𝓞 X.E) • (cA : 𝓞 X.E) • x ∈ homAt S N N' := Submodule.smul_mem _ _ hx
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at h
    exact h
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)) with hr
  have hrq : ∀ q, Submodule.Quotient.mk (r q) = q := fun q => Function.surjInv_eq _ q
  have hx : ∀ q, A.thInd S N N' cB (r q : HomE X.E a b) z = _ := fun q =>
    hT N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, hdiv _ (r q).2⟩ (Nat.mul_pos hA hB) z
  simp only [hx]
  unfold xiC thC xiV
  refine sum_xiL _ _ _ hv _ _ _ (fun q => Ξ (r q)) (fun q => onV (X.embC A.σ₀) A.δ (cosInd S N N' cB (r q))) _ _ ?_ z
  intro v
  unfold onV
  split_ifs with h
  · have := eq_sum_coset _ _ hle Ξ h1 h2 r hrq h.choose
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cosInd
    congr
  · simp

end GlobalTheory
