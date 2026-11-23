import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
open NumberField IsDedekindDomain Formalism.L2.Ker

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.CocIntLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem embH_apply (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ) (hs : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x))
    (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hs, Complex.conj_conj]
  ring

theorem int_of_local (M : Submodule (𝓞 E) (HomE E a b)) (f : HomE E a b → HomE E a b → ℝ)
    (hadd : ∀ x x' y, f (x + x') y = f x y + f x' y) (hsm : ∀ (r : E) x y, f (r • x) y = f x (star r • y))
    (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, f x y = n) (x y : HomE E a b)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal M ∧
      star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal M) : ∃ n : ℤ, f x y = n := by
  have hzero : ∀ z, f 0 z = 0 := fun z => by
    have := hadd 0 0 z
    rw [add_zero] at this
    linarith
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, f ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [hzero]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, hadd, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        show ∃ n : ℤ, f ((s * (c * r)) • x) y = n
        rw [← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨v, hv, hy⟩ := hy
    have hmem : u * cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := hM _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO E v)) • x = (star (algebraMap (𝓞 E) E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, hsm, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hP.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv ((mem_conjP Q v).2 h')
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

theorem integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  intro E _ _ _ ι _ _ a b emb δ d sc M _ hs hsd hsc x y h
  have hmemL : ∀ {z : HomE E a b}, z ∈ M → embH emb δ z ∈ laV emb δ M := fun {z} hz => ⟨z, hz, rfl⟩
  have hsmA : ∀ (r : E) (x y : HomE E a b), altE (HV sc) (embH emb δ (r • x)) (embH emb δ y) =
      altE (HV sc) (embH emb δ x) (embH emb δ (star r • y)) := by
    intro r x y; simp only [altE, hv_smul emb δ sc hs]
  have hintA : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, altE (HV sc) (embH emb δ x) (embH emb δ y) = n := by
    intro x hx y hy
    have h1 := hmemL hx
    rw [← hsd] at h1
    exact h1 _ (hmemL hy)
  refine ⟨int_of_local M (fun x y => altE (HV sc) (embH emb δ x) (embH emb δ y)) ?_ hsmA hintA x y h,
    int_of_local M (fun x y => (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re +
      altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2) ?_ ?_ ?_ x y h⟩
  · intro x x' y
    simp only [altE, map_add, LinearMap.add_apply, Complex.add_im]
  · intro x x' y
    simp only [altE, map_add, LinearMap.add_apply, Complex.add_im, Complex.add_re]
    ring
  · intro r x y
    simp only [altE, hv_smul emb δ sc hs]
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hintA x hx y hy
    have h := hsc.2 _ (hmemL hx) _ (hmemL hy)
    simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n + m, ?_⟩
    have h2 := congrArg Complex.im hn
    have h3 : (HV sc (embH emb δ y) (embH emb δ x)).re = (HV sc (embH emb δ x) (embH emb δ y)).re := by
      rw [hv_swap]; simp
    simp only [altE] at hm
    simp only [map_add, LinearMap.add_apply, Complex.add_re, h3, altE, hm] at h2
    simp at h2
    simp only [altE, hm]
    push_cast
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith

end GlobalTheory.CocIntLoc
