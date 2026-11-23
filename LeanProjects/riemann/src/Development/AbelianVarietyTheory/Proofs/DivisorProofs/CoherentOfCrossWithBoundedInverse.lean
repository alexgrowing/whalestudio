import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusProductsStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain

section Alg

variable {K : Type} [Field K] {N : ℕ}

theorem mul_cancel_mid {C : Matrix (Fin N) (Fin N) K} (hC : IsUnit C.det) (A X Y B : Matrix (Fin N) (Fin N) K) :
    A * X * C * (C⁻¹ * Y * B) = A * (X * Y) * B := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C C⁻¹, Matrix.mul_nonsing_inv _ hC, Matrix.one_mul]

theorem triMod_of_cross (R : Subring K) (p : K) (k a : ℕ) (hs : Small R (p ^ (k + 1 + a))) (hp : p ∈ R)
    (P Q Mx Mx' Mz Mz' : Matrix (Fin N) (Fin N) K) (hPQ : P * Q = 1)
    (hP : p ^ a • P ∈ R.matrix) (hQ : p ^ a • Q ∈ R.matrix)
    (hMx : Fr R Mx) (hMx' : Fr R Mx') (hMz : Fr R Mz) (hMz' : Fr R Mz') (d₁ d₂ d₃ : Fin N → K)
    (H₁ : TriMod R (p ^ (k + 1 + 3 * a)) (Mz'⁻¹ * P * Mx) d₁)
    (H₂ : TriMod R (p ^ (k + 1 + 3 * a)) (Mz'⁻¹ * P * Mz) d₂)
    (H₃ : TriMod R (p ^ (k + 1 + 3 * a)) (Mx'⁻¹ * P * Mz) d₃) :
    TriMod R (p ^ (k + 1)) (Mx⁻¹ * Mz) (fun i => (d₁ i)⁻¹ * d₂ i) ∧
      TriMod R (p ^ (k + 1)) (Mx'⁻¹ * Mz') (fun i => d₃ i * (d₂ i)⁻¹) := by
  have hQP : Q * P = 1 := by
    rw [← Matrix.inv_eq_right_inv hPQ]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Matrix.det_ne_zero_of_right_inverse hPQ))
  have hpa : p ^ a ∈ R := pow_mem hp a
  have mem3 : ∀ A B C : Matrix (Fin N) (Fin N) K, A ∈ R.matrix → p ^ a • B ∈ R.matrix → C ∈ R.matrix →
      p ^ a • (A * B * C) ∈ R.matrix := by
    intro A B C hA hB hC
    rw [show p ^ a • (A * B * C) = A * (p ^ a • B) * C by simp [Matrix.mul_smul, Matrix.smul_mul]]
    exact mul_mem (mul_mem hA hB) hC
  have u : ∀ {A : Matrix (Fin N) (Fin N) K}, Fr R A → IsUnit A.det := fun h => isUnit_iff_ne_zero.2 h.1
  have inv3 : ∀ (A C : Matrix (Fin N) (Fin N) K), Fr R A → Fr R C → (A⁻¹ * P * C)⁻¹ = C⁻¹ * Q * A := by
    intro A C hA hC
    apply Matrix.inv_eq_left_inv
    rw [mul_cancel_mid (u hA), hQP, Matrix.mul_one, Matrix.nonsing_inv_mul _ (u hC)]
  have det3 : ∀ (A C : Matrix (Fin N) (Fin N) K), Fr R A → Fr R C → (A⁻¹ * P * C).det ≠ 0 := by
    intro A C hA hC
    refine Matrix.det_ne_zero_of_right_inverse (B := C⁻¹ * Q * A) ?_
    rw [mul_cancel_mid (u hC), hPQ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (u hA)]
  have e3 : p ^ (k + 1 + 3 * a) = p ^ (k + 1 + a) * p ^ a * p ^ a := by ring
  have e2 : p ^ (k + 1 + 3 * a) = p ^ (k + 1) * p ^ a * p ^ (2 * a) := by ring
  have e1 : p ^ (k + 1 + a) = p ^ (k + 1) * p ^ a := by ring
  have hh : p ^ (k + 1) ∈ R := pow_mem hp _
  have h2a : p ^ (2 * a) ∈ R := pow_mem hp _
  have iA := inv3 Mz' Mx hMz' hMx
  have iA' := inv3 Mz' Mz hMz' hMz
  have mA : p ^ a • (Mx⁻¹ * Q * Mz') ∈ R.matrix := mem3 _ _ _ hMx.2.2 hQ hMz'.2.1
  have mA' : p ^ a • (Mz⁻¹ * Q * Mz') ∈ R.matrix := mem3 _ _ _ hMz.2.2 hQ hMz'.2.1
  obtain ⟨-, T₁⟩ := GlobalTheory.T.triangular_modulus_inverse K N R (p ^ (k + 1 + a)) (p ^ a) _ d₁ hs hpa (det3 Mz' Mx hMz' hMx)
    (by rw [iA]; exact mA) (by rwa [← e3])
  obtain ⟨-, T₂⟩ := GlobalTheory.T.triangular_modulus_inverse K N R (p ^ (k + 1 + a)) (p ^ a) _ d₂ hs hpa (det3 Mz' Mz hMz' hMz)
    (by rw [iA']; exact mA') (by rwa [← e3])
  rw [e1, iA] at T₁
  rw [e1, iA'] at T₂
  have U₂ : TriMod R (p ^ (k + 1) * p ^ a) (Mz'⁻¹ * P * Mz) d₂ := by rw [e2] at H₂; exact H₂.of_mul h2a
  have U₃ : TriMod R (p ^ (k + 1) * p ^ a) (Mx'⁻¹ * P * Mz) d₃ := by rw [e2] at H₃; exact H₃.of_mul h2a
  have m1 := (GlobalTheory.T.triangular_modulus_products K N R (p ^ (k + 1)) (p ^ a) _ _ _ _ hh hpa).1 mA (mem3 _ _ _ hMz'.2.2 hP hMz.2.1) T₁ U₂
  have m2 := (GlobalTheory.T.triangular_modulus_products K N R (p ^ (k + 1)) (p ^ a) _ _ _ _ hh hpa).1 (mem3 _ _ _ hMx'.2.2 hP hMz.2.1) mA' U₃ T₂
  rw [mul_cancel_mid (u hMz'), hQP, Matrix.mul_one] at m1
  rw [mul_cancel_mid (u hMz), hPQ, Matrix.mul_one] at m2
  exact ⟨m1, m2⟩

end Alg

theorem coh_of_cross : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M M' : X → Matrix (Fin N) (Fin N) X.functionField) (c c' : X → Fin N → X.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) X.functionField), P * Q = 1 → (∀ x, Ov p x → ((p : X.functionField) ^ a) • P ∈ (loc x).matrix ∧ ((p : X.functionField) ^ a) • Q ∈ (loc x).matrix) → Cross p (k + 1 + 3 * a) M M' c c' P → Coh p (k + 1) M c ∧ Coh p (k + 1) M' c' := by
  intro X _ p k a N M M' c c' P Q hPQ hPQa H
  have key : ∀ x, Ov p x → ∀ᶠ z in 𝓝 x, Ov p z →
      TriMod (loc z) ((p : X.functionField) ^ (k + 1)) ((M x)⁻¹ * M z) (fun i => (c x i : X.functionField) / c z i) ∧
      TriMod (loc z) ((p : X.functionField) ^ (k + 1)) ((M' x)⁻¹ * M' z) (fun i => (c' x i : X.functionField) / c' z i) := by
    intro x hx
    obtain ⟨hMx, hMx', hev⟩ := H x hx
    filter_upwards [hev, hMx.eventually, hMx'.eventually] with z hz hzx hzx' hOz
    obtain ⟨hMz, hMz', hevz⟩ := H z hOz
    obtain ⟨hself, -⟩ := hevz.self_of_nhds hOz
    obtain ⟨h₃, h₁⟩ := hz hOz
    obtain ⟨hPz, hQz⟩ := hPQa z hOz
    have hs : Small (loc z) ((p : X.functionField) ^ (k + 1 + a)) := by
      have := small_pow hOz (k + a); rwa [show k + a + 1 = k + 1 + a by omega] at this
    obtain ⟨r₁, r₂⟩ := triMod_of_cross (loc z) (p : X.functionField) k a hs (natCast_mem _ p) P Q (M x) (M' x) (M z) (M' z)
      hPQ hPz hQz hzx hzx' hMz hMz' _ _ _ h₁ hself h₃
    refine ⟨?_, ?_⟩
    · convert r₁ using 2
      field_simp
    · convert r₂ using 2
      field_simp
  exact ⟨fun x hx => ⟨(H x hx).1, (key x hx).mono fun z hz hOz => (hz hOz).1⟩,
    fun x hx => ⟨(H x hx).2.1, (key x hx).mono fun z hz hOz => (hz hOz).2⟩⟩

end GlobalTheory.LatChain

end
