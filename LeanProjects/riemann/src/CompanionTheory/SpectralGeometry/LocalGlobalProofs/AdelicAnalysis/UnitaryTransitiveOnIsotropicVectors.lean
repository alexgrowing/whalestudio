import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobalStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WittIso

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_sum (x y : Fin M → E) :
    hE σ J x y = ∑ i, ∑ j, σ (x i) * J i j * y j := rfl

theorem hE_add_right (x y z : Fin M → E) : hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp only [hE_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_right (c : E) (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hE_add_left (x y z : Fin M → E) : hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp only [hE_eq_sum, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hE_smul_left (c : E) (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) :
    σ (hE σ J x y) = hE σ J y x := by
  simp only [hE_eq_sum, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_hE_ne_zero (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0) :
    ∃ w, hE σ J x w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu : (fun i => σ (x i)) ᵥ* J = 0 := by
    funext j
    have h := hcon (Pi.single j 1)
    simp only [hE_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hu
  apply hx
  funext i
  have := congrFun h0 i
  simpa using this

theorem exists_hyperbolic_partner [CharZero E] (hσ : ∀ a, σ (σ a) = a)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0)
    (hxx : hE σ J x x = 0) :
    ∃ x', hE σ J x x' = 1 ∧ hE σ J x' x = 1 ∧ hE σ J x' x' = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_hE_ne_zero (σ := σ) hdet hx
  obtain ⟨w, hxw⟩ : ∃ w, hE σ J x w = 1 :=
    ⟨(hE σ J x w₀)⁻¹ • w₀, by rw [hE_smul_right, inv_mul_cancel₀ hw₀]⟩
  have hwx : hE σ J w x = 1 := by
    rw [← hE_conj hσ hJ x w, hxw, map_one]
  obtain ⟨t, ht⟩ : ∃ t, t = hE σ J w w := ⟨_, rfl⟩
  have hσt : σ t = t := by
    rw [ht]; exact hE_conj hσ hJ w w
  obtain ⟨c, hc⟩ : ∃ c : E, c = -t / 2 := ⟨_, rfl⟩
  have hσc : σ c = c := by
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [hc, map_div₀, map_neg, hσt, h2]
  have h1 : hE σ J x (w + c • x) = 1 := by
    rw [hE_add_right, hE_smul_right, hxx, hxw]; ring
  have h2 : hE σ J (w + c • x) x = 1 := by
    rw [hE_add_left, hE_smul_left, hxx, hwx]; ring
  refine ⟨w + c • x, h1, h2, ?_⟩
  rw [hE_add_left, hE_smul_left, h1, hE_add_right, hE_smul_right, hwx, ← ht, hσc, hc]
  ring

end Alg

theorem transitive_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 →
    ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x y hx hy hxx hyy
  have hσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  obtain ⟨x', h1, h2, h3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hx hxx
  obtain ⟨y', k1, k2, k3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hy hyy
  have hgram : gramE σ J ![x, x'] = gramE σ J ![y, y'] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramE, hxx, hyy, h1, h2, h3, k1, k2, k3]
  have hdet : (gramE σ J ![x, x']).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [gramE, hxx, h1, h2, h3]
  obtain ⟨g, hg, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM M J hJ 2 ![x, x'] ![y, y'] hgram hdet
  exact ⟨g, hg, by simpa using hgX 0⟩

end GlobalTheory.CompanionTheory.SW.WittIso
