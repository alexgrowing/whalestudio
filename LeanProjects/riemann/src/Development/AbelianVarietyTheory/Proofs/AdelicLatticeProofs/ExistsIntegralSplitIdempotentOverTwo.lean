import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalRingCardinality.ConjSqrtMinusD

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdem

theorem idem_alg {T : Type} [CommRing T] (p U R w m : T) (hU : p * U = U) (hR : R * R - R + m * p = 0)
    (hδ : U - 2 * (U * R) = p) (hw : w * w - w + m = 0) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * (1 - w) - U * R) = 0 ∧
      (U * w - U * R) + (U * (1 - w) - U * R) = p := by
  have h2 : (U * w - U * R) * (U * (1 - w) - U * R) = 0 := by
    linear_combination U * U * hR - U * U * hw - m * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] (φ : K →ₙ+* A) (c : A ⊗[F] E →+* A ⊗[F] E) (ω : E) (m : ℕ) (r u : K)
    (hc1 : ∀ a : A, c (a ⊗ₜ 1) = a ⊗ₜ 1) (hcω : ∀ a : A, c (a ⊗ₜ ω) = a ⊗ₜ (1 - ω))
    (hω : ω * ω - ω + m = 0) (hr : r * r - r + m = 0) (hu : u * (1 - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ ω + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have h1 : e = j (φ u) * k ω - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * (1 - k ω) - j (φ u) * j (φ r) := by
    rw [he, map_add, hc1, hcω, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one, map_sub, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ (m : A ⊗[F] E) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - φ r + m * φ 1 = 0 := by
      rw [← nsmul_eq_mul, ← map_nsmul, ← map_mul, ← map_sub, ← map_add, nsmul_eq_mul, mul_one, hr, map_zero]
    simpa using congrArg j this
  · have : φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← map_mul, ← map_add, ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_ofNat] at h
  · have h := congrArg k hω
    rwa [map_add, map_sub, map_mul, map_natCast, map_zero] at h

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem evalV_singleV_same (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

def placeHom : Fv F v →ₙ+* AF F where
  toFun y := pairA F 0 (singleV F v y)
  map_zero' := Prod.ext rfl (af_ext F fun w => by
    change evalV F w (singleV F v 0) = evalV F w 0
    by_cases hw : w = v
    · subst hw; rw [evalV_singleV_same, map_zero]
    · rw [evalV_singleV_ne F v _ hw, map_zero])
  map_add' x y := Prod.ext (add_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x + y)) = evalV F w (singleV F v x + singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_add, evalV_singleV_same]
    · simp only [map_add, evalV_singleV_ne F v _ hw, add_zero])
  map_mul' x y := Prod.ext (mul_zero _).symm (af_ext F fun w => by
    change evalV F w (singleV F v (x * y)) = evalV F w (singleV F v x * singleV F v y)
    by_cases hw : w = v
    · subst hw; simp only [map_mul, evalV_singleV_same]
    · simp only [map_mul, evalV_singleV_ne F v _ hw, mul_zero])

theorem singleV_mem_intAf (y : v.adicCompletionIntegers F) : singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne F v _ hw]; exact zero_mem _

theorem exists_root (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (k : ℕ) :
    ∃ r u : v.adicCompletionIntegers F, r * r - r + ((2 * k : ℕ) : v.adicCompletionIntegers F) = 0 ∧
      u * (1 - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (2 : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← map_ofNat (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) 2, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h h2
  obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k : ℕ) : v.adicCompletionIntegers F)) (by monicity!) 0
    (by simpa using Ideal.mul_mem_right _ _ hm) (by simp)
  have hunit : IsUnit (1 - 2 * r) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right r _ hm)
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

end Local

theorem exists_omega (D : D7) : ∃ (ω : 𝓞 D.host.E) (k : ℕ),
    (ω : D.host.E) * ω - ω + ((2 * k : ℕ) : D.host.E) = 0 ∧ D.host.conj ω = 1 - ω := by
  obtain ⟨k, hm⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * (2 * k) := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  generalize hmm : 2 * k = m at hm
  set c : D.host.E := (1 + D.host.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : D.host.E) = 0 := by
    have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
    have hs := D.host.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, k, ?_, ?_⟩
  · show c * c - c + _ = 0
    rw [hmm, ← pow_two, hc]
  · show D.host.conj c = 1 - c
    simp only [c, map_div₀, map_add, map_one, D.host.conj_sqrtMinusD, map_ofNat]
    ring

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := D.host.conjE_apply _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem exists_split_idempotent : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : Formalism.L2.Theta.AE D, e * e = e ∧ e * cA D e = 0 ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) ∧ ∃ α ∈ intAf D.host.F, ∃ β ∈ intAf D.host.F, ∃ ω : 𝓞 D.host.E, e = pairA D.host.F 0 α ⊗ₜ[D.host.F] (ω : D.host.E) + pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := by
  intro D v h2
  obtain ⟨ω, k, hω, hc⟩ := exists_omega D
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v h2 k
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  have key := idem_tensor (placeHom D.host.F v) (cA D) (ω : D.host.E) (2 * k) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun a => by rw [hcA, star_one]) (fun a => by rw [hcA, star_eq_conj, hc]) hω
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key.1, key.2.1, key.2.2, _, singleV_mem_intAf D.host.F v u, _,
    singleV_mem_intAf D.host.F v (-(u * r)), ω, rfl⟩

end GlobalTheory.SplitIdem

end
