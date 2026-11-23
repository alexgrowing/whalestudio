import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombinationStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.StrongApproximationSL2

section General

variable {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) (ε : R)

def prodMonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {x | ∃ γ : Matrix (Fin 2) (Fin 2) K, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) R,
    h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map φ * h}
  one_mem' := ⟨1, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, hε, rfl⟩ ⟨γ', hγ', h', hh', hε', rfl⟩
    set G := γ'.map φ with hG
    have hGd : G.det = 1 := by
      rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ', map_one]
    have h1 : G * G.adjugate = 1 := by rw [Matrix.mul_adjugate, hGd, one_smul]
    have h2 : G.adjugate * G = 1 := by rw [Matrix.adjugate_mul, hGd, one_smul]
    have h3 : G.adjugate.det = 1 := by
      have := congrArg Matrix.det h1
      rwa [det_mul, hGd, one_mul, det_one] at this
    refine ⟨γ * γ', by rw [det_mul, hγ, hγ', one_mul], G.adjugate * h * G * h', ?_, ?_, ?_⟩
    · rw [det_mul, det_mul, det_mul, h3, hh, hGd, hh']; simp
    · have e : G.adjugate * h * G * h' - 1 = G.adjugate * (h - 1) * G * h' + (h' - 1) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, Matrix.sub_mul, Matrix.one_mul]
        abel
      rw [e, smul_add, hε', ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, hε]
    · rw [Matrix.map_mul, ← hG]
      calc γ.map φ * h * (G * h') = γ.map φ * (G * G.adjugate) * h * (G * h') := by rw [h1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]

theorem upper_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, φ t + ε * s; 0, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, t; 0, 1], by simp [det_fin_two], !![1, ε * s; 0, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, 0; φ t + ε * s, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, 0; t, 1], by simp [det_fin_two], !![1, 0; ε * s, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mem_of_elementary (M : Submonoid (Matrix (Fin 2) (Fin 2) R)) (hU : ∀ x : R, !![1, x; 0, 1] ∈ M)
    (hL : ∀ x : R, !![1, 0; x, 1] ∈ M) (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R)
    (hu : (g 1 0 + g 1 1 * s) * u = 1) : g ∈ M := by
  rw [det_fin_two] at hg
  have e : g = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
      !![1, (g 1 1 - 1) * u; 0, 1] * !![1, 0; -s, 1] := by
    have e1 : g * !![1, 0; s, 1] = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
        !![1, (g 1 1 - 1) * u; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (-(g 0 0 + g 0 1 * s - 1)) * hu
      · linear_combination (-(g 0 1) - (g 0 0 + g 0 1 * s - 1) * (g 1 1 - 1) * u) * hu - u * hg
      · linear_combination (-(g 1 1 - 1)) * hu
    have e2 : (!![1, 0; s, 1] * !![1, 0; -s, 1] : Matrix (Fin 2) (Fin 2) R) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← e1, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hU _) (hL _)) (hU _)) (hL _)

theorem exists_unit_of_idem {c d a b : R} (haa : a * a = a) (hbb : b * b = b) (hab : a * b = 0) (hs : a + b = 1)
    (hw : IsUnit (a * c + b * d)) : ∃ s u : R, (c + d * s) * u = 1 := by
  obtain ⟨w, hw⟩ := hw.exists_right_inv
  have h1 : a * c * w = a := by linear_combination a * hw - c * w * haa - d * w * hab
  have h2 : b * d * w = b := by linear_combination b * hw - d * w * hbb - c * w * hab
  refine ⟨b * (1 - c) * w, a * w + b, ?_⟩
  have h3 : c + d * (b * (1 - c) * w) = a * c + b := by linear_combination (1 - c) * h2 - c * hs
  rw [h3]
  linear_combination hs + h1 + hbb + (c + w) * hab + c * w * haa

theorem mem_closure_of_dense [TopologicalSpace R] [IsTopologicalRing R] (hε : ε * ε = ε)
    (hd : ∀ (x : R) (U : Set R), U ∈ 𝓝 x → ∃ t : K, ∃ s : R, φ t + ε * s ∈ U)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R) (hu : (g 1 0 + g 1 1 * s) * u = 1) :
    g ∈ closure (prodMonoid φ ε : Set (Matrix (Fin 2) (Fin 2) R)) := by
  have key : ∀ f : R → Matrix (Fin 2) (Fin 2) R, Continuous f → (∀ t s, f (φ t + ε * s) ∈ prodMonoid φ ε) →
      ∀ x, f x ∈ (prodMonoid φ ε).topologicalClosure := by
    intro f hf h x
    change f x ∈ closure _
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨t, s, hts⟩ := hd x _ (hf.continuousAt.preimage_mem_nhds hV)
    exact ⟨_, hts, h t s⟩
  refine mem_of_elementary (prodMonoid φ ε).topologicalClosure ?_ ?_ g hg s u hu
  · refine key (fun x => !![1, x; 0, 1]) ?_ (upper_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine key (fun x => !![1, 0; x, 1]) ?_ (lower_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end General

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

theorem strongApprox_SL2 : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  intro F _ _ S₁ S₂ ε hε hS g hg
  have hdet : ∑ i : Fin 2, ![-g 0 1, g 0 0] i * g 1 i = 1 := by
    rw [det_fin_two] at hg
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hg
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 2) (g 1) ![-g 0 1, g 0 0] (hdet ▸ isUnit_one)
  rw [Fin.sum_univ_two] at h3 h4
  obtain ⟨s, u, hu⟩ := exists_unit_of_idem (h1 0) (h1 1) (h2 0 1 (by decide)) h3 h4
  refine mem_closure_of_dense (algebraMap F (AF F)) ε (idem_of_isPlacesIdem hε) (fun x U hU => ?_) g hg s u hu
  obtain ⟨t, -, s, h⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x U hU ∅
  exact ⟨t, s, h⟩

end GlobalTheory.StrongApproximationSL2
