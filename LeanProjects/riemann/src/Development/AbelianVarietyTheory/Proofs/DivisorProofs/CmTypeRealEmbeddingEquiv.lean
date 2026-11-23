import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

noncomputable section

namespace GlobalTheory.CMEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isReal_res (σ : E →+* ℂ) : ComplexEmbedding.IsReal (σ.comp (maximalRealSubfield E).subtype) := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, Subfield.subtype_apply]
  rw [← IsCMField.complexEmbedding_complexConj, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def res (σ : E →+* ℂ) : FR E →+* ℝ := (isReal_res σ).embedding

theorem res_apply (σ : E →+* ℂ) (x : FR E) : ((res σ x : ℝ) : ℂ) = σ (x : E) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

theorem exists_ext (ψ : FR E →+* ℂ) : ∃ σ : E →+* ℂ, ∀ x : FR E, σ (x : E) = ψ x := by
  letI : Algebra (FR E) ℂ := ψ.toAlgebra
  let f : E →ₐ[FR E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem eq_or_eq_conj (σ σ' : E →+* ℂ) (h : ∀ x : FR E, σ' (x : E) = σ (x : E)) :
    σ' = σ ∨ σ' = ComplexEmbedding.conjugate σ := by
  set c := IsCMField.complexConj E with hc
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra! H
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)
  have cc : ∀ z, c (c z) = z := IsCMField.complexConj_apply_apply E
  set α := y - c y with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcα : c α = -α := by rw [hα, map_sub, cc]; ring
  have mem : ∀ z, c z = z → σ' z = σ z := fun z hz =>
    h ⟨z, (IsCMField.complexConj_eq_self_iff E z).1 hz⟩
  have hsq : σ' α ^ 2 = σ α ^ 2 := by
    rw [← map_pow, ← map_pow]; exact mem _ (by rw [map_pow, hcα]; ring)
  have dec : ∀ z, ∃ a b, c a = a ∧ c b = b ∧ z = a + b * α ∧ c z = a - b * α := by
    intro z
    refine ⟨(z + c z) / 2, (z - c z) / (2 * α), ?_, ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, cc, map_ofNat]; ring
    · rw [map_div₀, map_sub, cc, map_mul, map_ofNat, hcα]
      field_simp
      ring
    · field_simp; ring
    · field_simp; ring
  have hsq' : (σ' α - σ α) * (σ' α + σ α) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hsq' with h1 | h1
  · left
    ext z
    obtain ⟨a, b, ha, hb, hz, -⟩ := dec z
    rw [hz, map_add, map_add, map_mul, map_mul, mem a ha, mem b hb, sub_eq_zero.1 h1]
  · right
    ext z
    obtain ⟨a, b, ha, hb, hz, hcz⟩ := dec z
    rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, ← hc, hcz, hz,
      map_add, map_sub, map_mul, map_mul, mem a ha, mem b hb, eq_neg_of_add_eq_zero_left h1]
    ring

theorem cmType_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) :
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  have hRC : Function.Bijective (fun τ : FR E →+* ℝ => Complex.ofRealHom.comp τ) := by
    constructor
    · intro τ τ' hτ
      ext x
      exact Complex.ofReal_injective (RingHom.congr_fun hτ x)
    · intro ψ
      obtain ⟨σ, hσ⟩ := exists_ext ψ
      refine ⟨res σ, RingHom.ext fun x => ?_⟩
      simp only [RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe]
      rw [res_apply, hσ]
  let eRC := Equiv.ofBijective _ hRC
  let e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) :=
    (Fintype.equivFinOfCardEq (Embeddings.card (FR E) ℂ)).symm.trans eRC.symm
  have hb : Function.Bijective (fun i => res (φ i)) := by
    constructor
    · intro i j hij
      have hx : ∀ x : FR E, φ j (x : E) = φ i (x : E) := fun x => by
        rw [← res_apply, ← res_apply]
        exact congrArg (fun τ : FR E →+* ℝ => ((τ x : ℝ) : ℂ)) hij.symm
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      exact (hk i (eq_or_eq_conj (φ i) (φ j) hx)).trans (hk j (Or.inl rfl)).symm
    · intro τ
      obtain ⟨σ, hσ⟩ := exists_ext (Complex.ofRealHom.comp τ)
      obtain ⟨i, hi, -⟩ := hφ σ
      refine ⟨i, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
      rw [res_apply]
      rcases hi with h | h
      · rw [← h, hσ]; rfl
      · have h' : φ i = ComplexEmbedding.conjugate σ := by
          ext z
          rw [ComplexEmbedding.conjugate_coe_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
        rw [h', ComplexEmbedding.conjugate_coe_eq, hσ]
        simp
  let b := Equiv.ofBijective _ hb
  refine ⟨e'.trans b.symm, e', fun j x => ?_⟩
  have hj : res (φ ((e'.trans b.symm) j)) = e' j := b.apply_symm_apply (e' j)
  rw [← hj, res_apply]

end GlobalTheory.CMEquiv
