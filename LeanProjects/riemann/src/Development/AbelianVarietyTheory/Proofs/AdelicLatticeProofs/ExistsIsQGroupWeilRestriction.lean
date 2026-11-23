import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHomStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReducedStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem ev_map_complexAut {ι : Type} (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) : ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  have h := MvPolynomial.comp_aeval (f := fun ij : ι × ι => g ij.1 ij.2) (σ.toRingHom.toRatAlgHom)
  have h2 := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, RingHom.toRatAlgHom_apply] at h2
  exact h2.symm

theorem exists_isQGroup_weilRestriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  intro F β _ _ _ _ ω n S hS
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_rational_equations_weil_restriction F β ω n S
  letI : Algebra F (ℂ ⊗[ℚ] F) := Algebra.TensorProduct.rightAlgebra
  have hb : ∀ i, Algebra.TensorProduct.basis ℂ ω i = algebraMap F (ℂ ⊗[ℚ] F) (ω i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hC := hS' ℂ (ℂ ⊗[ℚ] F) (Algebra.TensorProduct.basis ℂ ω) hb
  obtain ⟨h1, hm, hi⟩ := hS (ℂ ⊗[ℚ] F)
  obtain ⟨e1, em, ed, -⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom ℂ (ℂ ⊗[ℚ] F) β (Fin n) (Algebra.TensorProduct.basis ℂ ω)
  refine ⟨{g | ∀ f ∈ S', ev f g = 0}, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (hC 1).2 ⟨1, h1, e1.symm⟩
  · intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    obtain ⟨h', hh', rfl⟩ := (hC h).1 hh
    exact (hC _).2 ⟨g' * h', hm g' h' hg' hh', (em g' h').symm⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨g'⁻¹, hi g' hg', (ed g').2⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (ed g').1
  · intro σ g hg f hf
    rw [ev_map_complexAut, hg f hf, map_zero]
  · intro y hy
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' ℂ y).1 hy
  · intro R A _ _ _ _ _ b hbb
    refine ⟨fun y hy => (hS' R A b hbb y).1 ((GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R y).1 hy), fun hR g hg => ?_⟩
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R _).2 hR ((hS' R A b hbb _).2 ⟨g, hg, rfl⟩)

end GlobalTheory.ClassFin
