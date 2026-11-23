import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevel
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPartsF

theorem exists_real_finite_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J) :
    ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y : AEF F E, infPartF F E x = infPartF F E y → finPartF F E x = finPartF F E y → x = y :=
    fun x y h1 h2 => GlobalTheory.AdelicOrbit.parts_inj x y h1 h2
  have hs : ∀ a b, ∃ x : AEF F E, infPartF F E x = a ∧ finPartF F E x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  set g : GL (Fin n) (AEF F E) := matHomF σ J p with hg
  have hgm : g ∈ HR (AF F) σ J := p.2
  have hparts := (GlobalTheory.AdelicOrbit.mem_parts σ J g).1 hgm
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs (Formalism.UG.bc (infPartF F E) g) 1
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.gl_glue (infPartF F E) (finPartF F E) hi hs 1 (Formalism.UG.bc (finPartF F E) g)
  have ha : a ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J a).2 ⟨a1 ▸ hparts.1, a2 ▸ one_mem _⟩
  have hk : k ∈ HR (AF F) σ J := (GlobalTheory.AdelicOrbit.mem_parts σ J k).2 ⟨k1 ▸ one_mem _, k2 ▸ hparts.2⟩
  refine ⟨⟨a, ha⟩, ?_, ⟨k, hk⟩, ?_, ?_, ?_⟩
  · exact MonoidHom.mem_ker.2 a2
  · exact MonoidHom.mem_ker.2 k1
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (a * k)
      rw [map_mul, a1, k1, mul_one]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (a * k)
      rw [map_mul, a2, k2, one_mul]
  · refine Subtype.ext (GlobalTheory.UnitarySplit.gl_ext (infPartF F E) (finPartF F E) hi ?_ ?_)
    · show Formalism.UG.bc (infPartF F E) g = Formalism.UG.bc (infPartF F E) (k * a)
      rw [map_mul, a1, k1, one_mul]
    · show Formalism.UG.bc (finPartF F E) g = Formalism.UG.bc (finPartF F E) (k * a)
      rw [map_mul, a2, k2, mul_one]

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J), ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := exists_real_finite_mul

end GlobalTheory.WeilPartsF
