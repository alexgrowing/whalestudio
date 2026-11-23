import Formalism.LocalToGlobal.ProjectiveLattices.GenSectC

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem s1 [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    (IsField (RS K Ω D m ⧸ Is K x) ∧ FiniteDimensional (KTf K D m) (RS K Ω D m ⧸ Is K x)) ∧
      ∀ (K' : Type) [Field K'] [Algebra (KTf K D m) K'],
        FiniteDimensional K' (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K x)) ∧
          IsReduced (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K x)) := by
  obtain ⟨E, hE, hA, hfin, ⟨e⟩⟩ := quotient_generic_section_field hfg htr x j₀ hx₀ hbig
  have hKf : IsField (RS K Ω D m ⧸ Is K x) :=
    MulEquiv.isField (Field.toIsField E) e.toMulEquiv
  have hfd : FiniteDimensional (KTf K D m) (RS K Ω D m ⧸ Is K x) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  refine ⟨⟨hKf, hfd⟩, fun K' _ _ => ⟨inferInstance, ?_⟩⟩
  have e' : (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K x)) ≃ₐ[K'] (K' ⊗[KTf K D m] E) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  haveI : CharZero (KTf K D m) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K D m)).injective
  haveI : Algebra.IsSeparable (KTf K D m) E := inferInstance
  haveI : Algebra.FormallyUnramified (KTf K D m) E := by
    first
    | exact inferInstance
    | exact Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified K' (K' ⊗[KTf K D m] E) := inferInstance
  haveI : Algebra.EssFiniteType K' (K' ⊗[KTf K D m] E) := inferInstance
  haveI : IsReduced (K' ⊗[KTf K D m] E) := Algebra.FormallyUnramified.isReduced_of_field K' _
  exact isReduced_of_injective e'.toRingHom e'.injective

end Formalism.L2.Pj.GenSect
