import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma conj_real {K : Type} [Field K] [NumberField K] [IsTotallyReal K] (φ : K →+* ℂ) (x : K) :
    starRingEnd ℂ (φ x) = φ x := by
  have h : ComplexEmbedding.IsReal φ :=
    InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp h) x

private lemma exists_emb (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [Algebra.IsAlgebraic L Ω] : Nonempty (Ω →+* ℂ) := by
  let φ : L →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom
  letI : Algebra L ℂ := φ.toAlgebra
  exact ⟨(IsAlgClosed.lift (R := L) (S := Ω) (M := ℂ)).toRingHom⟩

theorem UpperTheory.V.Z.Sym.Ga.conjEx :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], ∃ c : G (maximalRealSubfield L) Ω, IsConjEl c := by
  intro L Ω _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ L Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨j⟩ := exists_emb L Ω
  let j' : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let τ' : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  let e : Ω ≃ₐ[ℚ] j'.fieldRange :=
    (AlgEquiv.ofInjectiveField j').trans (Subalgebra.equivOfEq _ _ (AlgHom.fieldRange_toSubalgebra j').symm)
  have hN : Normal ℚ j'.fieldRange := Normal.of_algEquiv e
  have hr := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ j'.fieldRange hN (τ'.comp e.symm.toAlgHom)
  have hex : ∀ x : Ω, ∃ y : Ω, j y = starRingEnd ℂ (j x) := by
    intro x
    have hmem : τ' x ∈ (τ'.comp e.symm.toAlgHom).fieldRange :=
      AlgHom.mem_fieldRange.mpr ⟨e x, by simp⟩
    have hmem' : τ' x ∈ j'.fieldRange := hr ▸ hmem
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hmem'
    exact ⟨y, hy⟩
  choose σ hσ using hex
  have inj := j.injective
  let c : Ω ≃ₐ[maximalRealSubfield L] Ω :=
    { toFun := σ
      invFun := σ
      left_inv := fun x => inj (by rw [hσ, hσ, Complex.conj_conj])
      right_inv := fun x => inj (by rw [hσ, hσ, Complex.conj_conj])
      map_mul' := fun x y => inj (by simp only [hσ, map_mul])
      map_add' := fun x y => inj (by simp only [hσ, map_add])
      commutes' := fun r => inj (by
        rw [hσ]
        exact conj_real (j.comp (algebraMap (maximalRealSubfield L) Ω)) r) }
  exact ⟨c, j, fun x => hσ x⟩
