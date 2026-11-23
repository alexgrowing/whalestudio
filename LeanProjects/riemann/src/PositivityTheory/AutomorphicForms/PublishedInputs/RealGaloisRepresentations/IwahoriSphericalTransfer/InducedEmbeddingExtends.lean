import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem induced_embedding_extends : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ (τK : K →+* Qbar l) (τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), τK.comp (algebraMap F K) = τ ∧ IsInduced Bw' τK τ'' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj τ LL' τ' hτ
  obtain ⟨Kw', j', j_E', _, _, _, _, _, _, _, _, _, _, _⟩ := Bw'
  dsimp only at hK hj ⊢
  subst hK
  subst hj
  let ι : K →+* ↥Bw.Kw.1 :=
    { toFun := fun x => ⟨Bw.j (algebraMap K Ω x), j_E' x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨(LL'.1.val.toRingHom.comp (τ'.toRingHom.comp ι)), τ', ?_, ?_⟩
  · ext x
    have := hτ x
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [this]
    have e : (ι (algebraMap F K x)) = ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩ := by
      apply Subtype.ext
      simp [ι, ← IsScalarTower.algebraMap_apply]
    simp [e]
  · intro x
    rfl

end GlobalTheory
