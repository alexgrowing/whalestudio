import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.SignChar

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem range_res (K : IntermediateField F Ω) :
    (res F Ω ↥K).range = K.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩, by ext x; rfl⟩

theorem index_fix [IsAlgClosure F Ω] (Q : QCM F Ω) :
    Q.K.fixingSubgroup.index = 2 ∧ IsOpen (Q.K.fixingSubgroup : Set (G F Ω)) := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_eq_succ Q.two
  exact ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index, Q.two], Q.K.fixingSubgroup_isOpen⟩

open Classical in

noncomputable def sign [IsAlgClosure F Ω] (Q : QCM F Ω) : G F Ω →* ℤˣ where
  toFun σ := if σ ∈ Q.K.fixingSubgroup then 1 else -1
  map_one' := by simp [Subgroup.one_mem]
  map_mul' a b := by
    have h := Subgroup.mul_mem_iff_of_index_two (index_fix Q).1 (a := a) (b := b)
    by_cases ha : a ∈ Q.K.fixingSubgroup <;> by_cases hb : b ∈ Q.K.fixingSubgroup
    · rw [if_pos (h.2 (iff_of_true ha hb)), if_pos ha, if_pos hb, mul_one]
    · rw [if_neg (fun hab => hb ((h.1 hab).1 ha)), if_pos ha, if_neg hb, one_mul]
    · rw [if_neg (fun hab => ha ((h.1 hab).2 hb)), if_neg ha, if_pos hb, mul_one]
    · rw [if_pos (h.2 (iff_of_false ha hb)), if_neg ha, if_neg hb]; decide

theorem ker_sign [IsAlgClosure F Ω] (Q : QCM F Ω) : (sign Q).ker = Q.K.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker]
  simp only [sign, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

theorem QCM.ext' {Q Q' : QCM F Ω} (h : Q.K = Q'.K) : Q = Q' := by
  cases Q; cases Q'; cases h; rfl

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ η : QCM F Ω → (G F Ω →* ℤˣ), Function.Injective η ∧ ∀ Q, (η Q).ker = (res F Ω ↥Q.K).range ∧ IsOpen ((η Q).ker : Set (G F Ω)) := by
  intro F Ω _ _ _ _ _
  refine ⟨sign, ?_, fun Q => ⟨by rw [ker_sign, range_res], by rw [ker_sign]; exact (index_fix Q).2⟩⟩
  intro Q Q' h
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hk : Q.K.fixingSubgroup = Q'.K.fixingSubgroup := by rw [← ker_sign, ← ker_sign, h]
  apply QCM.ext'
  rw [← InfiniteGalois.fixedField_fixingSubgroup Q.K, ← InfiniteGalois.fixedField_fixingSubgroup Q'.K, hk]

end GlobalTheory.RealGal.SignChar
