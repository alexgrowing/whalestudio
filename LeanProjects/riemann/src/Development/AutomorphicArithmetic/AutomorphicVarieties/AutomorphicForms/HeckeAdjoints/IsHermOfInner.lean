import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral

noncomputable section

open NumberField MeasureTheory UpperTheory.V.TR GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.Gk

def ToFound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : Sm F a), TR.IsCuspForm φ → φ.1 ∈ cuspForms F a

def LieMatch : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ),
    ∃ e : TR.Lie F a →ₗ[ℝ] (isExpLieAlgebra F a).lieSubalgebra, centralZ F a = centralExp F a • e (oneL F a) ∧
      ∀ X (φ : Sm F a) (h : φ.1 ∈ cuspForms F a), (lieActionCusp F a (e X) ⟨φ.1, h⟩).1 = (TR.lie F a X φ).1

private theorem isHerm_of_inner {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π : CuspSub F a} {L : Type}
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] (p : π.V →ₗ[ℂ] L) (h1 : ∀ φ, inner ℂ (p φ) (p φ) = 0 → φ = 0)
    (h2 : ∀ k φ ψ, inner ℂ (p (π.op (.fin k) φ)) (p (π.op (.fin k) ψ)) = inner ℂ (p φ) (p ψ))
    (h3 : ∀ k φ ψ, inner ℂ (p (π.op (.cpt k) φ)) (p (π.op (.cpt k) ψ)) = inner ℂ (p φ) (p ψ))
    (h4 : ∀ X φ ψ, inner ℂ (p (π.op (.lie X) φ)) (p ψ) + inner ℂ (p φ) (p (π.op (.lie X) ψ)) = 0) : ∃ H, IsHerm π H :=
  ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => inner ℂ (p φ) (p ψ))
    (fun _ _ _ => by rw [map_add, inner_add_left]) (fun _ _ _ => by rw [map_smul, inner_smul_left]; rfl)
    (fun _ _ _ => by rw [map_add, inner_add_right]) (fun _ _ _ => by rw [map_smul, inner_smul_right]; rfl), h1, h2, h3, h4⟩

theorem hermEx_of (h1 : ToFound) (h2 : LieMatch) : HermEx := by
  intro F _ _ _ a _ π h0
  obtain ⟨e, hz, he⟩ := h2 F a
  let μ : Measure (Reduction.normOneGL F a) := Measure.haar
  let j : π.V →ₗ[ℂ] cuspForms F a :=
    ((Sm F a).subtype ∘ₗ π.V.subtype).codRestrict _ fun φ => h1 F a φ.1 (π.cusp _ φ.2)
  have hl : ∀ X φ, (gkModuleCusp F a).ρ (e X) (j φ) = j (π.op (.lie X) φ) := fun X φ => Subtype.ext (he X φ.1 _)
  have hc : ∀ φ, j φ ∈ centralCuspForms F a := fun φ s x => by
    have h3 : lieActionCusp F a (e (oneL F a)) (j φ) = 0 :=
      Subtype.ext ((he _ φ.1 _).trans (congrArg Subtype.val (h0 _ φ.2)))
    have h4 : lieActionCusp F a (centralZ F a) (j φ) = (0 : ℂ) • j φ := by
      rw [hz, map_smul, LinearMap.smul_apply, h3, smul_zero, zero_smul]
    rw [Reduction.centralSection_mul_comm, apply_mul_centralSection h4]
    simp
  let p := CuspidalSpectrum.cuspToL2 μ ∘ₗ j
  have hr : ∀ (g : GlobalTheory.CuspRep.GA F a) (φ φ' ψ ψ' : π.V), φ'.1 = rt F a g φ.1 → ψ'.1 = rt F a g ψ.1 →
      inner ℂ (p φ') (p ψ') = inner ℂ (p φ) (p ψ) := fun g φ φ' ψ ψ' e1 e2 =>
    (congrArg₂ (inner ℂ) (cuspFormLp_rightTranslate_eq_rep μ (hc φ) g (ψ := j φ') (congrArg Subtype.val e1))
      (cuspFormLp_rightTranslate_eq_rep μ (hc ψ) g (ψ := j ψ') (congrArg Subtype.val e2))).trans
      (UnitaryRep.inner_map_map (CuspidalSpectrum.cuspRep μ) _ _ _)
  refine isHerm_of_inner p (fun φ h => ?_) (fun k φ ψ => hr _ _ _ _ _ rfl rfl) (fun k φ ψ => hr _ _ _ _ _ rfl rfl)
    fun X φ ψ => ?_
  · have h5 : (j φ).1 = (0 : cuspForms F a).1 := congrArg Subtype.val (eq_zero_of_petersson_inner_self_eq_zero μ (hc φ) h)
    exact Subtype.ext (Subtype.ext h5)
  · have e1 : p (π.op (.lie X) φ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j φ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X φ).symm
    have e2 : p (π.op (.lie X) ψ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j ψ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X ψ).symm
    exact (congrArg₂ (· + ·) (congrArg (inner ℂ · (p ψ)) e1) (congrArg (inner ℂ (p φ)) e2)).trans
      (petersson_inner_lieAlgebra_skewAdjoint μ (e X) (hc φ) (hc ψ))

end UpperTheory.V.Af.Gk
