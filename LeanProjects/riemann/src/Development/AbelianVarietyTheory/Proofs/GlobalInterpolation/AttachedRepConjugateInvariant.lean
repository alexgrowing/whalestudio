import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory.RealGal.AttConj

section Gen

variable {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem inv_apply_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g y) = y := by
  show (g⁻¹ * g) y = y
  rw [inv_mul_cancel]
  rfl

theorem apply_inv_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : g ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) = y := by
  show (g * g⁻¹) y = y
  rw [mul_inv_cancel]
  rfl

theorem val_le_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y ≤ 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem val_lt_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff',
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω).injective]

theorem exists_of_fixed [CharZero K] [IsAlgClosure K Ω] (z : Ω) (hz : ∀ t : Formalism.ConjugateSelfDual.G K Ω, t z = z) :
    ∃ y : K, algebraMap K Ω y = z := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω)
  have hz' : z ∈ IntermediateField.fixedField (⊥ : IntermediateField K Ω).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro t _
    exact hz t
  rw [h] at hz'
  exact IntermediateField.mem_bot.1 hz'

theorem exists_ringEquiv (g : Formalism.ConjugateSelfDual.G F Ω)
    (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)) :
    ∃ γ : K ≃+* K, ∀ x, algebraMap K Ω (γ x) = g (algebraMap K Ω x) := by
  choose f hf using h1
  choose f' hf' using h2
  have hinj := (algebraMap K Ω).injective
  let φ : K →+* K :=
    { toFun := f
      map_one' := hinj (by simp [hf])
      map_mul' := fun x y => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun x y => hinj (by simp [hf]) }
  let ψ : K →+* K :=
    { toFun := f'
      map_one' := hinj (by simp [hf'])
      map_mul' := fun x y => hinj (by simp [hf'])
      map_zero' := hinj (by simp [hf'])
      map_add' := fun x y => hinj (by simp [hf']) }
  refine ⟨RingEquiv.ofRingHom φ ψ ?_ ?_, fun x => hf x⟩
  · ext x
    exact hinj (by
      show algebraMap K Ω (f (f' x)) = algebraMap K Ω x
      rw [hf, hf', apply_inv_apply])
  · ext x
    exact hinj (by
      show algebraMap K Ω (f' (f x)) = algebraMap K Ω x
      rw [hf', hf, inv_apply_apply])

variable [NumberField K]

theorem ine_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := K) A) :
    c s ∈ ReciprocityTheory.Gal.Ine (F := K) (g • A) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply]
    exact hs.2 _ hx

theorem frob_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (q : ℕ) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : Formalism.ConjugateSelfDual.IsFrob A q s) :
    Formalism.ConjugateSelfDual.IsFrob (g • A) q (c s) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply, map_pow]
    exact hs.2 _ hx

end Gen

end GlobalTheory.RealGal.AttConj
