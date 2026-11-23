import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableCpowDiscr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.GlueSign

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem inv_eq_self_of_sq {η : Fˣ →* ℂˣ} (h2 : ∀ a, η a * η a = 1) : η⁻¹ = η := by
  ext a
  have := h2 a
  simp only [MonoidHom.inv_apply]
  rw [inv_eq_of_mul_eq_one_left this]

theorem isUnramifiedChar_one : IsUnramifiedChar (1 : Fˣ →* ℂˣ) := by
  rw [isUnramifiedChar_iff]; intro u _; rfl

variable [MeasurableSpace F] [BorelSpace F]

theorem localEpsilon_one_half (ψ : AddChar F Circle) : localEpsilon (1 : Fˣ →* ℂˣ) ψ (1 / 2) = 1 := by
  rw [localEpsilon_of_isUnramified isUnramifiedChar_one]
  simp

theorem gam_half {η : Fˣ →* ℂˣ} (hc : Continuous η) (hn : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1) (h2 : ∀ a, η a * η a = 1)
    (ψ : AddChar F Circle) : gam ψ η (1 / 2) = localEpsilon η ψ (1 / 2) := by
  have h : localLFactor η (1 / 2) ≠ 0 := by
    refine localLFactor_ne_zero hc ?_
    simp [quasiCharExponent, hn]
  rw [gam, inv_eq_self_of_sq h2, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  field_simp

theorem gam_one_half (ψ : AddChar F Circle) : gam ψ (1 : Fˣ →* ℂˣ) (1 / 2) = 1 := by
  rw [gam_half continuous_const (by simp) (by simp), localEpsilon_one_half]

end Local

section Local2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

theorem lamE_eq {η : Fˣ →* ℂˣ} (hc : Continuous η) (hn : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1) (h2 : ∀ a, η a * η a = 1)
    (ψ : AddChar F Circle) : GL2LocalData.lamE E ψ η = localEpsilon η ψ (1 / 2) := by
  rw [GL2LocalData.lamE, gam_one_half, gam_one_half, gam_half hc hn h2]
  simp

end Local2

section Sym

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

instance isAbelianGalois_quadratic : IsAbelianGalois ℚ K := {}

theorem heckeChar_apply (c : IdeleClassGroup ℚ) :
    ((Quadratic.heckeChar K c : Circle) : ℂ) = Quadratic.galChar K (reciprocityMap ℚ K c) := by
  rw [Quadratic.heckeChar, heckeCharacterOfChar_apply, reciprocityMap_intermediateField,
    ← charBar_restrictNormalHom (Quadratic.galChar K) (reciprocityMap ℚ K c)]
  rfl

theorem localChar_apply (v : Pl) (a : (Qv v)ˣ) :
    ((localChar (Quadratic.heckeChar K) v a : ℂˣ) : ℂ) = Quadratic.galChar K (localSymbol K v a) := by
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply,
    heckeChar_apply, reciprocityMap_mk, ideleSymbol_finiteEmbedding]

theorem infiniteComponent_apply (w : InfinitePlace ℚ) (a : (w.Completion)ˣ) :
    (((Quadratic.heckeChar K).infiniteComponent w a : Circle) : ℂ) = Quadratic.galChar K (infiniteLocalSymbol K w a) := by
  change (((Quadratic.heckeChar K) (IdeleClassGroup.mk ℚ (IdeleGroup.infiniteEmbedding w a)) : Circle) : ℂ) = _
  rw [heckeChar_apply, reciprocityMap_mk, ideleSymbol_infiniteEmbedding]

end Sym

section Sym2

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

open Classical in
theorem galChar_val (σ : Gal(K/ℚ)) : ((Quadratic.galChar K σ : ℂˣ) : ℂ) = if σ = 1 then 1 else -1 := by
  split_ifs with h
  · rw [h, Quadratic.galChar_one_apply]; rfl
  · rw [Quadratic.galChar_apply_of_ne_one K h]; simp

end Sym2

section Inf

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem infiniteLocalSymbol_neg_one [IsTotallyComplex K] (w : InfinitePlace ℚ) :
    infiniteLocalSymbol K w (-1) ≠ 1 := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver K w
  rw [infiniteLocalSymbol_apply K w hv u, if_pos (by simp)]
  refine conjAt_ne_one (InfinitePlace.isRamified_iff.2 ⟨IsTotallyComplex.isComplex _, ?_⟩)
  exact IsTotallyReal.isReal _

theorem infiniteComponent_neg_one [IsTotallyComplex K] (w : InfinitePlace ℚ) :
    (((Quadratic.heckeChar K).infiniteComponent w (-1) : Circle) : ℂ) = -1 := by
  rw [infiniteComponent_apply, galChar_val, if_neg (infiniteLocalSymbol_neg_one K w)]

end Inf

section Prod

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

attribute [local instance] galCommGroup

end Prod

section Root

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
theorem heckeChar_inv : (Quadratic.heckeChar K)⁻¹ = Quadratic.heckeChar K := by
  ext c
  have h := heckeChar_apply K c
  rw [galChar_val] at h
  change (((Quadratic.heckeChar K c)⁻¹ : Circle) : ℂ) = _
  rw [Circle.coe_inv, h]
  split_ifs <;> simp

end Root

section Root2

open Complex

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] [IsTotallyComplex K]

end Root2

section Main

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

end Main

end GlobalTheory.CompanionTheory.GlueSign
