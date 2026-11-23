import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormCoeffMinpolyLeOneOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEmbExist

variable {E : Type} [Field E] [NumberField E]

theorem isIntegral_or_isIntegral_inv (w : HeightOneSpectrum (𝓞 E)) (x : GlobalTheory.LocDict.Kbar w) :
    IsIntegral (w.adicCompletionIntegers E) x ∨ IsIntegral (w.adicCompletionIntegers E) x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl isIntegral_zero
  let K := w.adicCompletion E
  let L : IntermediateField K (GlobalTheory.LocDict.Kbar w) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hy0 : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let f : L →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w := L.val.restrictScalars _
  have hf : Function.Injective f := L.val.injective
  have key : ∀ z : L, IsIntegral (w.adicCompletionIntegers E) (z : GlobalTheory.LocDict.Kbar w) ↔
      Valued.v (Algebra.norm K z) ≤ 1 := fun z => by
    rw [← GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one E w L z]
    exact isIntegral_algHom_iff f hf
  have hyx : ((y⁻¹ : L) : GlobalTheory.LocDict.Kbar w) = x⁻¹ := by simp [y]
  have hmul : Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  rcases le_total (Valued.v (Algebra.norm K y)) 1 with h | h
  · exact Or.inl ((key y).2 h)
  · right
    rw [← hyx]
    refine (key _).2 ?_
    calc Valued.v (Algebra.norm K y⁻¹) = 1 * Valued.v (Algebra.norm K y⁻¹) := (one_mul _).symm
      _ ≤ Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) := mul_le_mul' h le_rfl
      _ = 1 := hmul

def intValRing (w : HeightOneSpectrum (𝓞 E)) : ValuationSubring (GlobalTheory.LocDict.Kbar w) where
  toSubring := (integralClosure (w.adicCompletionIntegers E) (GlobalTheory.LocDict.Kbar w)).toSubring
  mem_or_inv_mem' x := isIntegral_or_isIntegral_inv w x

theorem mem_intValRing {w : HeightOneSpectrum (𝓞 E)} (x : GlobalTheory.LocDict.Kbar w) :
    x ∈ intValRing w ↔ IsIntegral (w.adicCompletionIntegers E) x := Iff.rfl

theorem isIntegral_algebraMap_iff (w : HeightOneSpectrum (𝓞 E)) (e : E) :
    IsIntegral (w.adicCompletionIntegers E) (algebraMap E (GlobalTheory.LocDict.Kbar w) e) ↔
      w.valuation E e ≤ 1 := by
  let K := w.adicCompletion E
  have h1 : algebraMap E (GlobalTheory.LocDict.Kbar w) e = algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) :=
    IsScalarTower.algebraMap_apply E K _ e
  let f : K →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w :=
    (IsScalarTower.toAlgHom K K (GlobalTheory.LocDict.Kbar w)).restrictScalars _
  rw [h1, show algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) = f (algebraMap E K e) from rfl,
    isIntegral_algHom_iff f f.toRingHom.injective, IsIntegrallyClosed.isIntegral_iff (K := K)]
  have hv : Valued.v (algebraMap E K e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  constructor
  · rintro ⟨y, hy⟩
    have h := y.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v (y : K) ≤ 1 at h
    rw [show (y : K) = algebraMap E K e from hy, hv] at h
    exact h
  · intro h
    refine ⟨⟨algebraMap E K e, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]
    exact h

theorem valuation_lt_one_iff_of_mem_iff {Ω : Type} [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (hB : ∀ e : E, algebraMap E Ω e ∈ B ↔ w.valuation E e ≤ 1) (e : E) :
    B.valuation (algebraMap E Ω e) < 1 ↔ w.valuation E e < 1 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have ha : algebraMap E Ω e ≠ 0 := (map_ne_zero _).2 he
  have h1 : B.valuation (algebraMap E Ω e) < 1 ↔ ¬ B.valuation (algebraMap E Ω e⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)), not_le]
  have h2 : w.valuation E e < 1 ↔ ¬ w.valuation E e⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he)), not_le]
  rw [h1, h2, ValuationSubring.valuation_le_one_iff, hB]

end GlobalTheory.LocEmbExist

namespace GlobalTheory.LocDict

theorem exists_isLocEmb : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ ι : Ω →ₐ[E] Kbar w, IsLocEmb A w ι := by
  intro E Ω _ _ _ _ _ A w h
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[E] Kbar w := IsAlgClosed.lift
  let A₀ : ValuationSubring Ω := (GlobalTheory.LocEmbExist.intValRing w).comap ι₀.toRingHom
  have hA₀ : ∀ z, z ∈ A₀ ↔ IsIntegral (w.adicCompletionIntegers E) (ι₀ z) := fun _ => Iff.rfl
  have hE : ∀ e : E, algebraMap E Ω e ∈ A₀ ↔ w.valuation E e ≤ 1 := fun e => by
    rw [hA₀, ι₀.commutes]
    exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff w e
  have hP : IsPlaceOver A₀ w := fun x => by
    rw [GlobalTheory.LocEmbExist.valuation_lt_one_iff_of_mem_iff A₀ w hE]
    exact w.valuation_lt_one_iff_mem (K := E) x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hP h
  refine ⟨ι₀.comp (σ.symm : Ω →ₐ[E] Ω), fun z => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA₀]
  rfl

end GlobalTheory.LocDict
