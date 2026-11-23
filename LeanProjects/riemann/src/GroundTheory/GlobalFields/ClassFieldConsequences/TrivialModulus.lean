import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Unramified

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup SemiLocal
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension)
open scoped nonZeroDivisors

noncomputable section

universe u

section Unramified

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [Algebra K L]

def IsUnramifiedEverywhere : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) ∧
    ∀ v : InfinitePlace K, v.IsUnramifiedIn L

variable [NumberField L]

theorem isUnramifiedIn_iff_ramificationIdx (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  constructor
  · intro h w hw
    exact Ideal.ramificationIdx_eq_one_iff.2 (h w.asIdeal w.isPrime hw)
  · intro h P hP hPv
    have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    exact Ideal.ramificationIdx_eq_one_iff.1 (h ⟨P, hP, hne⟩ hPv)

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem infiniteLocalSymbol_eq_one_iff (v : InfinitePlace K) :
    infiniteLocalSymbol L v = 1 ↔ v.IsUnramifiedIn L := by
  by_cases hv : v.IsReal
  · constructor
    · intro h w hw
      have : w.LiesOver v := by
        subst hw
        exact ⟨rfl⟩
      by_contra hram
      have hneg : InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          ((-1 : (v.Completion)ˣ) : v.Completion) < 0 := by
        simp
      have h1 := infiniteLocalSymbol_apply L v hv ⟨w, this⟩ (-1)
      rw [h, if_pos hneg, MonoidHom.one_apply] at h1
      exact conjAt_ne_one hram h1.symm
    · intro h
      ext1 x
      obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
      have := w.2
      have hc := NumberField.InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v
      have hw : (w : InfinitePlace L).IsReal :=
        (NumberField.InfinitePlace.isUnramified_iff.1 (h _ hc)).resolve_right
          (by rw [hc]; exact NumberField.InfinitePlace.not_isComplex_iff_isReal.2 hv)
      rw [infiniteLocalSymbol_apply L v hv w, MonoidHom.one_apply, conjAt_of_isReal hw, ite_self]
  · rw [infiniteLocalSymbol_of_not_isReal L v hv]
    simp only [true_iff]
    intro w hw
    exact NumberField.InfinitePlace.isUnramified_iff.2
      (Or.inr (hw ▸ NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hv))

theorem units_le_ker_localSymbol_of_isUnramifiedIn (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact units_le_ker_localSymbol L v w ((isUnramifiedIn_iff_ramificationIdx K L v).1 h w.1 w.2)

theorem ideleSymbol_eq_one_of_isUnramifiedEverywhere (h : IsUnramifiedEverywhere K L)
    {x : IdeleGroup K} (hx : ∀ v, finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ideleSymbol K L x = 1 := by
  have hN : ∀ v, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker :=
    fun v ↦ units_le_ker_localSymbol_of_isUnramifiedIn K L v (h.1 v)
  have hNinf : ∀ w : InfinitePlace K, (⊤ : Subgroup (w.Completion)ˣ) ≤ (infiniteLocalSymbol L w).ker := by
    intro w
    rw [(infiniteLocalSymbol_eq_one_iff K L w).2 (h.2 w), MonoidHom.ker_one]
  have h1 : ∀ v, localSymbol L v (finiteProj v x) = 1 := fun v ↦ hN v (hx v)
  have h2 : ∀ w, infiniteLocalSymbol L w (infiniteProj w x) = 1 := fun w ↦ hNinf w (Subgroup.mem_top _)
  rw [ideleSymbol_apply]
  simp only [h1, h2, finprod_one, Finset.prod_const_one, mul_one]

end Unramified

section Descent

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem IsUnramifiedEverywhere.of_le {E M : IntermediateField K Ω} (hEM : E ≤ M) [FiniteDimensional K M]
    (hM : IsUnramifiedEverywhere K M) : IsUnramifiedEverywhere K E := by
  refine ⟨fun v ↦ GroundTheory.ProfCoh.isUnramifiedIn_of_le hEM v (hM.1 v), fun v w hw ↦ ?_⟩
  have : FiniteDimensional K E := GroundTheory.ProfCoh.finiteDimensional_of_le hEM
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  have : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite E M := Module.Finite.of_restrictScalars_finite K E M
  obtain ⟨w', rfl⟩ := NumberField.InfinitePlace.comap_surjective (K := M) w
  rw [NumberField.InfinitePlace.isUnramified_iff]
  by_cases hv : v.IsReal
  · left
    have hc : w'.comap (algebraMap K M) = v := by
      rw [IsScalarTower.algebraMap_eq K E M, NumberField.InfinitePlace.comap_comp, hw]
    have hw'r : w'.IsReal := (NumberField.InfinitePlace.isUnramified_iff.1 (hM.2 v w' hc)).resolve_right
      (by rw [hc]; exact NumberField.InfinitePlace.not_isComplex_iff_isReal.2 hv)
    exact hw'r.comap _
  · right
    rw [hw]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hv

end Descent

variable {K : Type u} [Field K] [NumberField K]

namespace Modulus

def one : Modulus K :=
  ⟨⊤, top_ne_bot, ∅⟩

theorem not_dvd_one_ideal (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (one : Modulus K).ideal := by
  change ¬ v.asIdeal ∣ ⊤
  rw [Ideal.dvd_iff_le]
  exact fun h ↦ v.isPrime.ne_top (top_le_iff.1 h)

theorem idelesOneMod_one : (one : Modulus K).idelesOneMod = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ one.mem_idelesOneMod.2
    ⟨fun v hv ↦ (not_dvd_one_ideal v hv).elim, fun _ hw ↦ hw.elim⟩

theorem congruenceSubgroup_one : (one : Modulus K).congruenceSubgroup = standardOpenSubgroup K := by
  rw [congruenceSubgroup_eq_inf, idelesOneMod_one, top_inf_eq]

theorem coprimeIdeals_one : (one : Modulus K).coprimeIdeals = ⊤ :=
  eq_top_iff.2 fun _ _ v hv ↦ (not_dvd_one_ideal v hv).elim

theorem rayUnits_one : (one : Modulus K).rayUnits = ⊤ := by
  rw [rayUnits, idelesOneMod_one, Subgroup.comap_top]

theorem classGroup_mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [← (ClassGroup.equiv K).injective.eq_iff, ClassGroup.equiv_mk, map_one,
    FractionalIdeal.canonicalEquiv_self, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

def toClassGroup : (one : Modulus K).coprimeIdeals →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (one : Modulus K).coprimeIdeals.subtype

theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  refine ⟨⟨FractionalIdeal.mk0 K I, by rw [coprimeIdeals_one]; trivial⟩, ?_⟩
  exact ClassGroup.mk_mk0 (K := K) I

theorem ker_toClassGroup : (toClassGroup (K := K)).ker = (one : Modulus K).principalRay := by
  ext I
  rw [MonoidHom.mem_ker, toClassGroup, MonoidHom.comp_apply, Subgroup.coe_subtype,
    classGroup_mk_eq_one_iff, mem_principalRay, rayUnits_one, MonoidHom.mem_range]
  simp only [Subgroup.mem_top, true_and]

def classGroupEquiv : (one : Modulus K).IdealRayClassGroup ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_toClassGroup.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)

theorem classGroupEquiv_mk (I : (one : Modulus K).coprimeIdeals) :
    classGroupEquiv (QuotientGroup.mk I) = ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  rfl

theorem classGroupEquiv_primeClass (v : HeightOneSpectrum (𝓞 K)) :
    classGroupEquiv (one.primeClass (not_dvd_one_ideal v)) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  rw [primeClass, classGroupEquiv_mk, ← ClassGroup.mk_mk0 (K := K)]
  congr 1

end Modulus

end

end GroundTheory.Global
