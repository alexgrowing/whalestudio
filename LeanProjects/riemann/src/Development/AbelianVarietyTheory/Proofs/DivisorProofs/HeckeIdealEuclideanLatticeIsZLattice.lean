import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckePoisson

open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]

def toMixed {φ : I → K →+* ℂ} (h : IsCMType φ) : EuclideanSpace ℂ I ≃ₗ[ℝ] mixedEmbedding.mixedSpace K := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  let b : I ≃ InfinitePlace K := Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)
  exact
  { toFun := fun z => (0, fun w => if φ (b.symm w.1) = (InfinitePlace.mk (φ (b.symm w.1))).embedding
        then z (b.symm w.1) else conj (z (b.symm w.1)))
    invFun := fun x => WithLp.toLp 2 (fun i => if φ i = (InfinitePlace.mk (φ i)).embedding
        then x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩
        else conj (x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩))
    map_add' := fun x y => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.snd_add, Pi.add_apply, PiLp.add_apply]; split_ifs <;> simp)
    map_smul' := fun r x => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply]
      split_ifs <;> simp [Complex.real_smul])
    left_inv := fun z => by
      ext i
      have hi : b.symm (InfinitePlace.mk (φ i)) = i := b.symm_apply_apply i
      simp only [hi]
      split_ifs <;> simp
    right_inv := fun x => by
      refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
      have e : (⟨InfinitePlace.mk (φ (b.symm w.1)), IsTotallyComplex.isComplex _⟩ : {w : InfinitePlace K // w.IsComplex}) = w :=
        Subtype.ext (b.apply_symm_apply w.1)
      simp only [e]
      split_ifs <;> simp }

theorem toMixed_embA {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [toMixed, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, embA_apply]
  set i := (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).symm w.1 with hi
  have hw : InfinitePlace.mk (φ i) = w.1 :=
    (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).apply_symm_apply w.1
  split_ifs with hs
  · rw [hs, hw]
  · have hc := (InfinitePlace.embedding_mk_eq (φ i)).resolve_left (fun e => hs e.symm)
    rw [← hw, hc]
    simp [ComplexEmbedding.conjugate_coe_eq]

open Classical in
theorem lat_eq_comap {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by
  ext z
  rw [mem_lat]
  change _ ↔ toMixed h z ∈ mixedEmbedding.idealLattice K _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : K), (FractionalIdeal.mem_coeIdeal _).2 ⟨μ, hμ, rfl⟩, (toMixed_embA h μ).symm⟩
  · rintro ⟨y, hy, hyz⟩
    have hy' : y ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hy
    obtain ⟨μ, hμ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy'
    exact ⟨μ, hμ, (toMixed h).injective (by rw [toMixed_embA]; exact hyz)⟩

theorem lat_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ →
      ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  intro K _ _ _ I _ φ h M hM
  classical
  rw [lat_eq_comap h M hM]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.HeckePoisson
