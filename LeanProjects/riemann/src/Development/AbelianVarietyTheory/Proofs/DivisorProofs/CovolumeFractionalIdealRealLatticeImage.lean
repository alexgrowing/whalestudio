import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzCovol

open NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def embPlace : (F →+* ℝ) ≃ {w : InfinitePlace F // IsReal w} where
  toFun τ := ⟨mk (Complex.ofRealHom.comp τ), IsTotallyReal.isReal _⟩
  invFun w := embedding_of_isReal w.2
  left_inv τ := by
    have h : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
      isReal_of_mk_isReal (IsTotallyReal.isReal _)
    ext x
    apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal h]
    rfl
  right_inv w := by
    apply Subtype.ext
    have : Complex.ofRealHom.comp (embedding_of_isReal w.2) = embedding w.1 := by
      ext x; simp
    simp only [this, mk_embedding]

theorem embPlace_symm_apply (w : {w : InfinitePlace F // IsReal w}) :
    (embPlace.symm w : F →+* ℝ) = embedding_of_isReal w.2 := rfl

instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed : RSp F ≃ₗ[ℝ] mixedSpace F where
  toFun x := (fun w => x (embPlace.symm w), 0)
  invFun p := WithLp.toLp 2 (fun τ => p.1 (embPlace τ))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by ext τ; simp
  right_inv p := by
    refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
    simp

theorem toMixed_remb (a : F) : toMixed (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
  simp [toMixed, embPlace_symm_apply]

theorem measurePreserving_toMixed :
    MeasurePreserving (toMixed (F := F)).toContinuousLinearEquiv volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (F →+* ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
    (embPlace (F := F))
  have h3 : MeasurePreserving (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
      (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) volume volume := by
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [Measure.volume_eq_prod, show (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac 0 from Measure.volume_pi_eq_dirac 0, Measure.prod_dirac]
  have h := h3.comp (h2.comp h1)
  have he : ⇑(toMixed (F := F)).toContinuousLinearEquiv =
      (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
        (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
        (embPlace (F := F))) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext (funext fun w => ?_) rfl
    simp [toMixed, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact h

end GlobalTheory.LipschitzCovol

open scoped Classical in
open GlobalTheory.LipschitzCovol in
theorem GlobalTheory.LipschitzCovol.covolume_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)],
    ZLattice.covolume (latOf N) = covol N := by
  intro F _ _ _ N hN _ _
  have hmem : ∀ x : RSp F, x ∈ latOf N ↔
      toMixed x ∈ mixedEmbedding.idealLattice F (Units.mk0 N hN) := by
    intro x
    rw [mem_latOf, mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, by simpa using ha, (toMixed_remb a).symm⟩
    · rintro ⟨a, ha, h⟩
      refine ⟨a, by simpa using ha, toMixed.injective ?_⟩
      rw [toMixed_remb, h]
  have hL : latOf N = ZLattice.comap ℝ (mixedEmbedding.idealLattice F (Units.mk0 N hN))
      (toMixed (F := F)).toContinuousLinearEquiv.toLinearMap :=
    Submodule.ext fun x => hmem x
  have key := ZLattice.covolume_comap (mixedEmbedding.idealLattice F (Units.mk0 N hN)) volume volume
    (measurePreserving_toMixed (F := F))
  have hc := covol_eq_covolume (Units.mk0 N hN)
  rw [Units.val_mk0] at hc
  rw [hc, ← key]
  congr 1
