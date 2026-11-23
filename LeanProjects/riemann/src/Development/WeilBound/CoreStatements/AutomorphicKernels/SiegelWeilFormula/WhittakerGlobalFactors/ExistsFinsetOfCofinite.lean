import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.UnrPDifferentiable

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.W

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix

theorem hermOf_unit {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0)
    (R : Type) [CommRing R] [Algebra F R] :
    IsUnit ((hermOf R σ T hT : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
  have h : (T.map (inclR (F := F) R)).det = inclR (F := F) R T.det := (RingHom.map_det _ _).symm
  show IsUnit (T.map (inclR R)).det
  rw [h]
  exact (Ne.isUnit hdet).map _

theorem isSchwartzInf_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ} :
    IsSchwartzInf (0 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) := by
  intro N e _ _
  exact ⟨0, fun x => by simp⟩

theorem exists_finset_of_cofinite {α : Type} {p : α → Prop} (h : ∀ᶠ v in Filter.cofinite, p v) :
    ∃ S : Finset α, ∀ v, v ∉ S → p v := by
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv ((Set.Finite.mem_toFinset _).2 h')

end PositivityTheory.SiegelWeilFormula.Gen.W

end
