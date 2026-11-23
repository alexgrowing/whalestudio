import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
open MeasureTheory

namespace GlobalTheory.ArchimedeanLineL2

theorem archOp_lintegral_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (N : ℕ) (C : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
      (f : SInf F (Fin n × Fin d)),
      ∫⁻ x, ‖archOp om h f (C.symm x)‖ₑ ^ 2 = ∫⁻ x, ‖f (C.symm x)‖ₑ ^ 2 := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex h hh N C f
  haveI := GlobalTheory.ArchimedeanUnitaryL2.opensMeasurable F (Fin n × Fin d)
  set μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.map C.symm volume with hμ
  haveI : μ.IsAddHaarMeasure := C.symm.isAddHaarMeasure_map volume
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : ∀ f' : SInf F (Fin n × Fin d), tens (evI F) (⇑f') r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f' => Submodule.subset_span ⟨f', g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchimedeanUnitaryL2.snd_eq_zero hz i, add_zero]
  have hU := (IsUWeilPair.isUSplitting hW).unit μA hμA (1, h) (tens (evI F) (⇑f) r) (hS f)
  have hAct : om (1, h) (tens (evI F) (⇑f) r) = tens (evI F) (⇑(archOp om h f)) r :=
    acts_archOp om h f (hex h hh f) r ⟨hr, hS f⟩
  rw [hAct] at hU
  have h1 := ((hc (archOp om h f)).symm.trans hU).trans (hc f)
  have h2 := (ENNReal.mul_right_inj hc0 hct).1 h1
  rw [hμ, lintegral_map ((archOp om h f).continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable,
    lintegral_map (f.continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable] at h2
  exact h2

end GlobalTheory.ArchimedeanLineL2

end
