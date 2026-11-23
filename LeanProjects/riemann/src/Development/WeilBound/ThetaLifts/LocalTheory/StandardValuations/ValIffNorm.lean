import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.VacuumImageIntertwiner

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict MeasureTheory ValuativeRel Topology
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

theorem int_iff (x : Fv F v) : x ∈ v.adicCompletionIntegers F ↔ valuation (Fv F v) x ≤ 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact ((ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one (x := x)).symm

theorem val_iff_norm (x : Fv F v) : valuation (Fv F v) x = 1 ↔ ‖x‖ = 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one, le_antisymm_iff, le_antisymm_iff,
    Valued.toNormedField.norm_le_one_iff, Valued.toNormedField.one_le_norm_iff]

theorem norm_nabs (x : (Fv F v)ˣ) : ‖(x : Fv F v)‖ = GlobalTheory.SplitWeil.nabs _ x := by
  have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (x : Fv F v) x.ne_zero
  rw [Units.mk0_val] at this
  exact (congrArg NNReal.toReal this).symm

end PositivityTheory.ThKG.Std
