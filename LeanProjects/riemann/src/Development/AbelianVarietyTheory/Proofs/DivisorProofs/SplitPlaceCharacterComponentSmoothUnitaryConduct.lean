import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

noncomputable section

namespace GlobalTheory.ChrWLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valuation_eq_one_iff {v : Pl F} (x : Fv F v) :
    valuation (Fv F v) x = 1 ↔ Valued.v x = 1 := by
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isUnram_chrW_iff (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t) := by
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := (SplitTie.complMap_bijective t (splitPrime_under t)).2 (y : _)
    have hv : Valued.v a = 1 := by
      rw [← SplitTie.valued_complMap t (splitPrime_under t), ha]; exact hy
    have h0 : a ≠ 0 := by rintro rfl; simp at hv
    have h1 := h (Units.mk0 a h0) ((valuation_eq_one_iff _).2 hv)
    rw [← h1]
    exact congrArg (locChar χ _) (Units.ext ha.symm)
  · intro h x hx
    exact h _ (show Valued.v (complMap (splitPrime_under t) (x : Fv F v)) = 1 by
      rw [SplitTie.valued_complMap t (splitPrime_under t)]; exact (valuation_eq_one_iff _).1 hx)

theorem chrW_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E),
    IsHecke F E χ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  intro F E _ _ _ _ _ χ hχ v t
  have hc := GlobalTheory.ChrWSmooth.continuous_chrW hχ.1 t
  refine ⟨⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ hc, GlobalTheory.ChrWSmooth.isUnitaryChar_chrW χ t⟩, ?_,
    isUnram_chrW_iff χ t⟩
  exact GlobalTheory.GaussNonvanish.exists_condLE (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec _
    (Units.continuous_val.comp hc)

end GlobalTheory.ChrWLocal
