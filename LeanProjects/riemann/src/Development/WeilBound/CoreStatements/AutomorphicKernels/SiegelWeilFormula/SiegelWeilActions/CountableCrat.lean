import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SectionSumIntegralExpand
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernHodgeTateFacts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

variable {R L}

theorem continuous_th' (T' : nF σ L.Y L.b) : Continuous fun β : nA σ L.Y L.b => th' (d := d) T' β :=
  kfour.continuous_chr (σ := σ) (Y := L.Y) (b := L.b) d.ok.good.std.1 T'.1.1

theorem countable_crat : Countable (Crat L) := by
  have : Countable L.ratV := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
      (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
    obtain ⟨v, hv⟩ := C1.ratV_inc u.2
    exact ⟨v, Subtype.ext hv.symm⟩
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (Set.range (algebraMap F (AF F))) := (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun c : Crat L =>
    ((⟨c.1.1, c.2.1⟩ : L.ratV), (⟨c.1.2, c.2.2⟩ : Set.range (algebraMap F (AF F)))))
    fun c c' hcc => ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
  exact Subtype.ext (Prod.ext hcc.1 (congrArg Subtype.val hcc.2))

end PositivityTheory.SiegelWeilFormula.Act.C5

end
