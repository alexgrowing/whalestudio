import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.JmMono

section General

variable {F G U V W : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem occursTimes_of_isSubquotient {σ : Representation F G U} {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) {r : ℕ} (ho : OccursTimes σ π r) :
    OccursTimes σ P r := by
  obtain ⟨S, f, hf⟩ := h
  unfold GlobalTheory.SmGL.OccursTimes at ho ⊢
  obtain ⟨A, B, hBA, hAB, hiso⟩ := ho
  let ι : Representation.IntertwiningMap S.toRepresentation P :=
    ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hι : Function.Injective ι := fun a b hab => Subtype.val_injective hab
  refine ⟨fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (A i)),
    fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (B i)),
    fun i => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hBA i)),
    fun i j hij => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hAB i j hij)),
    fun i => ?_⟩
  exact GlobalTheory.JHMult.step_iff.mpr
    (GlobalTheory.JHMult.step_map ι hι
      (GlobalTheory.JHMult.step_comap f hf
        (GlobalTheory.JHMult.step_iff.mp (hiso i))))

theorem jhMult_le_of_isSubquotient (σ : Representation F G U) {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) : jhMult σ π ≤ jhMult σ P := by
  unfold GlobalTheory.SmGL.jhMult
  exact iSup₂_le fun r hr => le_iSup₂_of_le r (GlobalTheory.CompanionTheory.JmMono.occursTimes_of_isSubquotient h hr) le_rfl

end General

theorem jm_le_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P) :
    jm y hy π ≤ jm y hy P := by
  unfold Zc.jm
  exact GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient _
    (GlobalTheory.JacquetExact.isSubquotient_jac _ hP h)

end GlobalTheory.CompanionTheory.JmMono

end
