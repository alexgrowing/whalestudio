import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.choiceM :
    UpperTheory.V.Z.Mult.ChoiceM := by
  classical
  intro E _ _ _ n hn π hns μ e hμ S hS K' hK' hKn
  obtain ⟨-, hc, hInf, hSec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hbad : {w : Pl E | ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (((GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E n π).and
      (GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ).1).and hK'.2)
  obtain ⟨Bd, hBd⟩ : ∃ Bd : Finset (Pl E), ∀ w, w ∈ Bd ↔
      ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w) :=
    ⟨hbad.toFinset, fun w => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hgood : ∀ w, w ∉ Bd → ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w := fun w hw => by
    by_contra h
    exact hw ((hBd w).2 h)
  have hsplit : ∀ w ∈ Bd, IsSplitAt w := fun w hw => by
    by_contra hs
    exact (hBd w).1 hw ⟨⟨hns w hs, fun x hx => by
      rw [hμ.2.2.1 w hs]
      exact GlobalTheory.CompanionTheory.MuOpen.unrChar_apply_of_isUnitAt w _ x hx⟩, hKn w hs⟩
  have hcs : ∀ w, IsSplitAt w → IsSplitAt (cPl w) := fun w hw =>
    (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hw).symm)
  obtain ⟨m, hm, hmS⟩ : ∃ m : Pl E → Pl E, (∀ w, m w ∈ S ∧ (m w = w ∨ m w = cPl w)) ∧ ∀ w ∈ S, m w = w :=
    ⟨fun w => if w ∈ S then w else cPl w, fun w => by
      by_cases h : w ∈ S
      · simp [h]
      · simpa [h] using ((hSec S hS w).1.resolve_left h), fun w h => by simp [h]⟩
  have hms : ∀ w, IsSplitAt w → IsSplitAt (m w) := fun w hw => by
    rcases (hm w).2 with e | e
    · rwa [e]
    · rw [e]; exact hcs w hw
  obtain ⟨w₀, hw₀, hw₀'⟩ := (hInf.diff (Bd ∪ Bd.image cPl).finite_toSet).nonempty
  have hn₀ : w₀ ∉ Bd := fun h => hw₀' (by simp [h])
  have hn₁ : cPl w₀ ∉ Bd := fun h => hw₀' (by
    refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, (hc w₀).1⟩)))
  obtain ⟨w₁, hw₁, hw₁S, hw₁s⟩ : ∃ w₁, w₁ ∉ Bd ∧ w₁ ∈ S ∧ IsSplitAt w₁ := by
    refine ⟨m w₀, ?_, (hm w₀).1, hms w₀ hw₀⟩
    rcases (hm w₀).2 with e | e <;> rwa [e]
  choose! B hB using fun w (h : ∃ B, (CG.mk π).HasSat w B) => h
  choose τ hτ using fun w => GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
  obtain ⟨b, hb⟩ := (hgood w₁ hw₁).1.1
  obtain ⟨g, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regFn E n w₁ (τ w₁) b
    (((GlobalTheory.Cong.satake_locComp E n π w₁ (τ w₁) (hτ w₁).1).1 b).1 hb)
  refine ⟨insert w₁ (Bd.image m), B, τ, w₁, g, fun w hw => ?_, fun w hw hwZ => ?_, fun w hw => ?_,
    fun w _ => (hτ w).1, Finset.mem_insert_self _ _, h1, h2, h3⟩
  · rcases Finset.mem_insert.1 hw with rfl | h
    · exact ⟨hw₁S, hw₁s⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hm u).1, hms u (hsplit u hu)⟩
  · refine (hgood w fun h => hwZ ?_).2
    have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
    rwa [hmS w hw] at hi
  · have hw' : w ∉ Bd := fun h => by
      have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
      rcases (hm w).2 with e | e
      · exact hw.1 (e ▸ hi)
      · exact hw.2 (e ▸ hi)
    exact ⟨hB w (hgood w hw').1.1, (hgood w hw').1.2⟩
