import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.endoS :
    Enlarge → Places → EndoBlockG → EndoBlockS := by
  intro hEn hP hG E _ _ _ hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  obtain ⟨J, _, D₁, D₂, B₁, B₂, hSat, hInf, hGr⟩ := hG E hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := fun w hw => by
    have hc : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hz : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hz, by rw [hc]; exact hz⟩
  let St : J → Prop := fun j =>
    ∀ w : Pl E, ¬ IsSplitAt w → inv (B₁ j w) = B₁ j w ∧ inv (B₂ j w) = B₂ j w
  have hu : ∀ i : {j // ¬ St j}, ∃ w : Pl E, ¬ IsSplitAt w ∧
      ¬ (inv (B₁ i.1 w) = B₁ i.1 w ∧ inv (B₂ i.1 w) = B₂ i.1 w) := fun i => by
    by_contra h
    exact i.2 fun w hw => by_contra fun h' => h ⟨w, hw, h'⟩
  choose u hu₁ hu₂ using hu
  classical
  refine ⟨{j // St j}, inferInstance, fun j => D₁ j.1, fun j => D₂ j.1, fun j => B₁ j.1, fun j => B₂ j.1,
    fun j w h => hSat j.1 w h, fun j => hInf j.1, fun j w h => j.2 w h, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hone, hzero, hval, hgeom⟩ :=
    hEn E hunr a b S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ St j} u (fun i => B₁ i.1) (fun i => B₂ i.1) fun i =>
      ⟨hu₁ i, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).1, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).2, hu₂ i⟩
  have hsm := hGr T' hT'S hT'Z e₁' e₂' ρ hone hρ fun j => by
    by_cases hj : St j
    · rw [hval (B₁ j) (B₂ j) fun i =>
        ⟨sat_card (hSat j (u i) (hoff _ (hu₁ i))).1, sat_card (hSat j (u i) (hoff _ (hu₁ i))).2,
          (hj (u i) (hu₁ i)).1, (hj (u i) (hu₁ i)).2⟩]
      exact hlt ⟨j, hj⟩
    · have h0 := hzero ⟨j, hj⟩
      simp only at h0
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom] using hsm
