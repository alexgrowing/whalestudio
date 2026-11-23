import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAPsiVScPSame

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_vecV_add' (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a + b) = PI.FinKW.vecV X.B.I v a + PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero' (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.vecV X.B.I v (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem scalarAt_one_mem_integralAdeles (p : TypX X) : scP X p 1 ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  have h := scalarAt_mem_integralAdeles X p 1
  simpa using h

theorem imA_lift_sp (p : TypX X) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    {a : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (ha : a ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
      {w | ∃ t ∈ OEp X p, ∃ s ∈ PI.FinKW.vecV X.B.I p.1 '' S, w = t • s}) :
    ∃ A ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S, PI.FinKW.vecV X.B.I p.1 A = a ∧
      ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ⟨τ, hτ, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
    refine ⟨(scP X p 1 * τ) • s, ?_, ?_, ?_⟩
    · exact Submodule.smul_mem _
        (⟨scP X p 1 * τ, Subring.mul_mem _ (scalarAt_one_mem_integralAdeles X p) hτ⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span hs)
    · rw [imA_vecV_smul', map_mul, component_scalarAt_same, map_one, one_mul]
    · intro v hv
      rw [imA_vecV_smul', map_mul, component_scalarAt_of_ne X p v hv, zero_mul, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

theorem imA_lift_lat (p : TypX X) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    refine ⟨scP X p 1 • (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)),
      Submodule.smul_mem _ (⟨_, scalarAt_one_mem_integralAdeles X p⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hin, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, map_one, one_smul]
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

end MassDataIdxSteps
