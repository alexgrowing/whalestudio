import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem compSt : CompSt := by
  intro D V H _ _ _ π hπ w W hW
  set ρ := π.comp (embArch D.sp.cm.sig V.gram w) with hρdef
  have hρ : IsUnitaryRep ρ := isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  let δ : IrrU (GArch D.sp.cm.sig V.gram w) := ⟨W, hW.1.rep, isIrrUnitary_rep hρ hW⟩
  refine ⟨δ, ?_⟩
  show isoPart δ.π ρ ⊤ = ⊤
  set P := isoPart δ.π ρ ⊤ with hPdef
  have hP : IsSubrep ρ P := isSubrep_isoPart

  have hcomm : ∀ g' : GA D V, projArch D.sp.cm.sig V.gram w g' = 1 → ∀ v ∈ P, π g' v ∈ P := by
    intro g' hg' v hv
    have hle : P ≤ P.comap ((π g' : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine isoPart_le (hP.1.preimage (π g').continuous) fun T hT x => ?_
      show π g' (T x) ∈ P
      have hT' : (π g').comp T ∈ homIn δ.π ρ ⊤ := by
        refine mem_homIn_top.2 fun h y => ?_
        have hc : Commute (embArch D.sp.cm.sig V.gram w h) g' := commute_embArch _ _ h hg'
        have e1 : π g' (π (embArch D.sp.cm.sig V.gram w h) (T y)) = π (embArch D.sp.cm.sig V.gram w h) (π g' (T y)) := by
          rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hc.eq]
        simp only [ContinuousLinearMap.comp_apply]
        rw [(mem_homIn_top.1 hT) h y]
        exact e1
      exact apply_mem_isoPart hT' x
    exact hle hv
  have hinv : IsSubrep π P := by
    refine ⟨hP.1, fun g v hv => ?_⟩
    set x := projArch D.sp.cm.sig V.gram w g
    set g' : GA D V := (embArch D.sp.cm.sig V.gram w x)⁻¹ * g
    have hg' : projArch D.sp.cm.sig V.gram w g' = 1 := by
      simp [g', x, map_mul, map_inv]
    have hg : g = embArch D.sp.cm.sig V.gram w x * g' := by simp [g']
    rw [hg, map_mul, ContinuousLinearMap.mul_apply]
    exact hP.2 x _ (hcomm g' hg' v hv)
  have hne : P ≠ ⊥ := by
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
    intro hbot
    have hsub : W.subtypeL ∈ homIn δ.π ρ ⊤ := mem_homIn_top.2 fun h z => rfl
    have hm : W.subtypeL ⟨y, hyW⟩ ∈ P := apply_mem_isoPart hsub _
    rw [hbot] at hm
    exact hy0 ((Submodule.mem_bot ℂ).1 hm)
  exact (hπ.irred.2 P hinv).resolve_left hne

end MainStatements.Flath2
