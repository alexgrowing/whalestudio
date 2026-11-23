import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongRegularised
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem pot_fin_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : HermLine ι)
    (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PoincareLelongRegularised.proof (hInt : PtsIntegrableStatement)
    (hMeas : GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement) : PoincareLelongRegularised.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB _ hs
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  have hM : ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (n + 1) → HermLine ι) j) := fun j =>
    Fin.cases (by simpa using hB) (fun i => by simpa using hL i) j
  have hlim := GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt hMeas) K ι P (n + 1) (Fin.cons B L) A s
    ⟨a, ha, hsa⟩ hP hM hA hsP
  rw [pot_fin_cons] at hlim
  have hg : ∀ ε, (fun z => Real.log ((GroundTheory.Heights₂.Heights.Inter.regLine A s ⟨a, ha, hsa⟩ ε).h z)) =
      regLog A s ε := by
    intro ε
    funext z
    rw [GroundTheory.Heights₂.Heights.Inter.log_regLine_h]
    rfl
  simpa only [hg] using hlim

end GroundTheory.Heights₂.Heights.Targets
