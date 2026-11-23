import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

theorem haar_open_pos {k r : ℕ} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {O : Set (Mt k r)}
    (hO : IsOpen O) {g₀ : Mt k r} (hg₀ : Matrix.of g₀ ∈ B.GV k r) (hg₀O : g₀ ∈ O) : μ O ≠ 0 := by
  intro h0
  have hnull : ∀ b ∈ B.GV k r, μ (lmulM (k := k) (r := r) b ⁻¹' O) = 0 := by
    intro b hb
    have hm : Measurable (lmulM (k := k) (r := r) b) := (BesselUnitaryEquiv.continuous_lmulM b).measurable
    rw [← Measure.map_apply hm hO.measurableSet, hμ.left b hb, h0]
  let U : {b : B.Mat k r // b ∈ B.GV k r} → Set (Mt k r) := fun b => lmulM (k := k) (r := r) b.1 ⁻¹' O
  have hUo : ∀ i, IsOpen (U i) := fun i => hO.preimage (BesselUnitaryEquiv.continuous_lmulM i.1)
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hcov : {x : Mt k r | Matrix.of x ∈ B.GV k r} ⊆ ⋃ i, U i := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨Matrix.of g₀ * (Matrix.of x)⁻¹,
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hg₀ (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem hx)⟩, ?_⟩
    have hx' : Matrix.of x ∈ B.GV k r := hx
    have e : lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x = g₀ := by
      unfold lmulM
      rw [mul_assoc, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hx').2, mul_one]
      rfl
    show lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x ∈ O
    rw [e]
    exact hg₀O
  have hGV0 : μ {x : Mt k r | Matrix.of x ∈ B.GV k r} = 0 := by
    refine measure_mono_null (hcov.trans hT.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun i _ => hnull i.1 i.2
  have hsub : (Set.univ : Set (Mt k r)) ⊆ {x : Mt k r | Matrix.of x ∈ B.GV k r} ∪ (B.GV k r)ᶜ := by
    intro x _
    by_cases hx : Matrix.of x ∈ B.GV k r
    · exact Or.inl hx
    · exact Or.inr hx
  have huniv : μ Set.univ = 0 := measure_mono_null hsub (measure_union_null hGV0 hμ.conc)
  exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

end Formalism.FourierDecayAlt.P.CutMP.ER
