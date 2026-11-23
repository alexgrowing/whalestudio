import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality

noncomputable section

namespace PIW.HCFdeg

open MeasureTheory Filter Topology

section

variable {X H : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def toL2Map (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (hL v).toLp (c v)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(hL (u + v)).coeFn_toLp, Lp.coeFn_add ((hL u).toLp (c u)) ((hL v).toLp (c v)),
      (hL u).coeFn_toLp, (hL v).coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, map_add, Pi.add_apply]
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [(hL (a • u)).coeFn_toLp, Lp.coeFn_smul a ((hL u).toLp (c u)),
      (hL u).coeFn_toLp] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, map_smul, Pi.smul_apply]

theorem toL2Map_apply (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) (v : H) :
    toL2Map c hL v = (hL v).toLp (c v) := rfl

theorem toL2Map_apply_ae_eq (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) (v : H) :
    (toL2Map c hL v : X → ℂ) =ᵐ[μ] c v := by
  rw [toL2Map_apply]
  exact (hL v).coeFn_toLp

theorem continuous_toL2Map [CompleteSpace H] (c : H →ₗ[ℂ] (X → ℂ))
    (hcont : ∀ x, Continuous fun v => c v x) (hL : ∀ v, MemLp (c v) 2 μ) :
    Continuous (toL2Map c hL) := by
  refine LinearMap.continuous_of_seq_closed_graph (g := toL2Map c hL) ?_
  intro u v y hu hy
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, (toL2Map c hL (u n) : X → ℂ) x = c (u n) x :=
    ae_all_iff.2 fun n => toL2Map_apply_ae_eq c hL (u n)
  apply Lp.ext
  filter_upwards [hae, hall, toL2Map_apply_ae_eq c hL v] with x hx hxa hxv
  rw [hxv]
  have h2 : Tendsto (fun i => c (u (ns i)) x) atTop (𝓝 (c v x)) :=
    ((hcont x).tendsto v).comp (hu.comp hns.tendsto_atTop)
  refine tendsto_nhds_unique hx (h2.congr fun i => ?_)
  exact (hxa (ns i)).symm

end

theorem stBdd : StBdd := by
  intro X H _ μ _ _ _ c hcont hL
  exact ⟨⟨toL2Map c hL, continuous_toL2Map c hcont hL⟩, toL2Map_apply_ae_eq c hL⟩

end PIW.HCFdeg
