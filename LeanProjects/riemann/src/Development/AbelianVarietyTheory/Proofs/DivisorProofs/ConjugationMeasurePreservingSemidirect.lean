import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory.SupMeasInv

theorem supMeas_inv_invariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N Q : Subgroup G) (hnorm : ∀ h ∈ Q ⊔ N, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (νN : Measure N)
    (hR : ∀ n : N, MeasurePreserving (· * n) νN νN)
    (hI : MeasurePreserving (fun n : N => n⁻¹) νN νN)
    (hC : ∀ h ∈ Q ⊔ N, ∀ f : N → N, (∀ n, (f n : G) = h * n * h⁻¹) → MeasurePreserving f νN νN) :
    MeasurePreserving (fun p : ↥(Q ⊔ N) => p⁻¹) (supMeas N Q νN) (supMeas N Q νN) := by
  set H := Q ⊔ N with hH
  let ι : N → H := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N)
  have hιc : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  haveI hK : (N.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g.1 g.2 n.1 hn
  let D : H → Measure H := fun h => νN.map (fun n => ι n * h)
  have hfm : ∀ h : H, Measurable (fun n : N => ι n * h) := fun h =>
    (hιc.mul continuous_const).measurable

  have hD1 : ∀ h h' : H, (QuotientGroup.mk h : H ⧸ N.subgroupOf H) = QuotientGroup.mk h' → D h = D h' := by
    intro h h' hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
    set m : H := h⁻¹ * h' with hm
    have hc : (h : G) * (m : G) * (h : G)⁻¹ ∈ N := hnorm h.1 h.2 m.1 hq
    let c : N := ⟨_, hc⟩
    have hfun : (fun n : N => ι n * h') = (fun n : N => ι n * h) ∘ (· * c) := by
      funext n
      apply Subtype.ext
      simp [ι, c, hm, mul_assoc]
    show νN.map _ = νN.map _
    rw [hfun, ← Measure.map_map (hfm h) (hR c).measurable, (hR c).map_eq]

  have hD2 : ∀ h : H, (D h).map (fun p : H => p⁻¹) = D h⁻¹ := by
    intro h
    have hh : ((h⁻¹ : H) : G) ∈ Q ⊔ N := (h⁻¹).2
    let f : N → N := fun x => ⟨(h⁻¹ : G) * x * (h⁻¹ : G)⁻¹, hnorm _ hh x.1 x.2⟩
    have hf : MeasurePreserving f νN νN := hC _ hh f (fun n => rfl)
    have hfun : (fun p : H => p⁻¹) ∘ (fun n : N => ι n * h) =
        (fun n : N => ι n * h⁻¹) ∘ f ∘ (fun n : N => n⁻¹) := by
      funext n
      apply Subtype.ext
      simp [ι, f, mul_assoc]
    show (νN.map _).map _ = νN.map _
    rw [Measure.map_map continuous_inv.measurable (hfm h), hfun,
      ← Measure.map_map (hfm _) (hf.measurable.comp hI.measurable),
      ← Measure.map_map hf.measurable hI.measurable, hI.map_eq, hf.map_eq]
  refine ⟨continuous_inv.measurable, ?_⟩
  show (Measure.sum fun k : H ⧸ N.subgroupOf H => D (Quotient.out k)).map _ =
    Measure.sum fun k : H ⧸ N.subgroupOf H => D (Quotient.out k)
  rw [Measure.map_sum continuous_inv.measurable.aemeasurable]
  have hk : ∀ k : H ⧸ N.subgroupOf H, (D (Quotient.out k)).map (fun p : H => p⁻¹) = D (Quotient.out (k⁻¹ : H ⧸ N.subgroupOf H)) := by
    intro k
    rw [hD2]
    apply hD1
    rw [QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq']
  simp_rw [hk]
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  exact (Equiv.inv (H ⧸ N.subgroupOf H)).tsum_eq (fun k => D (Quotient.out k) s)

end GlobalTheory.SupMeasInv
