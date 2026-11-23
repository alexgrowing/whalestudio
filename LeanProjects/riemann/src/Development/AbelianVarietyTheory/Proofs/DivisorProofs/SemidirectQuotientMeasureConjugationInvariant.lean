import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory.SupMeas

theorem supMeas_sfinite_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G), (∀ h ∈ Q ⊔ N, ∃ n ∈ N, ∃ q ∈ Q, n * q = h) → ∀ [Countable Q], (∀ h ∈ Q ⊔ N, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → ∀ (νN : Measure N) [SFinite νN], (∀ n : N, MeasurePreserving (· * n) νN νN) → (∀ h ∈ Q ⊔ N, ∀ f : N → N, (∀ n, (f n : G) = h * n * h⁻¹) → MeasurePreserving f νN νN) → SFinite (supMeas N Q νN) ∧ ∀ h : ↥(Q ⊔ N), MeasurePreserving (h * ·) (supMeas N Q νN) (supMeas N Q νN) := by
  intro G _ _ _ _ _ _ _ _ N Q hdec _ hnorm νN _ hR hC
  have hmeasD : ∀ h : ↥(Q ⊔ N),
      Measurable (fun n : N => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * h) := by
    intro h
    have : Measurable (fun n : N => ((n : G) * (h : G))) := measurable_subtype_coe.mul_const _
    exact this.subtype_mk

  have step1 : ∀ (h : ↥(Q ⊔ N)) (n' : N),
      νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n
        * (h * Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n'))
      = νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * h) := by
    intro h n'
    let c : N := ⟨h * n' * (h : G)⁻¹, hnorm h h.2 n' n'.2⟩
    have hfun : (fun n : N => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n
        * (h * Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n'))
        = (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * h) ∘ (· * c) := by
      funext n; apply Subtype.ext; simp [c, mul_assoc]
    rw [hfun, ← Measure.map_map (hmeasD h) (hR c).measurable, (hR c).map_eq]

  have step2 : ∀ g h : ↥(Q ⊔ N),
      (νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * h)).map (g * ·)
      = νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * (g * h)) := by
    intro g h
    let f : N → N := fun n => ⟨g * n * (g : G)⁻¹, hnorm g g.2 n n.2⟩
    have hf := hC g g.2 f (fun n => rfl)
    rw [Measure.map_map (by fun_prop) (hmeasD h)]
    have : (g * ·) ∘ (fun n : N => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * h)
        = (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * (g * h)) ∘ f := by
      funext n; apply Subtype.ext; simp [f, mul_assoc]
    rw [this, ← Measure.map_map (hmeasD _) hf.measurable, hf.map_eq]

  have step3 : ∀ (g : ↥(Q ⊔ N)) (k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)),
      νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * Quotient.out (g • k))
      = νN.map (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * (g * Quotient.out k)) := by
    intro g k
    have hk : (QuotientGroup.mk (g * Quotient.out k) : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N))
        = QuotientGroup.mk (Quotient.out (g • k)) := by
      rw [QuotientGroup.out_eq']
      conv_rhs => rw [← QuotientGroup.out_eq' k]
      rfl
    rw [QuotientGroup.eq] at hk
    let n' : N := ⟨_, Subgroup.mem_subgroupOf.mp hk⟩
    have hout : Quotient.out (g • k)
        = (g * Quotient.out k) * Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n' := by
      apply Subtype.ext; simp [n', mul_assoc]
    rw [hout, step1]
  refine ⟨?_, fun g => ⟨by fun_prop, ?_⟩⟩
  · haveI : Countable (↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N)) := by
      refine Function.Surjective.countable
        (f := fun q : Q => (QuotientGroup.mk (⟨(q : G)⁻¹,
          (Q ⊔ N).inv_mem (le_sup_left (a := Q) (b := N) q.2)⟩ : ↥(Q ⊔ N))
          : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N))) ?_
      intro k
      induction k using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨n, hn, q, hq, hnq⟩ := hdec ((h : G)⁻¹) ((Q ⊔ N).inv_mem h.2)
        refine ⟨⟨q, hq⟩, ?_⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : (h : G) = (n * q)⁻¹ := by rw [hnq, inv_inv]
        show ((q : G)⁻¹)⁻¹ * (h : G) ∈ N
        rw [inv_inv, e, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
        exact N.inv_mem hn
    unfold supMeas; infer_instance
  · unfold supMeas
    rw [Measure.map_sum (by fun_prop : Measurable (fun x : ↥(Q ⊔ N) => g * x)).aemeasurable]
    simp_rw [step2, ← step3]
    refine Eq.trans ?_ (Measure.sum_comp_equiv (MulAction.toPerm g : Equiv.Perm (↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N))) (fun k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N) => νN.map
      (fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * Quotient.out k)))
    congr 1

end GlobalTheory.SupMeas
