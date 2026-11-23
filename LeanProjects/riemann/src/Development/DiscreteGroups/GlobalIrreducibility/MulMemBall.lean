import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := by
    intro a b ha hb
    simp only [cball, Set.mem_setOf_eq] at ha hb ⊢
    exact Valuation.map_add_le _ ha hb
  neg_mem' := by
    intro a ha
    simp only [cball, Set.mem_setOf_eq] at ha ⊢
    rwa [Valuation.map_neg]

theorem mem_ball {s : kˣ} {a : k} : a ∈ ball s ↔ valuation k a ≤ valuation k (s : k) := Iff.rfl

theorem ball_mono {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) {a : k} (ha : a ∈ ball s) :
    a ∈ ball t := mem_ball.2 (le_trans (mem_ball.1 ha) h)

theorem mul_mem_ball {s t : kˣ} {a b : k} (ha : a ∈ ball s) (hb : b ∈ ball t) : a * b ∈ ball (s * t) := by
  rw [mem_ball, map_mul, Units.val_mul, map_mul]
  exact mul_le_mul' ha hb

theorem isOpen_ball (s : kˣ) : IsOpen ((ball s : AddSubgroup k) : Set k) := isOpen_cball s

abbrev Q (s t : kˣ) : Type := ↥(ball t) ⧸ (ball s).addSubgroupOf (ball t)

instance finite_Q (s t : kˣ) : Finite (Q (k := k) s t) := by
  haveI : CompactSpace ↥(ball t) := isCompact_iff_compactSpace.mp (isCompact_cball t)
  refine AddSubgroup.quotient_finite_of_isOpen _ ?_
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_ball s).preimage continuous_subtype_val

noncomputable instance (s t : kˣ) : Fintype (Q (k := k) s t) := Fintype.ofFinite _

theorem out_eq_add {s t : kˣ} (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    ∃ h ∈ ball s, ((Quotient.out q : ↥(ball t)) : k) = (x : k) + h := by
  have h1 : (QuotientAddGroup.mk (Quotient.out q) : Q s t) = QuotientAddGroup.mk x := by
    rw [← hq]; exact QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq] at h1
  refine ⟨((Quotient.out q : ↥(ball t)) : k) - x, ?_, by ring⟩
  have h2 := AddSubgroup.mem_addSubgroupOf.1 (neg_mem h1)
  convert h2 using 1
  push_cast
  ring

theorem apply_out {M : Type} {s t : kˣ} (g : k → M) (hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b)
    (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    g ((Quotient.out q : ↥(ball t)) : k) = g x := by
  obtain ⟨h, hh, he⟩ := out_eq_add x q hq
  rw [he, hg _ _ hh]

theorem out_mem {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball t := (Quotient.out q).2

theorem out_zero_mem {s t : kˣ} : ((Quotient.out (0 : Q s t) : ↥(ball t)) : k) ∈ ball s := by
  obtain ⟨h, hh, he⟩ := out_eq_add (s := s) (0 : ↥(ball t)) 0 rfl
  rw [he]; simpa using hh

theorem out_mem_iff {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball s ↔ q = 0 := by
  constructor
  · intro h
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf.2 h
  · rintro rfl; exact out_zero_mem

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def avg (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (s t : kˣ) (ξ : k) : V →ₗ[ℂ] V :=
  ∑ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) • σ ((Quotient.out q : ↥(ball t)) : k)

theorem ch_add (ψ : AddChar k Circle) (a b : k) : ((ψ (a + b) : Circle) : ℂ) = (ψ a : ℂ) * (ψ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem ch_neg_mul (ψ : AddChar k Circle) (a : k) : ((ψ (-a) : Circle) : ℂ) * (ψ a : ℂ) = 1 := by
  rw [← ch_add ψ, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

section Avg

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)
include hadd

theorem comm (a b : k) : σ a * σ b = σ b * σ a := by rw [← hadd, ← hadd, add_comm]

theorem avg_comm (s t : kˣ) (ξ : k) (b : k) : avg ψ σ s t ξ * σ b = σ b * avg ψ σ s t ξ := by
  simp only [avg, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, comm σ hadd]

theorem avg_comm_avg (s t s' t' : kˣ) (ξ ξ' : k) :
    avg ψ σ s t ξ * avg ψ σ s' t' ξ' = avg ψ σ s' t' ξ' * avg ψ σ s t ξ := by
  rw [avg, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, avg_comm ψ σ hadd]

omit hadd in
theorem avg_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) (s t : kˣ) (ξ : k) {w : V} (hw : w ∈ W) :
    avg ψ σ s t ξ w ∈ W := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  exact W.sum_mem fun q _ => W.smul_mem _ (hW _ _ hw)

theorem avg_eigen {s t : kˣ} {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1) {y : V} (hy : ∀ h ∈ ball s, σ h y = y)
    {a : k} (ha : a ∈ ball t) : σ a (avg ψ σ s t ξ y) = ((ψ (ξ * a) : Circle) : ℂ) • avg ψ σ s t ξ y := by
  rw [← Module.End.mul_apply, ← avg_comm ψ σ hadd, Module.End.mul_apply]
  let g : k → V := fun b => ((ψ (-(ξ * b)) : Circle) : ℂ) • σ b y
  have hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b := by
    intro b h hh
    simp only [g, hadd, Module.End.mul_apply, hy h hh, mul_add, neg_add, ch_add ψ, hξ h hh]
    have : ((ψ (-(ξ * h)) : Circle) : ℂ) = 1 := by
      have := ch_neg_mul ψ (ξ * h); rwa [hξ h hh, Circle.coe_one, mul_one] at this
    rw [this, mul_one]
  let a' : ↥(ball t) := ⟨a, ha⟩
  have key : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) (σ a y) =
      ((ψ (ξ * a) : Circle) : ℂ) • g ((Quotient.out (q + QuotientAddGroup.mk a') : ↥(ball t)) : k) := by
    intro q
    rw [apply_out g hg (Quotient.out q + a') _ (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [g, AddSubgroup.coe_add, a', ← Module.End.mul_apply, ← hadd, smul_smul]
    congr 1
    rw [mul_add, neg_add, ch_add ψ, ← mul_assoc, mul_comm ((ψ (ξ * a) : Circle) : ℂ), mul_assoc]
    rw [mul_comm ((ψ (ξ * a) : Circle) : ℂ), ch_neg_mul, mul_one]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, key, ← Finset.smul_sum]
  congr 1
  exact (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk a' : Q s t)) (fun q => g ((Quotient.out q : ↥(ball t)) : k)))

end Avg

end DiscreteGroups.sglob.LConvGenF
