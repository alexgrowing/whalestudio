import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj.IopRepr

theorem mk_eq_iff {V : Type*} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) (a b : A₂) :
    (QuotientAddGroup.mk a : A₂ ⧸ A₁.addSubgroupOf A₂) = QuotientAddGroup.mk b ↔
      (a : V) - (b : V) ∈ A₁ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem iop_eq_sum (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hF : RepInd D T A₁ A₂ F) {n : ℕ} (x : Fin n → A₂)
    (hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂))) :
    Iop D T A₁ A₂ F =
      (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) := by
  let e := Equiv.ofBijective _ hx
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofEquiv _ e
  have hn : (A₁.addSubgroupOf A₂).index = n := by
    rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  funext z
  unfold Iop
  rw [hn, finsum_eq_sum_of_fintype, ← e.sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((Quotient.out (e i) : A₂) : VC D N N') - x i ∈ A₁ := by
    rw [← mk_eq_iff]
    exact Quotient.out_eq (e i)
  exact congrFun (hF _ (Quotient.out (e i) : A₂).2 _ (x i).2 h) z

theorem iop_pair : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  intro D T T' N N' A₁ A₂ A₁' A₂' F F' R hfin hF hF' h1 h2 h3
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (A₂ ⧸ A₁.addSubgroupOf A₂)
  let x : Fin n → A₂ := fun i => Quotient.out (e.symm i)
  have hxe : ∀ i, (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂) = e.symm i :=
    fun i => Quotient.out_eq _
  have hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
    have : (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) = e.symm :=
      funext hxe
    rw [this]; exact e.symm.bijective
  choose y hy hR using fun i => h1 (x i) (x i).2
  let x' : Fin n → A₂' := fun i => ⟨y i, hy i⟩
  have hx' : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x' i) : A₂' ⧸ A₁'.addSubgroupOf A₂')) := by
    constructor
    · intro i j hij
      apply hx.1
      have := (mk_eq_iff _ _ _ _).1 hij
      exact (mk_eq_iff _ _ _ _).2 ((h3 _ _ _ _ (hR i) (hR j)).2 this)
    · intro q
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨a, ha, hab⟩ := h2 b b.2
      obtain ⟨i, hi⟩ := hx.2 (QuotientAddGroup.mk ⟨a, ha⟩)
      refine ⟨i, (mk_eq_iff _ _ _ _).2 ?_⟩
      exact (h3 _ _ _ _ (hR i) hab).1 ((mk_eq_iff _ _ _ _).1 hi)
  exact ⟨n, fun i => x i, y, fun i => ⟨(x i).2, hy i, hR i⟩,
    iop_eq_sum D T A₁ A₂ F hF x hx, iop_eq_sum D T' A₁' A₂' F' hF' x' hx'⟩

end GlobalTheory.ThetaConj.IopRepr
