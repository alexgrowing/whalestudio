import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevC

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Rename₂

variable {R σ τ M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

theorem isWH_rename (g : σ → τ) (w1 : σ → M) (w2 : τ → N) (L : M →+ N) (hL : ∀ x, w2 (g x) = L (w1 x))
    (f : MvPolynomial σ R) (μ : M) (hf : IsWeightedHomogeneous w1 f μ) :
    IsWeightedHomogeneous w2 (rename g f) (L μ) := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [← hf (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul])]
  simp only [Finsupp.sum, map_sum, map_nsmul, hL]

theorem isWH_prod {ι : Type*} (s : Finset ι) (w : σ → M) (φ : ι → MvPolynomial σ R) (n : ι → M)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := IsWeightedHomogeneous.prod s φ n h

end Rename₂

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def om (x : Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  fun y => if y = (x.1, x.2.2.1) then 1 else 0

def atV (v : Fin P.nV) : (Fin (P.m + 1) → ℕ) →+ (Fin P.nV × Fin (P.m + 1) → ℕ) where
  toFun μ := fun y => if y.1 = v then μ y.2 else 0
  map_zero' := by funext y; simp
  map_add' a b := by funext y; by_cases h : y.1 = v <;> simp [h]

theorem emb_isWH (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : Fin (P.m + 1) → ℕ) (hf : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) f μ) :
    IsWeightedHomogeneous (om P) (P.vEmb v (blockEmb Kf s f)) (atV P v μ) := by
  simp only [blockEmb, Places.vEmb]
  rw [rename_rename]
  refine isWH_rename _ (rowW (P.m + 1) (P.m + 1)) (om P) (atV P v) ?_ f μ hf
  intro x
  funext y
  obtain ⟨y1, y2⟩ := y
  simp only [om, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rowW, Pi.single_apply,
    Prod.mk.injEq]
  by_cases h1 : y1 = v
  · subst h1
    simp
  · simp [h1]

def wtOf (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  ∑ v, ∑ s, atV P v (μ v s)

theorem prodF_isWH (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ)
    (h : ∀ v s, IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (F v s) (μ v s)) :
    IsWeightedHomogeneous (om P) (prodF P F) (wtOf P μ) := by
  simp only [prodF, wtOf]
  apply isWH_prod
  intro v _
  rw [map_prod]
  apply isWH_prod
  intro s _
  exact emb_isWH P v s (F v s) (μ v s) (h v s)

theorem wtOf_apply (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) (v : Fin P.nV) (a : Fin (P.m + 1)) :
    wtOf P μ (v, a) = ∑ s, μ v s a := by
  simp only [wtOf, Finset.sum_apply, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem eq_of_dom {S : Type*} [Fintype S] {k : ℕ} (μ ν : S → Fin k → ℕ)
    (hdom : ∀ s (c : ℕ), (∑ a : Fin k with a.val < c, μ s a) ≤ ∑ a : Fin k with a.val < c, ν s a)
    (hsum : ∀ a, ∑ s, μ s a = ∑ s, ν s a) : μ = ν := by
  have hpart : ∀ s c, (∑ a : Fin k with a.val < c, μ s a) = ∑ a : Fin k with a.val < c, ν s a := by
    intro s c
    have htot : ∑ s, (∑ a : Fin k with a.val < c, μ s a) = ∑ s, ∑ a : Fin k with a.val < c, ν s a := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => hsum a
    exact (Finset.sum_eq_sum_iff_of_le (fun s _ => hdom s c)).1 htot s (Finset.mem_univ s)
  funext s a
  have hs : (Finset.univ.filter fun b : Fin k => b.val < a.val + 1) =
      insert a (Finset.univ.filter fun b : Fin k => b.val < a.val) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hsplit : ∀ f : Fin k → ℕ,
      (∑ b : Fin k with b.val < a.val + 1, f b) = (∑ b : Fin k with b.val < a.val, f b) + f a := by
    intro f
    rw [hs, Finset.sum_insert (by simp), add_comm]
  have h1 := hpart s (a.val + 1)
  rw [hsplit (μ s), hsplit (ν s), hpart s a.val] at h1
  exact Nat.add_left_cancel h1

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective

theorem bV_ne (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) : bV P v s i ≠ 0 := by
  unfold bV
  generalize_proofs hh
  intro h0
  have h1 := (hh.choose_spec.2 i).2.1
  rw [h0, MonomialOrder.leadingCoeff_zero] at h1
  exact zero_ne_one h1

theorem bV_dom (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (c : ℕ) :
    (∑ a : Fin (P.m + 1) with a.val < c, rowWt i.1 a) ≤ ∑ a : Fin (P.m + 1) with a.val < c, nuV P v s a := by
  obtain ⟨_, _, hb⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis Kf (P.m + 1) (P.m + 1) (nuV P v s)
  exact hb i c

theorem bV_top (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (h : rowWt i.1 = nuV P v s) :
    ∃ c : Kf, bV P v s i = c • hw Kf le_rfl (nuV P v s) := by
  have hanti : Antitone (nuV P v s) := by
    unfold nuV
    exact Formalism.MainNotions.G.LatticeSystems.kp_nuOf_antitone _ (Formalism.MainNotions.G.LatticeSystems.kp_lamAt_antitone _ (P.dom v) s)
  unfold bV
  generalize_proofs hh
  obtain ⟨⟨_, hspan, hhom⟩, _⟩ := hh.choose_spec
  have hmem : hh.choose i ∈ dualWeyl Kf (P.m + 1) (P.m + 1) (nuV P v s) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hwt : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i)
      (rowNu (r := P.m + 1) (nuV P v s)) := by
    have e : rowNu (r := P.m + 1) (nuV P v s) = nuV P v s := by
      funext a
      simp [rowNu, a.isLt]
    have h2 : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i) (rowWt i.1) := hhom i
    rw [h] at h2
    rw [e]
    exact h2
  exact ⟨_, Formalism.L2.G.Model.sw_line Kf le_rfl (nuV P v s) hanti _ hmem hwt⟩

theorem prodF_smul (c : ∀ v, Fin (P.n' v) → Kf) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    prodF P (fun v s => c v s • F v s) = (∏ v, ∏ s, c v s) • prodF P F := by
  simp only [prodF, smul_eq_C_mul, map_mul, Finset.prod_mul_distrib, map_prod]
  simp [Places.vEmb, blockEmb, rename_C, ← map_prod]

abbrev LamTot : Fin P.nV × Fin (P.m + 1) → ℕ := wtOf P (nuV P)

theorem mem_line (e : P.Xsp) (he : e ∈ Submodule.span Kf (Set.range (BI P)))
    (hwt : IsWeightedHomogeneous (om P) e (LamTot P)) : ∃ c : Kf, e = c • EV P := by
  classical
  have hBI : ∀ I, BI P I = prodF P (fun v s => bV P v s (I v s)) := fun I => rfl
  have hEV : EV P = prodF P (fun v s => hw Kf le_rfl (nuV P v s)) := rfl
  have hwtI : ∀ I, IsWeightedHomogeneous (om P) (BI P I) (wtOf P (fun v s => rowWt (I v s).1)) := by
    intro I
    rw [hBI]
    apply prodF_isWH
    intro v s
    show IsWeightedHomogeneous _ (bV P v s (I v s)) (rowWt (I v s).1)
    unfold bV
    generalize_proofs hh
    exact hh.choose_spec.1.2.2 (I v s)
  have htop : ∀ I, wtOf P (fun v s => rowWt (I v s).1) = LamTot P →
      BI P I ∈ Submodule.span Kf {EV P} := by
    intro I hI
    have hall : ∀ v s, rowWt (I v s).1 = nuV P v s := by
      intro v
      have hv := eq_of_dom (fun s => rowWt (I v s).1) (fun s => nuV P v s)
        (fun s c => bV_dom P v s (I v s) c) (by
          intro a
          have h1 := congrFun hI (v, a)
          simp only [LamTot, wtOf_apply] at h1
          exact h1)
      exact fun s => congrFun hv s
    have hc : ∀ v s, ∃ c : Kf, bV P v s (I v s) = c • hw Kf le_rfl (nuV P v s) :=
      fun v s => bV_top P v s (I v s) (hall v s)
    choose c hc using hc
    have hF : (fun v s => bV P v s (I v s)) = (fun v s => c v s • hw Kf le_rfl (nuV P v s)) := by
      funext v s
      exact hc v s
    rw [hBI, hF, prodF_smul, ← hEV]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 he
  have hcomp : weightedHomogeneousComponent (om P) (LamTot P) e = e := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hwt), if_pos rfl]
  have hmem : e ∈ Submodule.span Kf {EV P} := by
    rw [← hcomp, ← hf, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun I _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hI : wtOf P (fun v s => rowWt (I v s).1) = LamTot P
    · have h3 := hwtI I
      rw [hI] at h3
      rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 h3), if_pos rfl]
      exact htop I hI
    · rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hwtI I)), if_neg (Ne.symm hI)]
      exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

end Formalism.BasicNotions.Examples₂.NZ
