import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

open GlobalTheory.RestrMeas

theorem finsum_doubleCoset_restr {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X]
    [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (T : Subgroup X)
    (Tv : ∀ v, Subgroup (Y v)) (hT : ∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) (F : X → ℂ) (Fv : ∀ v, Y v → ℂ)
    (hF : ∀ x, F x = ∏ᶠ v, Fv v (pf v x))
    (hinv : ∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y)
    (hfin : ∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite)
    (hev : ∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) =
      ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  have memKg : ∀ x, x ∈ Kg ↔ ∀ v, pf v x ∈ K v := fun x => by simp [hKg, Subgroup.mem_iInf]
  obtain ⟨S0, hS0⟩ := exists_finset_of_eventually hev

  have L0 : ∀ v (z₁ z₂ : Y v), DoubleCoset.mk (Tv v) (K v) z₁ = DoubleCoset.mk (Tv v) (K v) z₂ →
      Fv v z₁ = Fv v z₂ := fun v z₁ z₂ h => by
    obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h
    rw [e, hinv v t ht z₁ k hk]
  have L0' : ∀ v (z : Y v), Fv v (Quotient.out (DoubleCoset.mk (Tv v) (K v) z)) = Fv v z := fun v z =>
    L0 v _ _ (DoubleCoset.out_eq' _ _ _)

  have L1 : ∀ x y, DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y → ∀ v,
      DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y) := fun x y h v => by
    obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h
    exact (DoubleCoset.eq _ _ _ _).2 ⟨pf v t, (hT t).1 ht v, pf v k, (memKg k).1 hk v, by rw [e]; simp⟩

  have L1' : ∀ x y, (∀ v, DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y)) →
      DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y := fun x y h => by
    have h' := fun v => (DoubleCoset.eq _ _ _ _).1 (h v)
    choose t ht k hk e using h'
    let t' : ∀ v, Y v := fun v => if pf v x ∈ K v ∧ pf v y ∈ K v then 1 else t v
    have ht'T : ∀ v, t' v ∈ Tv v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c]; exact one_mem _
      · simp only [t', if_neg c]; exact ht v
    have ht'K : ∀ v, (pf v x)⁻¹ * (t' v)⁻¹ * pf v y ∈ K v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c, inv_one, mul_one]; exact mul_mem (inv_mem c.1) c.2
      · simp only [t', if_neg c]; rw [e v]; simpa [mul_assoc] using hk v
    have hev' : ∀ᶠ v in cofinite, t' v ∈ K v := ((hX.eventually_mem x).and (hX.eventually_mem y)).mono
      fun v c => by simp only [t', if_pos c]; exact one_mem _
    obtain ⟨g, -, hg⟩ := hX.exists_eq isEmptyElim t' hev'
    refine (DoubleCoset.eq _ _ _ _).2 ⟨g, (hT g).2 fun v => hg v ▸ ht'T v, x⁻¹ * g⁻¹ * y,
      (memKg _).2 fun v => by simpa [hg v] using ht'K v, by group⟩

  have ProjectionSandwichLength : ∀ x, (Function.mulSupport fun v => Fv v (pf v x)).Finite := fun x => by
    have hE : ∀ᶠ v in cofinite, pf v x ∈ K v ∧ v ∉ S0 :=
      (hX.eventually_mem x).and (eventually_of_finset S0 fun v hv => hv)
    refine (eventually_cofinite.1 hE).subset fun v hv c => hv ?_
    show Fv v (pf v x) = 1
    have := hinv v 1 (one_mem _) 1 (pf v x) c.1
    rw [one_mul, one_mul] at this
    rw [this, (hS0 v c.2).1]
  have L2 : ∀ x, F x ≠ 0 → ∀ v, Fv v (pf v x) ≠ 0 := fun x hx v h0 =>
    hx (by rw [hF]; exact finprod_eq_zero _ v h0 (ProjectionSandwichLength x))
  have KernelIndexFullLattice : ∀ v ∉ S0, ∀ y : Y v, Fv v y ≠ 0 → DoubleCoset.mk (Tv v) (K v) y = DoubleCoset.mk (Tv v) (K v) 1 ∧
      Fv v y = 1 := fun v hv y hy => by
    obtain ⟨t, ht, k, hk, e⟩ := (hS0 v hv).2 y hy
    refine ⟨((DoubleCoset.eq _ _ _ _).2 ⟨t, ht, k, hk, by rw [e, mul_one]⟩).symm, ?_⟩
    rw [e, ← (hS0 v hv).1, ← hinv v t ht 1 k hk, mul_one]
  have DegreeKernelLowerBound : ∀ x, (∀ v ∉ S0, Fv v (pf v x) ≠ 0) → F x = ∏ v ∈ S0, Fv v (pf v x) := fun x h => by
    rw [hF]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hS
    exact hv (KernelIndexFullLattice v hS _ (h v hS)).2

  have L3 : ∀ v ∉ S0, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) = 1 :=
    fun v hv => by
    rw [finsum_eq_single _ (DoubleCoset.mk (Tv v) (K v) 1), L0', (hS0 v hv).1]
    intro q hq
    by_contra h0
    apply hq
    rw [← DoubleCoset.out_eq' _ _ q]
    exact (KernelIndexFullLattice v hv _ h0).1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S0) fun v hv => by_contra fun h => hv (L3 v h),
    ← Finset.prod_coe_sort S0]
  let Q := fun v : S0 => DoubleCoset.Quotient (Tv v.1 : Set (Y v.1)) (K v.1 : Set (Y v.1))
  let Φ : DoubleCoset.Quotient (T : Set X) (Kg : Set X) → ∀ v : S0, Q v :=
    fun q v => DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 (Quotient.out q))
  let H : (∀ v : S0, Q v) → ℂ := fun b => ∏ v : S0, Fv v.1 (Quotient.out (b v))
  have hH : ∀ b, H b ≠ 0 → ∀ v : S0, Fv v.1 (Quotient.out (b v)) ≠ 0 := fun b hb v =>
    Finset.prod_ne_zero_iff.1 hb v (Finset.mem_univ _)
  have hval : ∀ q, F (Quotient.out q) ≠ 0 → F (Quotient.out q) = H (Φ q) := fun q hq => by
    rw [DegreeKernelLowerBound _ fun v _ => L2 _ hq v, ← Finset.prod_coe_sort S0]
    exact Finset.prod_congr rfl fun v _ => (L0' v.1 _).symm
  have hbij : Set.BijOn Φ (Function.support fun q => F (Quotient.out q)) (Function.support H) := by
    refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ e => ?_, fun b hb => ?_⟩
    · show H (Φ q) ≠ 0
      rw [← hval q hq]; exact hq
    · rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂]
      refine L1' _ _ fun v => ?_
      by_cases hv : v ∈ S0
      · exact congrFun e ⟨v, hv⟩
      · rw [(KernelIndexFullLattice v hv _ (L2 _ h₁ v)).1, (KernelIndexFullLattice v hv _ (L2 _ h₂ v)).1]
    · have hb' := hH b hb
      let y : ∀ v, Y v := fun v => if h : v ∈ S0 then Quotient.out (b ⟨v, h⟩) else 1
      obtain ⟨x, -, hx⟩ := hX.exists_eq isEmptyElim y
        (eventually_of_finset S0 fun v hv => by simp only [y, dif_neg hv]; exact one_mem _)
      have hq := L1 _ _ (DoubleCoset.out_eq' T Kg (DoubleCoset.mk T Kg x))
      have hxS : ∀ v : S0, DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 x) = b v := fun v => by
        rw [hx, show y v.1 = Quotient.out (b v) by simp [y, v.2]]
        exact DoubleCoset.out_eq' _ _ _
      have hΦ : Φ (DoubleCoset.mk T Kg x) = b := funext fun v => (hq v.1).trans (hxS v)
      refine ⟨DoubleCoset.mk T Kg x, ?_, hΦ⟩
      show F _ ≠ 0
      have hne : ∀ v ∉ S0, Fv v (pf v (Quotient.out (DoubleCoset.mk T Kg x))) ≠ 0 := fun v hv => by
        rw [L0 v _ _ (hq v), hx]; simp only [y, dif_neg hv, (hS0 v hv).1]; exact one_ne_zero
      rw [DegreeKernelLowerBound _ hne, Finset.prod_ne_zero_iff]
      intro v hv
      rw [L0 v _ _ (hq v), hx]
      simp only [y, dif_pos hv]
      exact hb' ⟨v, hv⟩
  refine ((finsum_mem_support _).symm.trans ((finsum_mem_eq_of_bijOn Φ hbij fun q hq => hval q hq).trans
    (finsum_mem_support H))).trans ?_
  have hsum : ∀ v : S0, ∑ᶠ q : Q v, Fv v.1 (Quotient.out q) =
      ∑ q ∈ (hfin v.1).toFinset, Fv v.1 (Quotient.out q) := fun v =>
    finsum_eq_sum_of_support_subset _ fun q hq => (hfin v.1).mem_toFinset.2 hq
  rw [Finset.prod_congr rfl fun v _ => hsum v, Finset.prod_univ_sum]
  refine finsum_eq_sum_of_support_subset H fun b hb => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun v => by simpa using hH b hb v

end GlobalTheory.EulerAbs
