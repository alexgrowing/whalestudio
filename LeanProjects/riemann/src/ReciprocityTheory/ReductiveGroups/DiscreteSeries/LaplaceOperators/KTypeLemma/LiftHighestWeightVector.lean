import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.InnerCompactWordActionAdjoint

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.LowestWeightLiftLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem lc_adLW (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) (x : M) :
    ∀ w : List (Fin n × Fin n),
      Finsupp.linearCombination ℂ (fun w' => wordE E w' x) (adLW a b w) =
        E a b (wordE E w x) - wordE E w (E a b x) := by
  intro w
  induction w with
  | nil => simp [adLW, wordE]
  | cons p w ih =>
    obtain ⟨c, d⟩ := p
    have h1 : Finsupp.linearCombination ℂ (fun w' => wordE E w' x) ((adL a b (c, d)).mapDomain (· :: w)) =
        E a b (E c d (wordE E w x)) - E c d (E a b (wordE E w x)) := by
      rw [Finsupp.linearCombination_mapDomain]
      have hg := congrArg (fun T : Module.End ℂ M => T (wordE E w x)) (hE a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hg
      rw [hg, adL, map_sub]
      simp only [Function.comp_def, wordAction_cons]
      congr 1 <;> split_ifs with h <;> simp_all
    have h2 : Finsupp.linearCombination ℂ (fun w' => wordE E w' x) ((adLW a b w).mapDomain ((c, d) :: ·)) =
        E c d (Finsupp.linearCombination ℂ (fun w' => wordE E w' x) (adLW a b w)) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
      congr 1
    simp only [adLW, map_add]
    rw [h1, h2, ih, wordAction_cons, wordAction_cons, map_sub]
    abel

theorem contraction_compactWordAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b)
    (x : KS (n := n) V) (d : Fin n) : sT E V (Cone.compactWordAction ε E V hV a b x) d = E a b (sT E V x d) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    have key := lc_adLW E hE a b (v : M) w
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at key
    rw [Cone.compactWordAction_single, dif_pos hab, map_add, map_sum, sT_single, Pi.add_apply, Finset.sum_apply]
    simp only [map_smul, sT_single, Pi.smul_apply]
    by_cases hd : d = c
    · subst hd
      simp only [Pi.single_eq_same]
      rw [key, sub_add_cancel]
    · simp [hd]

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  have e : sA ε E V hV a b x = Cone.compactWordAction ε E V hV a b x + Cone.sC V a b x := by
    simp [Cone.compactWordAction]
  funext d
  rw [e, map_add, Pi.add_apply, contraction_compactWordAction ε E V hV hE a b hab, Cone.sT_sC, Cone.tensV_eq]

theorem sA_single' (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) +
      (if p.2 = b then Finsupp.single (p.1, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

end Alg

section IP

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ipK_sC (V : Submodule ℂ M) (a b : Fin n) (x y : KS (n := n) V) :
    Cone.ipK V (Cone.sC V a b x) y = Cone.ipK V x (Cone.sC V b a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | single q u =>
      obtain ⟨w, c⟩ := p
      obtain ⟨w', c'⟩ := q
      rw [Cone.sC_single, Cone.sC_single]
      by_cases h1 : c = b <;> by_cases h2 : c' = a <;>
        simp [h1, h2, Cone.ipK_single, Finsupp.single_apply, Prod.ext_iff]

theorem ipK_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hU : IsKUnitary ε E) {a b : Fin n} (hab : ε a = ε b)
    (x y : KS (n := n) V) : Cone.ipK V (sA ε E V hV a b x) y = Cone.ipK V x (sA ε E V hV b a y) := by
  have e : ∀ a b (z : KS (n := n) V), sA ε E V hV a b z = Cone.compactWordAction ε E V hV a b z + Cone.sC V a b z := by
    intro a b z; simp [Cone.compactWordAction]
  rw [e, e, map_add, LinearMap.add_apply, map_add, Cone.inner_compactWordAction_adjoint hV hU hab, ipK_sC]

theorem lift_highestWeightVector {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hV : IsKStableSub ε E V)
    [FiniteDimensional ℂ V] (hE : IsGlRep E)
    (hU : ∀ a b, ε a = ε b → ∀ x y : M, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ)
    (μ : Fin n → ℝ) (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) (hμ : IsKHWVec ε (tensV E) μ f) :
    ∃ u, IsKHWVec ε (sA ε E V hV) μ u ∧ sT E V u = f := by
  have hU' : IsKUnitary ε E := hU
  obtain ⟨x, rfl⟩ := sT_surj E V f hf
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have hfd : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have hS : IsKStableSub ε (sA ε E V hV) (Finsupp.supported V ℂ S) := by
    intro a b hab y hy
    rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [sA_single']
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_) ?_
    · show w'.length ≤ R
      rw [TRA.adLW_length a b _ _ hw']; exact hpS
    · rw [dif_pos hab]
      exact Finsupp.single_mem_supported ℂ _ hpS
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ (show p.1.length ≤ R from hpS)
      · exact Submodule.zero_mem _
  let cr : InnerProductSpace.Core ℂ (KS (n := n) V) :=
    { inner := fun x y => Cone.ipK V x y
      conj_inner_symm := fun x y => Cone.ipK_symm x y
      re_inner_nonneg := fun x => by
        rw [Cone.ipK_apply, map_sum]; exact sum_nonneg fun p _ => inner_self_nonneg
      add_left := fun x y z => by rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      definite := fun x hx => by
        have h1 := congrArg RCLike.re hx
        rw [Cone.ipK_apply, map_sum, map_zero,
          sum_eq_zero_iff_of_nonneg fun p _ => inner_self_nonneg] at h1
        ext1 p
        by_cases hp : p ∈ x.support
        · have h2 := h1 p hp
          rw [inner_self_eq_norm_sq] at h2
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
        · exact Finsupp.notMem_support_iff.mp hp }
  let _ : NormedAddCommGroup (KS (n := n) V) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ cr
  let _ : InnerProductSpace ℂ (KS (n := n) V) := InnerProductSpace.ofCore cr.toCore
  obtain ⟨u, -, -, h1, h2⟩ := lift_khw (ε := ε) (A := sA ε E V hV) (μ := μ)
    (B := tensV E) (fun a b hab x y => ipK_sA ε E V hV hU' hab x y) (sT E V)
    (fun a b hab x => sT_sA ε E V hV hE a b hab x) hfd hS (x₀ := x)
    (fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp) hμ
  exact ⟨u, h1, h2⟩

end IP

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.LowestWeightLiftLemmas
