import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

section Grade

variable (R : Type) [CommRing R] {r n : ℕ}

theorem weyl_word_row_weight_sum (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ : Fin r → ℤ, IsWeightedHomogeneous (bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) μ ∧
      ∑ a, μ a = ∑ a, (Formalism.GradedWeylDivisibility.rowNu (r := r) ν a : ℤ) := by
  induction w with
  | nil =>
    refine ⟨fun i => (Formalism.GradedWeylDivisibility.rowNu (r := r) ν i : ℤ), fun m hm => ?_, rfl⟩
    have h := Formalism.GradedWeylDivisibility.hwRowWeight R r n hn ν hν hm
    rw [bwA_weight_cast, h]
  | cons x w ih =>
    obtain ⟨μ, hμ, hs⟩ := ih
    refine ⟨_, bwA_G_of_homog x.1 x.2.1 _ μ hμ x.2.2, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, bwA_del, Pi.sub_apply, Finset.sum_add_distrib, smul_eq_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self, mul_zero,
      add_zero, hs]

end Grade

section Support

variable (R : Type) [CommRing R] {r n : ℕ}

private theorem t2w_wcast_lemma (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (bwA_wZ r n) d a = (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, bwA_wZ, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply]

theorem weyl_word_homogeneous_nat (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) μ ∧
      ∑ a, μ a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  classical
  obtain ⟨μ, hμ, hs⟩ := weyl_word_row_weight_sum R hn ν hν w
  by_cases h0 : Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) = 0
  · refine ⟨fun a => Formalism.GradedWeylDivisibility.rowNu (r := r) ν a, ?_, rfl⟩
    rw [h0]
    intro d hd
    simp at hd
  · obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
    have key : ∀ d', MvPolynomial.coeff d' (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ≠ 0 →
        Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d' = Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d := by
      intro d' hd'
      funext a
      have h1 := congrFun ((hμ hd').trans (hμ hd).symm) a
      rw [t2w_wcast_lemma, t2w_wcast_lemma] at h1
      exact_mod_cast h1
    refine ⟨Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d, fun d' hd' => key d' hd', ?_⟩
    have h2 : ∀ a, μ a = (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℤ) := by
      intro a
      rw [← hμ hd, t2w_wcast_lemma]
    have h3 : ((∑ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℕ) : ℤ) =
        ((∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a : ℕ) : ℤ) := by
      push_cast
      rw [← hs]
      exact Finset.sum_congr rfl fun a _ => (h2 a).symm
    exact_mod_cast h3

theorem weyl_homogeneous_component_mem (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ, -⟩ := weyl_word_homogeneous_nat R hn ν hν w
    by_cases hm : μ = m
    · have hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m
          (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext d
        rw [MvPolynomial.coeff_weightedHomogeneousComponent]
        split_ifs with h
        · rfl
        · by_contra hc
          exact h ((hμ (Ne.symm hc)).trans hm)
      rw [hc]
      exact Submodule.subset_span ⟨w, rfl⟩
    · have hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m
          (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = 0 := by
        ext d
        rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
        split_ifs with h
        · by_contra hc
          exact hm ((hμ hc).symm.trans h)
        · rfl
      rw [hc]
      exact Submodule.zero_mem _
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem weyl_support_row_weight_sum (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    ∀ d, coeff d f ≠ 0 → ∑ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ, hs⟩ := weyl_word_homogeneous_nat R hn ν hν w
    intro d hd
    rw [hμ hd, hs]
  | zero =>
    intro d hd
    simp at hd
  | add x y _ _ hx hy =>
    intro d hd
    rw [MvPolynomial.coeff_add] at hd
    by_cases h : MvPolynomial.coeff d x = 0
    · rw [h, zero_add] at hd
      exact hy d hd
    · exact hx d h
  | smul c x _ hx =>
    intro d hd
    rw [MvPolynomial.coeff_smul] at hd
    exact hx d (fun h => hd (by rw [h, smul_zero]))

theorem weyl_support_row_weight_le (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) (d : Fin r × Fin n →₀ ℕ)
    (hd : coeff d f ≠ 0) : ∀ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  intro a
  rw [← weyl_support_row_weight_sum R hn ν hν f hf d hd]
  exact Finset.single_le_sum (f := fun a => Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem variable_le_row_weight (d : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    d v ≤ Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d v.1 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum (f := fun u => (d u • Formalism.GradedWeylDivisibility.rowW r n u) v.1)
      (fun _ _ => Nat.zero_le _) hv)
    simp [Formalism.GradedWeylDivisibility.rowW]
  · rw [Finsupp.mem_support_iff, not_not] at hv
    simp [hv]

end Support

section Pieces

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def t2wPc (m : Fin r → ℕ) : Submodule ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :=
  (weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) m).comap (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).subtype

def t2wW (r D : ℕ) : Finset (Fin r → ℕ) := Fintype.piFinset fun _ => Finset.range (D + 1)

theorem bounded_monomials_finite (K : ℕ) : ({d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ K} : Set _).Finite := by
  classical
  refine ((Fintype.piFinset fun _ : Fin r × Fin n => Finset.range (K + 1)).finite_toSet.image
    Finsupp.equivFunOnFinite.symm).subset ?_
  intro d hd
  refine ⟨⇑d, ?_, Finsupp.equivFunOnFinite_symm_coe d⟩
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  exact fun v => Nat.lt_succ_of_le (hd v)

theorem weyl_lattice_finite (hν : Antitone ν) : Module.Finite ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) := by
  classical
  have hfin := bounded_monomials_finite (r := r) (n := n) (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)
  have hT : (Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) ''
      {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a})).FG :=
    Submodule.fg_def.mpr ⟨_, hfin.image _, rfl⟩
  have hle : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν ≤ Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) ''
      {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a}) := by
    intro f hf
    rw [MvPolynomial.as_sum f]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hd' : MvPolynomial.coeff d f ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hmono : MvPolynomial.monomial d (MvPolynomial.coeff d f) =
        MvPolynomial.coeff d f • MvPolynomial.monomial d (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hmono]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ?_, rfl⟩)
    intro v
    exact (variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν f hf d hd' v.1)
  have hN : IsNoetherian ℤ _ := isNoetherian_of_fg_of_noetherian _ hT
  exact Module.Finite.iff_fg.mpr ((isNoetherian_submodule.mp hN) _ hle)

theorem weyl_lattice_internal_sum (hν : Antitone ν) :
    DirectSum.IsInternal (fun m : (t2wW r (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)) => t2wPc hn ν (m : Fin r → ℕ)) := by
  classical
  set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have key : ∀ y ∈ ⨆ (j) (_ : j ≠ i), t2wPc hn ν (j : Fin r → ℕ),
        weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ) (y : MvPolynomial _ ℤ) = 0 := by
      intro y hy
      induction hy using Submodule.iSup_induction' with
      | mem j y hy =>
        induction hy using Submodule.iSup_induction' with
        | mem hj y hy =>
          have hy' : (y : MvPolynomial (Fin r × Fin n) ℤ) ∈
              weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (j : Fin r → ℕ) := hy
          rw [weightedHomogeneousComponent_of_mem hy', if_neg]
          intro h; exact hj (Subtype.ext h.symm)
        | zero => simp
        | add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]
      | zero => simp
      | add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]
    have h1 := key x hx'
    have hx2 : (x : MvPolynomial (Fin r × Fin n) ℤ) ∈
        weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ) := hx
    rw [weightedHomogeneousComponent_of_mem hx2, if_pos rfl] at h1
    exact Subtype.ext h1
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hsum : x = ∑ m ∈ t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x := by
      ext d
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        apply h
        simp only [t2wW, Fintype.mem_piFinset, Finset.mem_range]
        intro a
        exact Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν x hx d hne a)
    have hmem : ∀ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈
        Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν := fun m => weyl_homogeneous_component_mem ℤ hn ν hν _ x hx
    have : (⟨x, hx⟩ : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) = ∑ m : t2wW r K, ⟨_, hmem m⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      show x = ∑ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x
      rw [Finset.sum_coe_sort (t2wW r K) (fun m => weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x)]
      exact hsum
    rw [this]
    refine Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m ?_
    show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈ weightedHomogeneousSubmodule ℤ _ _
    exact weightedHomogeneousComponent_mem _ _ _

end Pieces

section Perm

variable (R : Type) [CommRing R] {r n : ℕ}

def t2wPm (σ : Equiv.Perm (Fin r)) : Matrix (Fin r) (Fin r) R := Matrix.of fun x b => if b = σ x then 1 else 0

def t2wE (σ : Equiv.Perm (Fin r)) : Fin r × Fin n → Fin r × Fin n := fun v => (σ v.1, v.2)

theorem row_action_perm_eq_rename (σ : Equiv.Perm (Fin r)) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (t2wPm R σ) = MvPolynomial.rename (t2wE σ) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, MvPolynomial.rename_X, t2wPm, t2wE, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ v.1)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem swap_perm_eq_elementary_product (x y : Fin r) (hxy : x ≠ y) :
    t2wPm R (Equiv.swap x y) = (1 + Matrix.single y x 1) * (1 + Matrix.single x y (-1)) * (1 + Matrix.single y x 1) *
      (1 + Matrix.single y y (-2)) := by
  have hyx : y ≠ x := Ne.symm hxy
  simp only [add_mul, mul_add, mul_one, one_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, ne_eq, hxy, hyx, not_false_eq_true, add_zero, zero_add]
  ext i j
  simp only [t2wPm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.zero_apply, Equiv.swap_apply_def]
  by_cases hi : i = x <;> by_cases hj : j = x <;> by_cases hi' : i = y <;> by_cases hj' : j = y <;>
    simp_all [eq_comm] <;> ring_nf

private theorem t2w_pm_mul_lemma (f g : Equiv.Perm (Fin r)) :
    t2wPm R (f * g) = t2wPm R g * t2wPm R f := by
  ext i j
  simp only [t2wPm, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (g i)]
  · by_cases h : j = f (g i) <;> simp [h]
  · intro b _ hb
    simp [hb]
  · simp

theorem perm_matrix_mem_elementary_closure (σ : Equiv.Perm (Fin r)) :
    t2wPm R σ ∈ Submonoid.closure (bwA_elem R) := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · have h1 : t2wPm R (1 : Equiv.Perm (Fin r)) = 1 := by
      ext i j
      simp [t2wPm, Matrix.one_apply, @eq_comm _ j i]
    rw [h1]
    exact Submonoid.one_mem _
  · intro f x y hxy hf
    rw [t2w_pm_mul_lemma, swap_perm_eq_elementary_product R x y hxy]
    refine Submonoid.mul_mem _ hf ?_
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submonoid.subset_closure ⟨_, _, _, rfl⟩

theorem weyl_lattice_perm_stable (hn : n ≤ r) (ν : Fin n → ℕ) (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : MvPolynomial.rename (t2wE σ) f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  rw [← row_action_perm_eq_rename R σ]
  exact bwA_weyl_rowAct_closure (R := R) hn ν _ (perm_matrix_mem_elementary_closure R σ) f hf

theorem row_weight_rename_perm (σ : Equiv.Perm (Fin r)) (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) (Finsupp.mapDomain (t2wE σ) d) =
      Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d ∘ σ.symm := by
  classical
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · funext a
    simp
  · intro f g hf hg
    rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
    rfl
  · intro v k
    funext a
    simp [Finsupp.mapDomain_single, Finsupp.weight_apply, Finsupp.sum_single_index, t2wE,
      Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Equiv.symm_apply_eq]

theorem weighted_homogeneous_rename_perm (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) R) (m : Fin r → ℕ)
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f m) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (MvPolynomial.rename (t2wE σ) f) (m ∘ σ.symm) := by
  classical
  intro d hd
  have : ∃ u, Finsupp.mapDomain (t2wE σ) u = d ∧ MvPolynomial.coeff u f ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hd
    apply MvPolynomial.coeff_rename_eq_zero
    exact hcon
  obtain ⟨u, rfl, hu⟩ := this
  rw [row_weight_rename_perm, hf hu]

end Perm

section Sym

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def t2wRn (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) : t2wPc hn ν m →ₗ[ℤ] t2wPc hn ν (m ∘ σ.symm) where
  toFun x := ⟨⟨MvPolynomial.rename (t2wE σ) (x : MvPolynomial (Fin r × Fin n) ℤ),
      weyl_lattice_perm_stable ℤ hn ν σ _ (x : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).2⟩,
    (mem_weightedHomogeneousSubmodule _ _ _ _).2 (weighted_homogeneous_rename_perm ℤ σ _ m
      ((mem_weightedHomogeneousSubmodule _ _ _ _).1 x.2))⟩
  map_add' x y := by ext1; ext1; simp
  map_smul' c x := by ext1; ext1; simp

theorem rename_perm_symm_rename (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    MvPolynomial.rename (t2wE σ.symm) (MvPolynomial.rename (t2wE σ) f) = f := by
  rw [MvPolynomial.rename_rename]
  have h : (t2wE (n := n) σ.symm ∘ t2wE (n := n) σ) = id := by
    funext v
    simp [t2wE]
  rw [h]
  simp

theorem weyl_piece_rename_injective (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) : Function.Injective (t2wRn hn ν σ m) := by
  intro x y h
  have h2 := congrArg (fun z : t2wPc hn ν (m ∘ σ.symm) =>
    MvPolynomial.rename (t2wE σ.symm) ((z : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) h
  simp only [t2wRn, LinearMap.coe_mk, AddHom.coe_mk, rename_perm_symm_rename] at h2
  exact Subtype.ext (Subtype.ext h2)

theorem weyl_piece_finrank_perm (hν : Antitone ν) (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) :
    Module.finrank ℤ (t2wPc hn ν (m ∘ σ.symm)) = Module.finrank ℤ (t2wPc hn ν m) := by
  haveI := weyl_lattice_finite hn ν hν
  have h1 := LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ m)
  have h2 := LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ.symm (m ∘ σ.symm))
  have e : (m ∘ σ.symm) ∘ σ.symm.symm = m := by
    funext a
    simp
  rw [e] at h2
  exact le_antisymm h2 h1

end Sym

section Basis

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

theorem weyl_piece_eq_bot_of_large (hν : Antitone ν) (m : Fin r → ℕ) (hm : m ∉ t2wW r (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)) :
    t2wPc hn ν m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hxm : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (x : MvPolynomial (Fin r × Fin n) ℤ) m := by
    have h := hx
    simp only [t2wPc, Submodule.mem_comap, Submodule.subtype_apply,
      MvPolynomial.mem_weightedHomogeneousSubmodule] at h
    exact h
  by_contra hne
  have hne' : (x : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0 := fun h => hne (by ext1; simpa using h)
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hne'
  apply hm
  rw [← hxm hd]
  simp only [t2wW, Fintype.mem_piFinset, Finset.mem_range]
  intro a
  exact Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν _ x.2 d hd a)

theorem weyl_homogeneous_basis (hν : Antitone ν) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν)) (μ : ι → Fin r → ℕ),
      (∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n)
        ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) (μ i)) ∧
      (∀ i, ∑ a, μ i a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a) ∧
      (∀ m, (Finset.univ.filter fun i => μ i = m).card = Module.finrank ℤ (t2wPc hn ν m)) := by
  classical
  have := weyl_lattice_finite hn ν hν
  set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a with hK
  have hI := weyl_lattice_internal_sum hn ν hν
  have hfin : ∀ m : Fin r → ℕ, Module.Finite ℤ (t2wPc hn ν m) := fun m =>
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  have hfree : ∀ m : Fin r → ℕ, Module.Free ℤ (t2wPc hn ν m) := fun m =>
    Module.free_of_finite_type_torsion_free'
  have hft : ∀ m : t2wW r K, Fintype (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ))) := fun m =>
    Module.Free.ChooseBasisIndex.fintype ℤ _
  let v : ∀ m : t2wW r K, Module.Basis (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ))) ℤ
      (t2wPc hn ν (m : Fin r → ℕ)) := fun m => Module.Free.chooseBasis ℤ _
  have hhom : ∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n)
      ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) (i.1 : Fin r → ℕ) := by
    intro i
    rw [hI.collectedBasis_coe v]
    have h : (((v i.1 i.2 : t2wPc hn ν (i.1 : Fin r → ℕ)) : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)
        ∈ weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i.1 : Fin r → ℕ) := (v i.1 i.2).2
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).1 h
  refine ⟨Σ m : t2wW r K, Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ)), inferInstance,
    hI.collectedBasis v, fun i => (i.1 : Fin r → ℕ), hhom, ?_, ?_⟩
  · intro i
    have hne : ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0 := by
      intro h; exact (hI.collectedBasis v).ne_zero i (Subtype.ext h)
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.1 hne
    show ∑ a, (i.1 : Fin r → ℕ) a = _
    rw [← hhom i hd]
    exact weyl_support_row_weight_sum ℤ hn ν hν _ (hI.collectedBasis v i).2 d hd
  · intro m
    rw [Finset.card_filter, Fintype.sum_sigma]
    by_cases hm : m ∈ t2wW r K
    · rw [Finset.sum_eq_single ⟨m, hm⟩]
      · simp [Module.finrank_eq_card_chooseBasisIndex] <;> convert rfl
      · intro b _ hb
        refine Finset.sum_eq_zero fun j _ => if_neg ?_
        intro h; exact hb (Subtype.ext h)
      · simp
    · rw [weyl_piece_eq_bot_of_large hn ν hν m hm, finrank_bot]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun j _ => if_neg ?_
      intro h; exact hm (h ▸ b.2)

theorem weyl_weight_average (hν : Antitone ν) {ι : Type} [Fintype ι] (μ : ι → Fin r → ℕ)
    (hs : ∀ i, ∑ a, μ i a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)
    (hc : ∀ m, (Finset.univ.filter fun i => μ i = m).card = Module.finrank ℤ (t2wPc hn ν m)) (j : Fin r) :
    r * ∑ i, μ i j = Fintype.card ι * ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  classical
  set S := Finset.univ.image μ with hSdef
  set mult : (Fin r → ℕ) → ℕ := fun m => (Finset.univ.filter fun i => μ i = m).card with hmult
  have hsym : ∀ σ : Equiv.Perm (Fin r), ∀ w, mult (w ∘ σ) = mult w := by
    intro σ w
    simp only [hmult, hc]
    have := weyl_piece_finrank_perm hn ν hν σ.symm w
    simpa using this
  have hS : ∀ σ : Equiv.Perm (Fin r), ∀ w ∈ S, w ∘ σ ∈ S := by
    intro σ w hw
    have hpos : 0 < mult w := by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
      exact Finset.card_pos.2 ⟨i, by simp⟩
    rw [← hsym σ w] at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
  have hsum : ∀ w ∈ S, ∑ a, w a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
    intro w hw; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw; exact hs i
  have key := Formalism.HermitianLattices.LocalLatticeBases.length_average_bound r _ S mult hS hsym hsum j
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), μ i ∈ S := fun i _ => Finset.mem_image_of_mem μ (Finset.mem_univ i)
  have h1 : ∑ w ∈ S, mult w * w j = ∑ i, μ i j := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => w j) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, smul_eq_mul]
  have h2 : ∑ w ∈ S, mult w = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
  rw [← h1, key, h2, mul_comm]

end Basis

section abelian₂

open Formalism.BasicNotions

theorem dominant_natWeight_antitone {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  simp only [Formalism.BasicNotions.DomWeight.natW]
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem rowNu_self_alt {N : ℕ} (ν : Fin N → ℕ) (a : Fin N) : Formalism.GradedWeylDivisibility.rowNu (r := N) ν a = ν a := by
  unfold Formalism.GradedWeylDivisibility.rowNu
  rw [dif_pos a.isLt]

theorem dominant_natWeight_sum {N : ℕ} (lam : DomWeight N) :
    ((∑ a, lam.natW a : ℕ) : ℤ) = ∑ a, lam.w a - N * lam.detShift := by
  have h : ∀ a, ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.detShift := by
    intro a
    simp only [Formalism.BasicNotions.DomWeight.natW]
    apply Int.toNat_of_nonneg
    simp only [Formalism.BasicNotions.DomWeight.detShift]
    split_ifs with hN
    · have ha := a.isLt
      have hle : a ≤ ⟨N - 1, by omega⟩ := by
        show (a : ℕ) ≤ N - 1
        omega
      linarith [lam.anti hle]
    · exact absurd (lt_of_le_of_lt (Nat.zero_le _) a.isLt) hN
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib]
  simp

theorem dominant_weight_basis_row_weights {N : ℕ} (lam : DomWeight N) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (delSq ℤ N lam)) (μ : ι → Fin N → ℕ),
      (∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) ((b i : delSq ℤ N lam) : MvPolynomial (Fin N × Fin N) ℤ) (μ i)) ∧
      (∀ i, ∑ a, μ i a = ∑ a, lam.natW a) ∧
      ∀ j, (N : ℚ) * ∑ i, ((μ i j : ℚ) + lam.detShift) = (Fintype.card ι : ℚ) * ((∑ a, lam.w a : ℤ) : ℚ) := by
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis le_rfl lam.natW (dominant_natWeight_antitone lam)
  refine ⟨ι, hι, b, μ, hh, fun i => by rw [hs i]; simp [rowNu_self_alt], fun j => ?_⟩
  have havg := weyl_weight_average le_rfl lam.natW (dominant_natWeight_antitone lam) μ hs hc j
  simp only [rowNu_self_alt] at havg
  have hq : ((N * ∑ i, μ i j : ℕ) : ℚ) = ((Fintype.card ι * ∑ a, lam.natW a : ℕ) : ℚ) := by rw [havg]
  have hsum := dominant_natWeight_sum lam
  have hsumQ : ((∑ a, lam.natW a : ℕ) : ℚ) = ((∑ a, lam.w a : ℤ) : ℚ) - N * lam.detShift := by
    exact_mod_cast hsum
  push_cast at hq hsumQ ⊢
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, hq, hsumQ]
  ring

end abelian₂

section Diag

variable (R : Type) [CommRing R] {r n : ℕ}

theorem prod_rows_pow_row_weight (d : Fin r → R) (m : Fin r × Fin n →₀ ℕ) :
    ∏ v ∈ m.support, d v.1 ^ m v = ∏ a, d a ^ (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m a) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Formalism.GradedWeylDivisibility.rowW, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1 (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp

theorem row_action_diagonal_homogeneous (d : Fin r → R) (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    Formalism.GradedWeylDivisibility.rowAct R (Matrix.diagonal d) f = (∏ a, d a ^ μ a) • f := by
  classical
  have hg : ∀ v : Fin r × Fin n, (∑ b : Fin r, MvPolynomial.C (Matrix.diagonal d v.1 b) *
      MvPolynomial.X (b, v.2) : MvPolynomial (Fin r × Fin n) R) = MvPolynomial.C (d v.1) * MvPolynomial.X v := by
    intro v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m = μ := hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_monomial, hg, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [prod_rows_pow_row_weight R d m, hw, MvPolynomial.smul_eq_C_mul, MvPolynomial.monomial_eq,
    MvPolynomial.algebraMap_eq]
  simp only [Finsupp.prod]
  ring

end Diag

section LenBasis

theorem length_quotient_dvr_basis (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : Irreducible ϖ)
    {M : Type} [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) (a : ι → ℕ) :
    Module.length R (M ⧸ Submodule.span R (Set.range fun i => ϖ ^ a i • b i)) = ((∑ i, a i : ℕ) : ℕ∞) := by
  classical
  set P : Submodule R (ι → R) := Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ a i}) with hP
  have hmap : (Submodule.span R (Set.range fun i => ϖ ^ a i • b i)).map b.equivFun.toLinearMap = P := by
    rw [Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      intro j _
      simp only [LinearEquiv.coe_coe, map_smul, Module.Basis.equivFun_self, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · subst h; rw [mul_one]; exact Ideal.mem_span_singleton_self _
      · rw [mul_zero]; exact Submodule.zero_mem _
    · intro x hx
      have hx' : ∀ i, ∃ c, x i = c * ϖ ^ a i := fun i => by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hx i (Set.mem_univ i))
        exact ⟨c, hc.symm⟩
      choose c hc using hx'
      have : x = ∑ i, c i • b.equivFun (ϖ ^ a i • b i) := by
        funext j
        simp only [map_smul, Module.Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc j]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)
  have e := Submodule.Quotient.equiv _ P b.equivFun hmap
  rw [e.length_eq]
  exact Formalism.HermitianLattices.RamifiedLatticeOperators.lemmaB_length_statement R ϖ hϖ ι a

end LenBasis

section Indep

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

theorem weyl_basis_lin_indep_field (hν : Antitone ν) (K : Type) [Field K] [CharZero K] {ι : Type}
    (b : Module.Basis ι ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν)) :
    LinearIndependent K (fun i => MvPolynomial.map (Int.castRingHom K)
      ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) := by
  classical
  set Kb := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a
  set S : Set (Fin r × Fin n →₀ ℕ) := {d | ∀ v, d v ≤ Kb}
  have : Finite S := (bounded_monomials_finite Kb).to_subtype
  have hsupp : ∀ x ∈ Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν, ∀ d, d ∉ S → coeff d x = 0 := by
    intro x hx d hd
    by_contra h
    exact hd fun v => (variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν x hx d h v.1)
  let f : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν →ₗ[ℤ] (S → ℤ) :=
    LinearMap.pi fun d => (MvPolynomial.lcoeff ℤ d.1).comp (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    ext d
    by_cases hd : d ∈ S
    · have := congrFun hx ⟨d, hd⟩
      simpa [f] using this
    · simpa using hsupp x x.2 d hd
  have hv : LinearIndependent ℤ (f ∘ b) := b.linearIndependent.map' f hf
  have h2 : LinearIndependent K (fun i => algebraMap ℤ K ∘ (f ∘ b) i) :=
    linearIndependent_algebraMap_comp_iff.2 hv
  let g : MvPolynomial (Fin r × Fin n) K →ₗ[K] (S → K) := LinearMap.pi fun d => MvPolynomial.lcoeff K d.1
  refine LinearIndependent.of_comp g ?_
  convert h2 using 1
  funext i d
  simp [g, f, MvPolynomial.coeff_map]

end Indep

section Factor

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

theorem weighted_homogeneous_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPolynomial (Fin r × Fin n) R)
    (μ : Fin r → ℕ) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (MvPolynomial.map φ f) μ := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

theorem prod_update_pow_alt {R : Type} [CommRing R] (j : Fin r) (p : R) (μ : Fin r → ℕ) :
    ∏ a, (Function.update (1 : Fin r → R) j p) a ^ μ a = p ^ μ j := by
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Function.update_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem weyl_length_diagonal_uniformiser (hν : Antitone ν) (K : Type) [Field K] [CharZero K] (O : Subring K)
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (j : Fin r) (a : ℕ) :
    ∃ N : ℕ, Module.length O (bwA_span O hn ν ⧸ ((bwA_span O hn ν).map
        ((Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j ((ϖ : K) ^ a)))).toLinearMap.restrictScalars O)).comap
          (bwA_span O hn ν).subtype) = N ∧
      r * N = a * Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) * ∑ c, Formalism.GradedWeylDivisibility.rowNu (r := r) ν c := by
  classical
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis hn ν hν
  set Λ := bwA_span O hn ν with hΛ
  set e : ι → MvPolynomial (Fin r × Fin n) K := fun i =>
    MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he
  have hliK : LinearIndependent K e := weyl_basis_lin_indep_field hn ν hν K b
  have hinjO : Function.Injective fun c : O => c • (1 : K) := by
    intro x y h; simpa using h
  have hliO : LinearIndependent O e := hliK.restrict_scalars hinjO
  have hspan : Submodule.span O (Set.range e) = Λ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
    · rw [hΛ, bwA_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) := by
        have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h1
        simp only [Submodule.coe_smul] at h1
        exact h1.symm
      rw [hxx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :
          MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bS : Module.Basis ι O (Submodule.span O (Set.range e)) := Module.Basis.span hliO
  let bΛ : Module.Basis ι O Λ := bS.map (LinearEquiv.ofEq _ _ hspan)
  have hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i := by
    intro i
    simp [bΛ, bS, Module.Basis.span_apply]
  set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j ((ϖ : K) ^ a)))).toLinearMap.restrictScalars O
  have hφe : ∀ i, φ (e i) = (ϖ ^ (a * μ i j) : O) • e i := by
    intro i
    have hom := weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)
    show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _
    rw [row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt, ← pow_mul]
    rw [Subring.smul_def]
    simp
  set W : Submodule O Λ := Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i) with hW
  have hmapW : W.map Λ.subtype = Λ.map φ := by
    rw [hW, Submodule.map_span]
    conv_rhs => rw [← hspan, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
  have hcomap : (Λ.map φ).comap Λ.subtype = W := by
    rw [← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]
  refine ⟨∑ i, a * μ i j, ?_, ?_⟩
  · rw [hcomap, hW]
    exact length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)
  · have havg := weyl_weight_average hn ν hν μ hs hc j
    rw [Module.finrank_eq_card_basis b, ← Finset.mul_sum]
    calc r * (a * ∑ i, μ i j) = a * (r * ∑ i, μ i j) := by ring
      _ = _ := by rw [havg]; ring

theorem weyl_length_diagonal_unit_uniformiser (hν : Antitone ν) (K : Type) [Field K] [CharZero K] (O : Subring K)
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (j : Fin r) (a : ℕ) :
    ∃ N : ℕ, Module.length O (bwA_span O hn ν ⧸ ((bwA_span O hn ν).map
        ((Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j (((u : O) * ϖ ^ a : O) : K)))).toLinearMap.restrictScalars O)).comap
          (bwA_span O hn ν).subtype) = N ∧
      r * N = a * Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) * ∑ c, Formalism.GradedWeylDivisibility.rowNu (r := r) ν c := by
  classical
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis hn ν hν
  set Λ := bwA_span O hn ν with hΛ
  set e : ι → MvPolynomial (Fin r × Fin n) K := fun i =>
    MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he
  have hliK : LinearIndependent K e := weyl_basis_lin_indep_field hn ν hν K b
  have hinjO : Function.Injective fun c : O => c • (1 : K) := by
    intro x y h; simpa using h
  have hliO : LinearIndependent O e := hliK.restrict_scalars hinjO
  have hspan : Submodule.span O (Set.range e) = Λ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
    · rw [hΛ, bwA_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) := by
        have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h1
        simp only [Submodule.coe_smul] at h1
        exact h1.symm
      rw [hxx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :
          MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bS : Module.Basis ι O (Submodule.span O (Set.range e)) := Module.Basis.span hliO
  let bΛ : Module.Basis ι O Λ := bS.map (LinearEquiv.ofEq _ _ hspan)
  have hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i := by
    intro i
    simp [bΛ, bS, Module.Basis.span_apply]
  set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j (((u : O) * ϖ ^ a : O) : K)))).toLinearMap.restrictScalars O
  have hφe : ∀ i, φ (e i) = (((u : O) * ϖ ^ a) ^ μ i j : O) • e i := by
    intro i
    have hom := weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)
    show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _
    rw [row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt]
    rw [Subring.smul_def]
    simp
  set W : Submodule O Λ := Submodule.span O (Set.range fun i => ((u : O) * ϖ ^ a) ^ μ i j • bΛ i) with hW
  have hWeq : W = Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i) := by
    rw [hW]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : ((u : O) * ϖ ^ a) ^ μ i j • bΛ i = ((u : O) ^ μ i j) • (ϖ ^ (a * μ i j) • bΛ i) := by
        rw [smul_smul, mul_pow, ← pow_mul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : ϖ ^ (a * μ i j) • bΛ i = (((u⁻¹ : Oˣ) : O) ^ μ i j) • (((u : O) * ϖ ^ a) ^ μ i j • bΛ i) := by
        rw [smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul, ← pow_mul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmapW : W.map Λ.subtype = Λ.map φ := by
    rw [hW, Submodule.map_span]
    conv_rhs => rw [← hspan, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
  have hcomap : (Λ.map φ).comap Λ.subtype = W := by
    rw [← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]
  refine ⟨∑ i, a * μ i j, ?_, ?_⟩
  · rw [hcomap, hWeq]
    exact length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)
  · have havg := weyl_weight_average hn ν hν μ hs hc j
    rw [Module.finrank_eq_card_basis b, ← Finset.mul_sum]
    calc r * (a * ∑ i, μ i j) = a * (r * ∑ i, μ i j) := by ring
      _ = _ := by rw [havg]; ring

end Factor

section FnOf

open Formalism.L2.Forms

variable {ι : Type} [Fintype ι] {n : ℕ}

def t2wDet : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ : ι, (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

theorem eval_det_product (pt : ι × Fin n × Fin n → ℂ) :
    MvPolynomial.eval pt (t2wDet (ι := ι) (n := n)) = ∏ τ : ι, (Matrix.of fun a b : Fin n => pt (τ, a, b)).det := by
  unfold t2wDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem polynomial_function_frames_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) : Function.Injective (fnOf G s M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro P hP
  rw [LinearMap.mem_ker] at hP
  rw [Submodule.mem_bot]
  have h1 : ∀ z : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (z τ).det) →
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => z x.1 x.2.1 x.2.2) P = 0 := by
    intro z hz
    let y : Frames G := ⟨fun τ => (M τ)⁻¹ * z τ, fun τ => by
      rw [Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 (hM τ)).mul (hz τ)⟩
    have hMy : ∀ τ, M τ * y.1 τ = z τ := by
      intro τ
      show M τ * ((M τ)⁻¹ * z τ) = z τ
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hM τ), Matrix.one_mul]
    have h := congrFun hP y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at h
    have hne : (∏ τ, (z τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hz τ).ne_zero
    exact (mul_eq_zero.1 h).resolve_left hne
  have h2 : t2wDet (ι := ι) (n := n) * P = 0 := by
    apply MvPolynomial.funext
    intro pt
    rw [map_mul, map_zero, eval_det_product]
    by_cases h : ∀ τ, (Matrix.of fun a b : Fin n => pt (τ, a, b)).det ≠ 0
    · have := h1 (fun τ => Matrix.of fun a b : Fin n => pt (τ, a, b)) (fun τ => isUnit_iff_ne_zero.2 (h τ))
      simp only [Matrix.of_apply] at this
      rw [this, mul_zero]
    · push_neg at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]
  have hD : t2wDet (ι := ι) (n := n) ≠ 0 := by
    intro h0
    have := congrArg (MvPolynomial.eval (fun x : ι × Fin n × Fin n => if x.2.1 = x.2.2 then (1 : ℂ) else 0)) h0
    rw [eval_det_product, map_zero] at this
    have hI : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0).det = 1 := by
      have : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0) = 1 := by
        ext a b; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    rw [Finset.prod_eq_one (fun τ _ => hI)] at this
    exact one_ne_zero this
  exact (mul_eq_zero.1 h2).resolve_left hD

end FnOf

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
