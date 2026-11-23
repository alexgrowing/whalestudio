import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.BCRowGenMonomial

noncomputable section

namespace PI.WHw

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial

theorem highest_weight_in_closure : HWInClosedC := by
  intro r n hn ν hν M hMle hM hne
  obtain ⟨v, hvM, hv0, hkill⟩ := bC_exists_killed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hMle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv0
    rw [hc, zero_smul]
  have h1 : hw ℂ hn ν = c⁻¹ • v := by rw [hc, inv_smul_smul₀ hc0]
  rw [h1]
  exact M.smul_mem _ hvM

theorem bC_dualWeyl_le_homog (r n : ℕ) (ν : Fin n → ℕ) :
    dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
  intro f hf
  have hw : IsWeightedHomogeneous (colW r n) f ν := hf.1
  rw [mem_homogeneousSubmodule]
  intro m hm
  rw [← hw hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one, Finset.sum_apply,
    Pi.smul_apply, colW, Pi.single_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => by simp)

private theorem homogeneousSubmodule_le_span_bounded_monomials (σ : Type) [Fintype σ] (N : ℕ) :
    homogeneousSubmodule σ ℂ N ≤ Submodule.span ℂ ((fun d => (monomial d (1 : ℂ) : MvPolynomial σ ℂ)) ''
      Set.range (fun e : σ → Fin (N + 1) => Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))) := by
  intro f hf
  rw [mem_homogeneousSubmodule] at hf
  rw [f.as_sum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdeg := hf (MvPolynomial.mem_support_iff.mp hd)
  have hle : ∀ v, d v ≤ N := by
    intro v
    rw [Finsupp.weight_apply, Finsupp.sum] at hdeg
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hdeg
    by_cases hv : v ∈ d.support
    · rw [← hdeg]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hv
    · have h0 : d v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      rw [h0]
      exact Nat.zero_le _
  rw [show monomial d (coeff d f) = coeff d f • monomial d (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨fun v => ⟨d v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩, rfl⟩)
  ext v
  simp

theorem bC_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (dualWeyl ℂ r n ν) := by
  have h1 := (bC_dualWeyl_le_homog r n ν).trans (homogeneousSubmodule_le_span_bounded_monomials (Fin r × Fin n) (∑ s, ν s))
  haveI := FiniteDimensional.span_of_finite ℂ ((Set.finite_range (fun e : (Fin r × Fin n) → Fin ((∑ s, ν s) + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))).image
      (fun d => (monomial d (1 : ℂ) : MvPolynomial (Fin r × Fin n) ℂ)))
  exact Submodule.finiteDimensional_of_le h1

private theorem fockF_eq_sum_of_support_subset_of_type {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h1 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h1, zero_mul, zero_mul]

private theorem fockF_add_left_highest_weight_irreducible {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fockF_eq_sum_of_support_subset_of_type (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fockF_eq_sum_of_support_subset_of_type f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_eq_sum_of_support_subset_of_type f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring

private theorem fockF_add_right_highest_weight_irreducible {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem bC_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (c • f) g = c * fockF f g := by
  rw [fockF_eq_sum_of_support_subset_of_type (c • f) g f.support MvPolynomial.support_smul]
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem bC_smul_right {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem closure_eq_nabla : ClosedEqNablaC := by
  intro r n hn ν hν M hMle hM hhw
  by_contra hne
  have hlt : M < dualWeyl ℂ r n ν := lt_of_le_of_ne hMle hne
  haveI := bC_fd r n ν
  haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMle
  let bM := Module.finBasis ℂ M
  let L : dualWeyl ℂ r n ν →ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) :=
    { toFun := fun g i => star (fockF ((bM i : M) : MvPolynomial (Fin r × Fin n) ℂ)
        (g : MvPolynomial (Fin r × Fin n) ℂ))
      map_add' := by
        intro g g'
        funext i
        simp [fockF_add_right_highest_weight_irreducible, star_add]
      map_smul' := by
        intro c g
        funext i
        simp [bC_smul_right, star_mul'] }
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hr1 : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ M := by
    calc Module.finrank ℂ (LinearMap.range L)
        ≤ Module.finrank ℂ (Fin (Module.finrank ℂ M) → ℂ) := Submodule.finrank_le _
      _ = Module.finrank ℂ M := by simp
  have hMW : Module.finrank ℂ M < Module.finrank ℂ (dualWeyl ℂ r n ν) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hker : 0 < Module.finrank ℂ (LinearMap.ker L) := by omega
  obtain ⟨⟨g, hgker⟩, hg0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hker
  have hperp : ∀ f ∈ M, fockF f (g : MvPolynomial (Fin r × Fin n) ℂ) = 0 := by
    let N : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ) :=
      { carrier := {f | fockF f (g : MvPolynomial (Fin r × Fin n) ℂ) = 0}
        add_mem' := by
          intro a b ha hb
          show fockF (a + b) _ = 0
          rw [fockF_add_left_highest_weight_irreducible, show fockF a _ = 0 from ha, show fockF b _ = 0 from hb, add_zero]
        zero_mem' := by
          show fockF 0 _ = 0
          simp [fockF]
        smul_mem' := by
          intro c a ha
          show fockF (c • a) _ = 0
          rw [bC_smul_left, show fockF a _ = 0 from ha, mul_zero] }
    intro f hf
    have hsp := bM.sum_repr ⟨f, hf⟩
    have hf' : f = ∑ i, (bM.repr ⟨f, hf⟩ i) • ((bM i : M) : MvPolynomial (Fin r × Fin n) ℂ) := by
      have h2 := congrArg Subtype.val hsp
      rw [Submodule.coe_sum] at h2
      simpa using h2.symm
    have hfN : f ∈ N := by
      rw [hf']
      refine N.sum_mem (fun i _ => N.smul_mem _ ?_)
      have hi := congrFun (LinearMap.mem_ker.mp hgker) i
      show fockF ((bM i : M) : MvPolynomial (Fin r × Fin n) ℂ) (g : MvPolynomial (Fin r × Fin n) ℂ) = 0
      simpa [L] using hi
    exact hfN
  let P : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ) :=
    { carrier := {h | h ∈ dualWeyl ℂ r n ν ∧ ∀ f ∈ M, fockF f h = 0}
      add_mem' := by
        intro a b ha hb
        exact ⟨(dualWeyl ℂ r n ν).add_mem ha.1 hb.1, fun f hf => by
          rw [fockF_add_right_highest_weight_irreducible, ha.2 f hf, hb.2 f hf, add_zero]⟩
      zero_mem' := ⟨(dualWeyl ℂ r n ν).zero_mem, fun f _ => by simp [fockF]⟩
      smul_mem' := by
        intro c a ha
        exact ⟨(dualWeyl ℂ r n ν).smul_mem c ha.1, fun f hf => by
          rw [bC_smul_right, ha.2 f hf, mul_zero]⟩ }
  have memP : ∀ h, h ∈ P ↔ (h ∈ dualWeyl ℂ r n ν ∧ ∀ f ∈ M, fockF f h = 0) := fun h => Iff.rfl
  have hgP : ((g : dualWeyl ℂ r n ν) : MvPolynomial (Fin r × Fin n) ℂ) ∈ P := (memP _).mpr ⟨g.2, hperp⟩
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Submodule.mem_bot] at hgP
    exact hg0 (Subtype.ext (Subtype.ext hgP))
  have hPclosed : RowDivClosed P := by
    intro a b k h hh
    have hh' := (memP h).mp hh
    refine (memP _).mpr ⟨rowDivStable ℂ r n ν a b k h hh'.1, fun f hf => ?_⟩
    rw [← lfockq_adjC b a k f h]
    exact hh'.2 _ (hM b a k f hf)
  obtain ⟨v, hvP, hv0, hkill⟩ := bC_exists_killed P hPclosed hPne
  have hvP' := (memP v).mp hvP
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v hvP'.1 hkill
  have hvM : v ∈ M := by
    rw [hc]
    exact M.smul_mem c hhw
  have h0 := hvP'.2 v hvM
  have hpos := (fockPos _ v hv0).1
  rw [h0, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end PI.WHw
