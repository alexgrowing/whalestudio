import Formalism.PieriBlockIdeals.StatementLPR
import Formalism.PieriBlockIdeals.PieriColumnMinors.PieriGenerated
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero

open MvPolynomial

namespace Formalism.CohomologicalDescent.LPR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample Formalism.CohomologicalDescent.LP Formalism.CohomologicalDescent.LR

theorem lpr_inv {K A : Type*} [Field K] [AddCommGroup A] [Module K A] (f : Module.End K A) (p : Submodule K A)
    (hp : ∀ x ∈ p, f x ∈ p) (s : Finset K) :
    ∀ x : K → A, (∀ μ ∈ s, f (x μ) = μ • x μ) → ∑ μ ∈ s, x μ ∈ p → ∀ μ ∈ s, x μ ∈ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x _ _ μ hμ
    simp at hμ
  | insert a s ha ih =>
    intro x hx hsum
    have hxa : f (x a) = a • x a := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ μ ∈ s, f (x μ) = μ • x μ := fun μ hμ => hx μ (Finset.mem_insert_of_mem hμ)
    rw [Finset.sum_insert ha] at hsum

    have h1 : f (x a + ∑ μ ∈ s, x μ) - a • (x a + ∑ μ ∈ s, x μ) ∈ p :=
      p.sub_mem (hp _ hsum) (p.smul_mem a hsum)
    have e : f (x a + ∑ μ ∈ s, x μ) - a • (x a + ∑ μ ∈ s, x μ) = ∑ μ ∈ s, (μ - a) • x μ := by
      rw [map_add, map_sum, smul_add, Finset.smul_sum, Finset.sum_congr rfl hxs, hxa]
      rw [show a • x a + ∑ μ ∈ s, μ • x μ - (a • x a + ∑ μ ∈ s, a • x μ) =
          ∑ μ ∈ s, μ • x μ - ∑ μ ∈ s, a • x μ by abel, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun μ _ => (sub_smul μ a (x μ)).symm
    rw [e] at h1
    have ih' := ih (fun μ => (μ - a) • x μ)
      (fun μ hμ => by rw [map_smul, hxs μ hμ, smul_comm]) h1
    have hs : ∀ μ ∈ s, x μ ∈ p := fun μ hμ => by
      have hμa : μ - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hμ))
      have h2 := p.smul_mem (μ - a)⁻¹ (ih' μ hμ)
      rwa [smul_smul, inv_mul_cancel₀ hμa, one_smul] at h2
    intro μ hμ
    rcases Finset.mem_insert.mp hμ with rfl | hμ
    · have h3 := p.sub_mem hsum (p.sum_mem hs)
      rwa [add_sub_cancel_right] at h3
    · exact hs μ hμ

theorem diagonal_transfer : DiagTransfer := by
  classical
  intro K M A _ _ _ _ _ i g f hi hgf hf
  rw [eq_top_iff]
  intro x _
  have hx : i x ∈ ⨆ μ : K, Module.End.eigenspace f μ := by
    rw [hf]
    exact Submodule.mem_top
  obtain ⟨c, hcmem, hcsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  have heig : ∀ μ ∈ c.support, f (c μ) = μ • c μ := fun μ _ => Module.End.mem_eigenspace_iff.mp (hcmem μ)
  have hsum : ∑ μ ∈ c.support, c μ ∈ LinearMap.range i := ⟨x, hcsum.symm⟩
  have hp : ∀ y ∈ LinearMap.range i, f y ∈ LinearMap.range i := by
    rintro _ ⟨z, rfl⟩
    exact ⟨g z, hgf z⟩

  have hin := lpr_inv f (LinearMap.range i) hp c.support c heig hsum
  choose w hw using fun μ : {μ // μ ∈ c.support} => LinearMap.mem_range.mp (hin μ.1 μ.2)
  let W : K → M := fun μ => if h : μ ∈ c.support then w ⟨μ, h⟩ else 0
  have hW : ∀ μ ∈ c.support, i (W μ) = c μ := fun μ h => by
    simp only [W, dif_pos h]
    exact hw ⟨μ, h⟩
  have hxsum : x = ∑ μ ∈ c.support, W μ := by
    apply hi
    rw [map_sum, Finset.sum_congr rfl hW]
    exact hcsum.symm
  rw [hxsum]
  refine Submodule.sum_mem _ fun μ hμ => (le_iSup (fun μ => Module.End.eigenspace g μ) μ) ?_
  rw [Module.End.mem_eigenspace_iff]
  apply hi
  rw [hgf, hW μ hμ, heig μ hμ, map_smul, hW μ hμ]

theorem irreducible_generation : IrredGen := by
  intro K N q _ _ _ _ _ _ T B hB h hh hmin S hS hhS

  have hPstab : Stab T (B.orthogonal S) := by
    intro a b y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
    intro x hx
    rw [← hB.adj b a x y]
    exact hy _ (hS b a x hx)
  by_cases hP : B.orthogonal S = ⊥
  · have hrefl : B.IsRefl := fun x y hxy => by rw [hB.symm]; exact hxy
    have hdisj : Disjoint S (B.orthogonal S) := by
      rw [Submodule.disjoint_def]
      intro x hxS hxP
      by_contra hne
      exact (hB.pos x hne).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxP) x hxS)
    have hnd := B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hdisj
    have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
    rw [hP] at hc
    exact eq_top_of_isCompl_bot hc
  · exfalso
    have hhP : h ∈ B.orthogonal S := hmin _ hPstab hP
    have h0 : B h h = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hhP) h hhS
    exact (hB.pos h hh).ne' h0

theorem euler_diagonal : EulerDiag := by
  intro r n a
  classical
  have hsum : ∀ m : Fin r × Fin n →₀ ℕ, ∑ i ∈ m.support.filter (fun i => i.1 = a), m i = ∑ s, m (a, s) := by
    intro m
    rw [Finset.sum_filter]
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun i _ hi => by
      rw [show m i = 0 from by simpa using hi]
      simp)]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have key : ∀ (m : Fin r × Fin n →₀ ℕ) (c : ℚ),
      der r n a a (monomial m c) = ((∑ s, m (a, s) : ℕ) : ℚ) • monomial m c := by
    intro m c
    unfold der
    rw [MvPolynomial.mkDerivation_monomial, Finsupp.sum]
    have hterm : ∀ i ∈ m.support, (monomial (m - Finsupp.single i 1)) ((m i : ℕ) : ℚ) •
        (if i.1 = a then (X (a, i.2) : MvPolynomial (Fin r × Fin n) ℚ) else 0) =
        if i.1 = a then monomial m ((m i : ℚ)) else 0 := by
      intro i hi
      split_ifs with h
      · rw [smul_eq_mul, show (a, i.2) = i from Prod.ext h.symm rfl, X, monomial_mul, mul_one,
          tsub_add_cancel_of_le]
        exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
      · rw [smul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← map_sum (monomial m), smul_monomial, smul_monomial,
      smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm, ← hsum m]
    push_cast
    rfl
  rw [eq_top_iff]
  intro p _
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  apply Submodule.mem_iSup_of_mem (((∑ s, m (a, s) : ℕ) : ℚ))
  rw [Module.End.mem_eigenspace_iff]
  exact key m _

theorem real_form_finite : RealFinite := by
  intro r n ν
  classical
  have hfin : Set.Finite {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν} := by
    apply Set.Finite.subset (Finset.Iic (Finsupp.equivFunOnFinite.symm (fun q : Fin r × Fin n => ν q.2))).finite_toSet
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    rw [Finset.coe_Iic, Set.mem_Iic, Finsupp.le_def]
    intro q
    have h := congrFun hd q.2
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    simp only [Finset.sum_apply, Pi.smul_apply, colW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    show d q ≤ ν q.2
    rw [← h]
    by_cases hq : q ∈ d.support
    · calc d q = (if q.2 = q.2 then d q else 0) := by simp
        _ ≤ _ := Finset.single_le_sum (f := fun i => if q.2 = i.2 then d i else 0) (fun _ _ => Nat.zero_le _) hq
    · rw [show d q = 0 from by simpa using hq]
      exact Nat.zero_le _
  have hW : weightedHomogeneousSubmodule ℚ (colW r n) ν ≤
      Submodule.span ℚ ((fun d => monomial d (1 : ℚ)) '' {d | Finsupp.weight (colW r n) d = ν}) := by
    intro p hp
    rw [mem_weightedHomogeneousSubmodule] at hp
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdS : Finsupp.weight (colW r n) d = ν := hp (mem_support_iff.1 hd)
    rw [show monomial d (coeff d p) = coeff d p • monomial d (1 : ℚ) by rw [smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hdS, rfl⟩)
  haveI : FiniteDimensional ℚ ↥(Submodule.span ℚ ((fun d => monomial d (1 : ℚ)) ''
      {d | Finsupp.weight (colW r n) d = ν})) := FiniteDimensional.span_of_finite ℚ (hfin.image _)
  have hle : dualWeyl ℚ r n ν ≤ weightedHomogeneousSubmodule ℚ (colW r n) ν := by
    unfold dualWeyl
    exact inf_le_left
  exact Submodule.finiteDimensional_of_le (hle.trans hW)

theorem real_form_modular : RealFormMod := by
  intro p q w lam2
  refine ⟨generators_satisfy_gl_relations _, ?_, ?_, ?_, ?_⟩
  · intro x y
    show formB p q w lam2 x y = formB p q w lam2 y x
    rw [formB_apply, formB_apply, fock_symm]
  · intro x hx
    show 0 < formB p q w lam2 x x
    rw [formB_apply]
    refine div_pos ((fockQPos _ ((x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ((x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)).2 ?_) (hw_norm_pos _)
    intro h0
    exact hx (Subtype.ext (Subtype.ext h0))
  · intro a b x y
    exact real_contragredient p q w lam2 (Sum.inr a) (Sum.inr b) x y
  · intro a
    refine diagonal_transfer ℚ _ _
      ((dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype ∘ₗ (rationalBlockModuleSetting p q w lam2).W.subtype)
      _ (der (p + q) (p + q) (idx p q (Sum.inr a)) (idx p q (Sum.inr a)) : Module.End ℚ (MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)) ?_ ?_ (euler_diagonal _ _ _)
    · exact (Subtype.val_injective).comp Subtype.val_injective
    · intro x; rfl

theorem real_highest_weight : RealHW := by
  intro p q w lam2 ha hb h hh
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hwNe ℚ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)
    rw [← hh, h0]; rfl
  · intro a b hab
    apply Subtype.ext; apply Subtype.ext
    show der _ _ (Fin.natAdd p a) (Fin.natAdd p b) ((h : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
    rw [hh]
    exact der_hw_raise _ _ _ (by rw [Fin.lt_def] at hab ⊢; simpa using hab)
  · intro a
    apply Subtype.ext; apply Subtype.ext
    show der _ _ (Fin.natAdd p a) (Fin.natAdd p a) ((h : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      (lam2 a : ℚ) • ((h : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    rw [hh, (der_diag_iff _ _).1 (hw_rowHom _ hanti)]
    have : LD.blockWt p q w lam2 (Fin.natAdd p a) = lam2 a := Fin.append_right _ _ a
    rw [this]

theorem real_form_generation : RealGen := by
  intro p q w lam2 ha hb S hS hall
  have : FiniteDimensional ℚ (VQ p q w lam2) := real_form_finite _ _ _
  let h : (rationalBlockModuleSetting p q w lam2).W := ⟨hwV p q w lam2 ha hb, hwV_mem p q w lam2 ha hb⟩
  obtain ⟨hne, hhw⟩ := real_highest_weight p q w lam2 ha hb h rfl
  refine irreducible_generation ℚ _ q _ _ (real_form_modular p q w lam2) h hne ?_ S hS (hall h hhw)
  intro Z hZ hZne
  have h1 := real_irreducible p q w lam2 ha hb (Z.map (rationalBlockModuleSetting p q w lam2).W.subtype) ?_ ?_ ?_ (hwV p q w lam2 ha hb) rfl
  · obtain ⟨y, hy, hyh⟩ := h1
    have : y = h := Subtype.ext hyh
    rwa [← this]
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · rintro b b' _ ⟨y, hy, rfl⟩
    exact ⟨(rationalBlockModuleSetting p q w lam2).EW b b' y, hZ b b' y hy, rfl⟩
  · intro h0
    apply hZne
    rw [eq_bot_iff]
    intro y hy
    have : ((rationalBlockModuleSetting p q w lam2).W.subtype y) ∈ Z.map (rationalBlockModuleSetting p q w lam2).W.subtype := ⟨y, hy, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this

theorem pieri_real_form : PieriReal := by
  intro p q w lam2 ha hb n
  have : FiniteDimensional ℚ (VQ p q w lam2) := real_form_finite _ _ _
  exact pieri_generated ℚ (Fin p) _ q _ _ lam2 (real_form_modular p q w lam2) (real_form_generation p q w lam2 ha hb) n

end Formalism.CohomologicalDescent.LPR
