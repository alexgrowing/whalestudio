import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.InitPartZeroXMul

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset

section Lib
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem cartan_eigC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (μ : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WtSpC p LL j Cs μ) (c : Fin r) (hc : c ∈ Cs) :
    glAct p LL j c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_cartan, coeff_smul, smul_eq_mul]
  by_cases h : coeff m x = 0
  · simp [h]
  · have hm := hx (Finset.mem_coe.mpr (mem_support_iff.mpr h))
    rw [Set.mem_setOf_eq] at hm
    rw [hm c hc]

theorem comm_wtspC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ x, Q (glAct p LL j c c x) = glAct p LL j c c (Q x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, Q x ∈ WtSpC p LL j Cs μ := by
  intro x hx
  rw [WtSpC, mem_restrictSupport_iff]
  intro m hm c hc
  have h1 : glAct p LL j c c (Q x) = ((μ c : ℤ) : ℚ_[p]) • Q x := by
    rw [← hQ c hc, cartan_eigC LL j Cs μ x hx c hc, map_smul]
  have := eig_supp LL j c (μ c) (Q x) h1
  rw [mem_restrictSupport_iff] at this
  exact this hm

theorem hwc_keepC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ HWC p LL j Cs la, Q x ∈ HWC p LL j Cs la := by
  intro x hx
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨comm_wtspC LL j Cs Q (fun c hc y => hQ c hc c hc y) la x h1, fun c d hcd => ?_⟩
  rw [← hQ c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]

theorem isoC_glStableC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) (c : Fin r) (hc : c ∈ Cs)
    (d : Fin r) (hd : d ∈ Cs) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c d x ∈ IsoC p LL j Cs la := by
  intro x hx
  rw [IsoC, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c hc d hd x (hx S hS)

theorem hwc_le_isoCC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    HWC p LL j Cs la ≤ IsoC p LL j Cs la := by
  intro x hx
  rw [IsoC, Submodule.mem_sInf]
  intro S hS
  exact hS.1 hx

theorem isoC_keepC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ IsoC p LL j Cs la, Q x ∈ IsoC p LL j Cs la := by
  intro x hx
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap Q := by
    apply sInf_le
    refine ⟨fun y hy => ?_, fun c hc d hd y hy => ?_⟩
    · exact hwc_le_isoCC LL j Cs la (hwc_keepC LL j Cs la Q hQ y hy)
    · show Q (glAct p LL j c d y) ∈ IsoC p LL j Cs la
      rw [hQ c hc d hd]
      exact isoC_glStableC LL j Cs la c hc d hd _ hy
  exact hle hx

theorem typeProj_comm_isoC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ la, ∀ x ∈ IsoC p LL j Cs la, Q x ∈ IsoC p LL j Cs la) : ∀ x, P (Q x) = Q (P x) := by
  apply comm_of_stable P Q hP.1
  · intro x hx
    rw [hP.2.1] at hx ⊢
    have hle : (⨆ la ∈ T, IsoC p LL j Cs la) ≤ (⨆ la ∈ T, IsoC p LL j Cs la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro y hy
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j Cs la) la hla) (hQ la y hy)
    exact hle hx
  · intro x hx
    rw [hP.2.2] at hx ⊢
    have hle : (⨆ (la : Fin r → ℤ), ⨆ (_ : la ∉ T), IsoC p LL j Cs la) ≤
        (⨆ (la : Fin r → ℤ), ⨆ (_ : la ∉ T), IsoC p LL j Cs la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro y hy
      exact (le_iSup₂ (f := fun la (_ : la ∉ T) => IsoC p LL j Cs la) la hla) (hQ la y hy)
    exact hle hx

theorem typeProj_commC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) : ∀ x, P (Q x) = Q (P x) :=
  typeProj_comm_isoC LL j Cs T P hP Q (fun la => isoC_keepC LL j Cs la Q hQ)

theorem typeProj_glActC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (c : Fin r) (hc : c ∈ Cs) (d : Fin r) (hd : d ∈ Cs) :
    ∀ x, P (glAct p LL j c d x) = glAct p LL j c d (P x) :=
  typeProj_comm_isoC LL j Cs T P hP _ (fun la => isoC_glStableC LL j Cs la c hc d hd)

theorem typeProj_eulC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (i0 : Fin N) :
    ∀ x, P (ProjS.eulL (fun c : Fin r => (i0, c)) x) = ProjS.eulL (fun c : Fin r => (i0, c)) (P x) :=
  typeProj_commC LL j Cs T P hP _ (fun c _ d _ x => eul_glAct LL j i0 c d x)

theorem typeProj_polC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) : ∀ x ∈ Pol p r LL, P x ∈ Pol p r LL := by
  intro x hx
  rw [pol_iff_eul] at hx ⊢
  intro i
  rw [← typeProj_eulC LL j Cs T P hP i, hx i, map_smul]

theorem glAct_wtspC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, glAct p LL j c d x ∈ WtSpC p LL j Cs (shiftW μ c d) := by
  intro x hx
  refine glAct_keep LL j c d {m | ∀ e ∈ Cs, wt LL j e m = μ e}
    {m | ∀ e ∈ Cs, wt LL j e m = shiftW μ c d e} ?_ ?_ x hx
  · intro i hi hv m hm h1
    rw [Set.mem_setOf_eq] at hm ⊢
    intro e he
    rw [(wt_shift LL j c d e i hi m).1 hv h1, hm e he]
    rfl
  · intro i hi hv m hm h1
    rw [Set.mem_setOf_eq] at hm ⊢
    intro e he
    rw [(wt_shift LL j c d e i hi m).2 hv h1, hm e he]
    rfl

private theorem exists_mem_coeff_eq_prod_weight_sub_mul (LL : Letters N) (j : ℕ) (c : Fin r)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, glAct p LL j c c x ∈ S) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ S) :
    ∀ F : Finset ℤ, ∃ y ∈ S, ∀ m, coeff m y = (∏ w ∈ F, (((wt LL j c m : ℤ) : ℚ_[p]) - (w : ℚ_[p]))) * coeff m x := by
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨x, hx, fun m => by simp⟩
  | insert a F ha ih =>
    obtain ⟨y, hy, hym⟩ := ih
    refine ⟨glAct p LL j c c y - ((a : ℤ) : ℚ_[p]) • y, sub_mem (hS y hy) (Submodule.smul_mem _ _ hy), fun m => ?_⟩
    rw [coeff_sub, coeff_cartan, coeff_smul, smul_eq_mul, hym m, Finset.prod_insert ha]
    ring
private theorem compP_weight_eq_mem_of_glAct_stable (LL : Letters N) (j : ℕ) (c : Fin r)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, glAct p LL j c c x ∈ S) (k : ℤ) :
    ∀ x ∈ S, compP (fun m => wt LL j c m = k) x ∈ S := by
  classical
  intro x hx
  set F := (x.support.image (wt LL j c)).erase k with hF
  obtain ⟨y, hy, hym⟩ := exists_mem_coeff_eq_prod_weight_sub_mul LL j c S hS x hx F
  have hD : (∏ w ∈ F, ((k : ℚ_[p]) - (w : ℚ_[p]))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    rw [sub_ne_zero]
    intro h
    exact (Finset.ne_of_mem_erase hw) (by exact_mod_cast h.symm)
  have heq : compP (fun m => wt LL j c m = k) x = (∏ w ∈ F, ((k : ℚ_[p]) - (w : ℚ_[p])))⁻¹ • y := by
    ext m
    rw [coeff_compP, coeff_smul, smul_eq_mul, hym m]
    by_cases hm : coeff m x = 0
    · simp [hm]
    · split_ifs with hk
      · rw [hk, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
      · have hmem : wt LL j c m ∈ F := by
          rw [hF, Finset.mem_erase]
          exact ⟨hk, Finset.mem_image_of_mem _ (mem_support_iff.mpr hm)⟩
        rw [Finset.prod_eq_zero (f := fun w : ℤ => ((wt LL j c m : ℤ) : ℚ_[p]) - (w : ℚ_[p])) hmem (sub_self _),
          zero_mul, mul_zero]
  rw [heq]
  exact Submodule.smul_mem _ _ hy
private theorem compP_weights_eq_mem_of_glAct_stable (LL : Letters N) (j : ℕ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (μ : Fin r → ℤ) :
    ∀ F : Finset (Fin r), (∀ c ∈ F, ∀ x ∈ S, glAct p LL j c c x ∈ S) →
      ∀ x ∈ S, compP (fun m => ∀ c ∈ F, wt LL j c m = μ c) x ∈ S := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ x hx
    rw [compP_congr _ (fun _ => True) (fun m => by simp), compP_true]
    exact hx
  | insert a F ha ih =>
    intro hS x hx
    rw [compP_congr _ (fun m => wt LL j a m = μ a ∧ ∀ c ∈ F, wt LL j c m = μ c)
      (fun m => Finset.forall_mem_insert _ _ _), compP_and]
    exact compP_weight_eq_mem_of_glAct_stable LL j a S (hS a (Finset.mem_insert_self _ _)) (μ a) _
      (ih (fun c hc => hS c (Finset.mem_insert_of_mem hc)) x hx)

theorem wcomp_memC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ c ∈ Cs, ∀ x ∈ S, glAct p LL j c c x ∈ S) (μ : Fin r → ℤ) :
    ∀ x ∈ S, compP (fun m => ∀ c ∈ Cs, wt LL j c m = μ c) x ∈ S := compP_weights_eq_mem_of_glAct_stable LL j S μ Cs hS

theorem exists_hwC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ S) (hx0 : x ≠ 0) : ∃ h ∈ S, h ≠ 0 ∧ ∃ μ, h ∈ HWC p LL j Cs μ := by
  classical
  have hSd : ∀ c ∈ Cs, ∀ z ∈ S, glAct p LL j c c z ∈ S := fun c hc z hz => hS c hc c hc z hz
  have hsupp : ∀ z ∈ S, ∀ m ∈ z.support, MultiDeg LL m := by
    intro z hz m hm
    have := hSP hz
    rw [Pol, mem_restrictSupport_iff] at this
    exact this (Finset.mem_coe.mpr hm)
  have hcong : ∀ (μ ν : Fin r → ℤ), (∀ c ∈ Cs, μ c = ν c) → ∀ z ∈ WtSpC p LL j Cs μ, z ∈ WtSpC p LL j Cs ν := by
    intro μ ν hμν z hz
    rw [WtSpC, mem_restrictSupport_iff] at hz ⊢
    intro m hm
    have := hz hm
    rw [Set.mem_setOf_eq] at this ⊢
    intro c hc
    rw [this c hc, hμν c hc]
  set M0 := (multiDeg_finite (r := r) LL).toFinset with hM0
  set A := M0.filter (fun m => ∃ h ∈ S, h ≠ 0 ∧ h ∈ WtSpC p LL j Cs (fun c => wt LL j c m)) with hA
  set φ : (Fin N × Fin r →₀ ℕ) → ℤ := fun m => ∑ c ∈ Cs, -((c : ℕ) : ℤ) * wt LL j c m with hφ
  have hAne : A.Nonempty := by
    have hne : x.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
      exact hx0
    obtain ⟨m0, hm0⟩ := hne
    refine ⟨m0, ?_⟩
    rw [hA, Finset.mem_filter, hM0, Set.Finite.mem_toFinset]
    refine ⟨hsupp x hx m0 hm0, compP (fun m => ∀ c ∈ Cs, wt LL j c m = wt LL j c m0) x,
      wcomp_memC LL j Cs S hSd _ x hx, ?_, ?_⟩
    · intro h0
      have := congrArg (coeff m0) h0
      rw [coeff_compP, if_pos (fun c _ => rfl), coeff_zero] at this
      exact (mem_support_iff.mp hm0) this
    · rw [WtSpC, mem_restrictSupport_iff]
      intro m hm
      have hc : coeff m (compP (fun m => ∀ c ∈ Cs, wt LL j c m = wt LL j c m0) x) ≠ 0 :=
        mem_support_iff.mp (Finset.mem_coe.mp hm)
      rw [coeff_compP] at hc
      split_ifs at hc with hP
      · exact hP
      · exact absurd rfl hc
  obtain ⟨ms, hms, hmax⟩ := Finset.exists_max_image A φ hAne
  rw [hA, Finset.mem_filter] at hms
  obtain ⟨_, h, hhS, hh0, hhW⟩ := hms
  refine ⟨h, hhS, hh0, fun c => wt LL j c ms, ?_⟩
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine ⟨hhW, fun c d hcd => ?_⟩
  obtain ⟨hc, hd, hlt⟩ := hcd
  by_contra hy0
  set y := glAct p LL j c d h with hy
  have hyS : y ∈ S := hS c hc d hd h hhS
  have hyW := glAct_wtspC LL j Cs c d (fun c => wt LL j c ms) h hhW
  have hne : y.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hy0
  obtain ⟨m', hm'⟩ := hne
  have hw' : ∀ e ∈ Cs, wt LL j e m' = shiftW (fun c => wt LL j c ms) c d e := by
    have := hyW
    rw [WtSpC, mem_restrictSupport_iff] at this
    exact this (Finset.mem_coe.mpr hm')
  have hm'A : m' ∈ A := by
    rw [hA, Finset.mem_filter, hM0, Set.Finite.mem_toFinset]
    exact ⟨hsupp y hyS m' hm', y, hyS, hy0, hcong _ _ (fun e he => (hw' e he).symm) y hyW⟩
  have hle := hmax m' hm'A
  have hcalc : φ m' = φ ms + ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) := by
    rw [hφ]
    dsimp only
    rw [Finset.sum_congr rfl (fun e he => by rw [hw' e he]),
      show (∑ e ∈ Cs, -((e : ℕ) : ℤ) * shiftW (fun c => wt LL j c ms) c d e) =
        ∑ e ∈ Cs, ((-((e : ℕ) : ℤ) * wt LL j e ms + (if c = e then -((e : ℕ) : ℤ) else 0)) -
          (if d = e then -((e : ℕ) : ℤ) else 0)) from
        Finset.sum_congr rfl (fun e _ => by simp only [shiftW]; split_ifs <;> ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos hc, if_pos hd]
    ring
  have hlt' : (c : ℕ) < (d : ℕ) := hlt
  have : ((c : ℕ) : ℤ) < ((d : ℕ) : ℤ) := by exact_mod_cast hlt'
  linarith

theorem proj_fixC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S) (hPS : ∀ x ∈ S, P x ∈ S)
    (hT : ∀ h ∈ S, h ≠ 0 → ∀ μ, h ∈ HWC p LL j Cs μ → μ ∈ T) : ∀ x ∈ S, P x = x := by
  have hPid : ∀ y, P (P y) = P y := fun y => LinearMap.congr_fun hP.1 y
  have hK0 : ∀ y ∈ S, P y = 0 → y = 0 := by
    intro y hy hPy
    by_contra hy0
    obtain ⟨h, hhK, hh0, μ, hμ⟩ := exists_hwC LL j Cs (S ⊓ LinearMap.ker P) (le_trans inf_le_left hSP)
      (fun c hc d hd z hz => by
        rw [Submodule.mem_inf, LinearMap.mem_ker] at hz ⊢
        exact ⟨hS c hc d hd z hz.1, by rw [typeProj_glActC LL j Cs T P hP c hc d hd z, hz.2, map_zero]⟩)
      y (Submodule.mem_inf.mpr ⟨hy, hPy⟩) hy0
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hhK
    have hT' := hT h hhK.1 hh0 μ hμ
    have hrange : h ∈ LinearMap.range P := by
      rw [hP.2.1]
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j Cs la) μ hT') (hwc_le_isoCC LL j Cs μ hμ)
    obtain ⟨z, rfl⟩ := hrange
    apply hh0
    rw [← hPid z]
    exact hhK.2
  intro x hx
  have := hK0 (P x - x) (sub_mem (hPS x hx) hx) (by rw [map_sub, hPid, sub_self])
  exact sub_eq_zero.mp this

end Lib

section YC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def YCondC (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (M : WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sSup {S | S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
    GlStableC p LL j Cs S}

theorem ycondC_glStable [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ) :
    GlStableC p LL j Cs (YCondC p LL j Cs Mt) := by
  intro c hc d hd x hx
  have hle : YCondC p LL j Cs Mt ≤ (YCondC p LL j Cs Mt).comap (glAct p LL j c d) := by
    unfold YCondC
    apply sSup_le
    rintro S ⟨h1, hS⟩ y hy
    exact (le_sSup (show S ∈ {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStableC p LL j Cs S} from ⟨h1, hS⟩))
      (hS c hc d hd y hy)
  exact hle hx

theorem ycondC_le_supp [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ) :
    YCondC p LL j Cs Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  unfold YCondC
  apply sSup_le
  rintro S ⟨h1, _⟩
  exact h1

theorem le_ycondC [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (h1 : S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h2 : GlStableC p LL j Cs S) : S ≤ YCondC p LL j Cs Mt :=
  le_sSup ⟨h1, h2⟩

theorem ycondC_keep [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      Q x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCondC p LL j Cs Mt, Q x ∈ YCondC p LL j Cs Mt := by
  intro x hx
  have hle : (YCondC p LL j Cs Mt).map Q ≤ YCondC p LL j Cs Mt := by
    apply le_ycondC
    · rintro _ ⟨y, hy, rfl⟩
      exact hw y (ycondC_le_supp LL j Cs Mt hy)
    · rintro c hc1 d hd1 _ ⟨y, hy, rfl⟩
      exact ⟨glAct p LL j c d y, ycondC_glStable LL j Cs Mt c hc1 d hd1 y hy, hc c hc1 d hd1 y⟩
  exact hle ⟨x, hx, rfl⟩

theorem ycond_le_ycondC [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ) :
    YCond p LL j Mt ≤ YCondC p LL j Cs Mt :=
  le_ycondC LL j Cs Mt _ (ycond_le_supp LL j Mt) (fun c _ d _ x hx => ycond_glStable LL j Mt c d x hx)

theorem le_ycond [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (h1 : S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h2 : GlStable p LL j S) : S ≤ YCond p LL j Mt :=
  le_sSup ⟨h1, h2⟩

theorem first_weight_le_of_support [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) (μ : Fin r → ℤ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh0 : h ≠ 0)
    (h1 : h ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h3 : h ∈ WtSpC p LL j Cs μ) : ((μ 0 : ℤ) : WithTop ℤ) ≤ Mt := by
  have hne : h.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hh0
  obtain ⟨m, hm⟩ := hne
  rw [mem_restrictSupport_iff] at h1
  rw [WtSpC, mem_restrictSupport_iff] at h3
  have a := h1 (Finset.mem_coe.mpr hm)
  have b := h3 (Finset.mem_coe.mpr hm)
  rw [Set.mem_setOf_eq] at a b
  rw [← b 0 h0]
  exact a

theorem ycondC_fix [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (hT : ∀ la : Fin r → ℤ, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt → la ∈ T) :
    ∀ x ∈ YCondC p LL j Cs Mt ⊓ Pol p r LL, P x = x := by
  intro x hx
  refine proj_fixC LL j Cs T P hP (YCondC p LL j Cs Mt ⊓ Pol p r LL) inf_le_right ?_ ?_ ?_ x hx
  · intro c hc d hd y hy
    rw [Submodule.mem_inf] at hy ⊢
    exact ⟨ycondC_glStable LL j Cs Mt c hc d hd y hy.1, glAct_pol LL j c d y hy.2⟩
  · intro y hy
    rw [Submodule.mem_inf] at hy ⊢
    exact ⟨ycondC_keep LL j Cs Mt P (fun c hc d hd z => typeProj_glActC LL j Cs T P hP c hc d hd z)
      (comm_preserves_weight_le LL j Mt P (fun z => typeProj_glActC LL j Cs T P hP 0 h0 0 h0 z)) y hy.1,
      typeProj_polC LL j Cs T P hP y hy.2⟩
  · intro h hh hh0 μ hμ
    rw [Submodule.mem_inf] at hh
    apply hT
    exact first_weight_le_of_support LL j Cs h0 Mt μ h hh0 (ycondC_le_supp LL j Cs Mt hh.1)
      (Submodule.mem_inf.mp hμ).1

theorem mem_typesLE_of_ycondC [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ x ∈ YCondC p LL j Cs Mt ⊓ Pol p r LL, x ∈ TypesLE p LL j Cs Mt := by
  intro x hx
  have hfix := ycondC_fix LL j Cs h0 Mt _ P hP (fun la h => h) x hx
  have h1 : x ∈ LinearMap.range P := ⟨x, hfix⟩
  rw [hP.2.1] at h1
  exact h1

theorem typeProj_range_le_ycond [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ)) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (hT : ∀ la ∈ T, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt) :
    ∀ x, P x ∈ YCond p LL j Mt := by
  intro x
  have h1 : P x ∈ LinearMap.range P := ⟨x, rfl⟩
  rw [hP.2.1] at h1
  exact (iSup₂_le fun la hla => isoC_le_ycond LL j la Mt (hT la hla)) h1

theorem ycond_fix [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ)) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (hT : ∀ la : Fin r → ℤ, ((la 0 : ℤ) : WithTop ℤ) ≤ Mt → la ∈ T) :
    ∀ x ∈ YCond p LL j Mt ⊓ Pol p r LL, P x = x := by
  intro x hx
  rw [Submodule.mem_inf] at hx
  exact ycondC_fix LL j univ (Finset.mem_univ _) Mt T P hP hT x
    (Submodule.mem_inf.mpr ⟨ycond_le_ycondC LL j univ Mt hx.1, hx.2⟩)

end YC

section Split
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def glRest (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j j' : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  glAct p LL j' c d - glAct p LL j c d

theorem glAct_split (LL : Letters N) (j j' : ℕ) (c d : Fin r) :
    glAct p LL j' c d = glAct p LL j c d + glRest p LL j j' c d := by
  unfold glRest; abel

theorem glRest_mem (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (c d : Fin r) :
    (glRest p LL j j' c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} := by
  show (glAct p LL j' c d - glAct p LL j c d : Module.End ℚ_[p] _) ∈ _
  unfold glAct
  rw [← Finset.sum_sub_distrib]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  by_cases h1 : (i : ℕ) < j
  · have h2 : (i : ℕ) < j' := lt_of_lt_of_le h1 hjj
    simp only [if_pos h1, if_pos h2, sub_self]
    exact Subalgebra.zero_mem _
  · have hm : ∀ e : Fin r, (i, e) ∈ {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} := fun e => not_lt.mp h1
    by_cases h2 : (i : ℕ) < j'
    · simp only [if_pos h2, if_neg h1, sub_zero]
      split_ifs
      · exact Subalgebra.mul_mem _ (FockB.mulLeftX_mem (hm c)) (FockB.pderiv_mem (hm d))
      · exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (FockB.mulLeftX_mem (hm d)) (FockB.pderiv_mem (hm c)))
    · simp only [if_neg h2, if_neg h1, sub_zero]
      exact Subalgebra.zero_mem _

theorem glRest_comm (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (c d a b : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glRest p LL j j' c d (glAct p LL j a b x) = glAct p LL j a b (glRest p LL j j' c d x) := FockB.ops_apply_comm (S := {v : Fin N × Fin r | j ≤ (v.1 : ℕ)}) (S' := {v : Fin N × Fin r | (v.1 : ℕ) < j})
  (Set.disjoint_left.mpr fun v h1 h2 => by
    simp only [Set.mem_setOf_eq] at h1 h2
    omega)
  (glRest_mem LL j j' hjj c d) (glAct_mem LL j a b) x

theorem typeProj_comm_later (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
  rw [glAct_split LL j j' c d, LinearMap.add_apply, LinearMap.add_apply, map_add,
    typeProj_glActC LL j univ T P hP c (Finset.mem_univ _) d (Finset.mem_univ _) x,
    typeProj_commC LL j univ T P hP (glRest p LL j j' c d) (fun a _ b _ y => glRest_comm LL j j' hjj c d a b y) x]

end Split

end Formalism.InvariantFactorPaths.L4
