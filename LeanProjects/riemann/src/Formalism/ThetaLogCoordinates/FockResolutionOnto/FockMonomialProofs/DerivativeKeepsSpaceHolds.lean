import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RaisingKeepsEarlyLetters
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.TypesLELeYcondC

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Onto
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem mem_xsp [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ XSp p LL J M ρ ↔ x ∈ Pol p r LL ∧ x ∈ FreeOf p (Fin.last K, ρ) ∧
      ∀ k, (K + 1 ≤ J k → x ∈ YCond p LL K (M k) ∧ x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧
        (¬ K + 1 ≤ J k → x ∈ YCond p LL (J k) (M k)) := by
  unfold XSp
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun k => ?_
  split_ifs with hk
  · rw [Submodule.mem_inf]
    exact ⟨fun h => ⟨fun _ => h, fun h' => absurd hk h'⟩, fun h => h.1 hk⟩
  · exact ⟨fun h => ⟨fun h' => absurd h' hk, fun _ => h⟩, fun h => h.2 hk⟩

theorem mem_y [NeZero r] {N : ℕ} (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Y p LL J M ↔ x ∈ Pol p r LL ∧ ∀ k, x ∈ YCond p LL (J k) (M k) := by
  unfold Y
  rw [Submodule.mem_inf, Submodule.mem_iInf]

theorem zero_mem_erase (ρ : Fin r) [NeZero r] (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) :
    (0 : Fin r) ∈ (univ : Finset (Fin r)).erase ρ := by
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  intro h'
  have := congrArg Fin.val h'
  simp at this
  omega

theorem setLast_self (LL : Letters (K + 1)) : setLast LL (LL.deg (Fin.last K)) = LL := by
  cases LL
  simp [setLast]

theorem pderiv_pol (LL : Letters (K + 1)) (a : Fin r) (o : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL (o + 1))) : pderiv (Fin.last K, a) x ∈ Pol p r (setLast LL o) := by
  classical
  have e : setLast (setLast LL (o + 1)) ((setLast LL (o + 1)).deg (Fin.last K) - 1) = setLast LL o := by
    simp [setLast]
  rw [Pol, mem_restrictSupport_iff] at hx ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
  have h1 : m + Finsupp.single (Fin.last K, a) 1 ∈ x.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have h2 : MultiDeg (setLast LL (o + 1)) (m + Finsupp.single (Fin.last K, a) 1) := hx (Finset.mem_coe.mpr h1)
  rw [add_comm m, multiDeg_pow (setLast LL (o + 1)) a 1 (by simp [setLast]) m, e] at h2
  exact h2

theorem pderiv_freeOf {σ : Type} (u v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) :
    pderiv u x ∈ FreeOf p v := by
  classical
  rw [FreeOf, mem_restrictSupport_iff] at hx ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
  have h1 : m + Finsupp.single u 1 ∈ x.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have h2 : (m + Finsupp.single u 1 : σ →₀ ℕ) v = 0 := hx (Finset.mem_coe.mpr h1)
  rw [Finsupp.add_apply] at h2
  exact (Nat.add_eq_zero_iff.mp h2).1

theorem resL_of_free {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by
  rw [FreeOf, mem_restrictSupport_iff] at hx
  ext m
  rw [resL_apply, coeff_initPart]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (hx (Finset.mem_coe.mpr (mem_support_iff.mpr (Ne.symm hc))))

theorem pderiv_ycond_early [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (hj : j ≤ K) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j Mt, pderiv (Fin.last K, c) x ∈ YCond p LL j Mt :=
  ops_ycond LL j Mt (pderiv (Fin.last K, c)).toLinearMap (FockB.pderiv_mem (by
    simp only [Set.mem_ofPred_eq, Fin.val_last]; exact hj))

theorem ycondC_pderiv [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r))
    (Mt : WithTop ℤ) (c : Fin r) (hc : c ∈ Cs) :
    ∀ x ∈ YCondC p LL (K + 1) Cs Mt, pderiv (Fin.last K, c) x ∈ YCondC p LL (K + 1) Cs Mt := by
  set B : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    ⨆ (c : Fin r) (_ : c ∈ Cs), (YCondC p LL (K + 1) Cs Mt).map (pderiv (Fin.last K, c)).toLinearMap with hB
  have hmem : ∀ c ∈ Cs, ∀ x ∈ YCondC p LL (K + 1) Cs Mt, pderiv (Fin.last K, c) x ∈ B := fun c hc x hx =>
    Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem hc
      (Submodule.mem_map_of_mem (f := (pderiv (Fin.last K, c)).toLinearMap) hx))
  have hle : B ≤ YCondC p LL (K + 1) Cs Mt := by
    refine le_ycondC LL (K + 1) Cs Mt _ ?_ ?_
    · refine iSup_le fun c => iSup_le fun _ => Submodule.map_le_iff_le_comap.mpr fun x hx =>
        pderiv_keep_wt LL hv c Mt x (ycondC_le_supp LL (K + 1) Cs Mt hx)
    · intro a ha b hb
      have : B ≤ B.comap (glAct p LL (K + 1) a b) := by
        refine iSup_le fun c => iSup_le fun hc => ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
        show glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) ∈ B
        have e : glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) =
            pderiv (Fin.last K, c) (glAct p LL (K + 1) a b x) - (if a = c then pderiv (Fin.last K, b) x else 0) := by
          rw [pderiv_glAct LL hv]; abel
        rw [e]
        refine Submodule.sub_mem _ (hmem c hc _ (ycondC_glStable LL (K + 1) Cs Mt a ha b hb x hx)) ?_
        split_ifs
        · exact hmem b hb x hx
        · exact Submodule.zero_mem _
      exact fun y hy => this hy
  intro x hx
  exact hle (hmem c hc x hx)

theorem pderiv_last_letter_mem [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ a : Fin r)
    (o : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P)
    (ha : a ≠ ρ) :
    ∀ x ∈ XSp p (setLast LL (o + 1)) J M ρ, pderiv (Fin.last K, a) x ∈ XSp p (setLast LL o) J M ρ := by
  intro x hx
  rw [mem_xsp] at hx ⊢
  obtain ⟨hxP, hxF, hxk⟩ := hx
  have hdP := pderiv_pol LL a o x hxP
  have h0 := zero_mem_erase ρ hr hρ
  refine ⟨hdP, pderiv_freeOf _ _ x hxF, fun k => ⟨fun hk => ⟨?_, ?_⟩, fun hk => ?_⟩⟩
  · exact pderiv_ycond_early LL K le_rfl (M k) a x ((hxk k).1 hk).1
  · obtain ⟨P, hP⟩ := hTP (M k)
    refine mem_typesLE_of_ycondC (setLast LL o) (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hdP⟩)
    exact ycondC_pderiv LL hv _ (M k) a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩) x
      (typesLE_le_ycondC LL (K + 1) _ h0 (M k) ((hxk k).1 hk).2)
  · exact pderiv_ycond_early LL (J k) (by omega) (M k) a x ((hxk k).2 hk)

theorem restriction_mem_space [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ h ∈ Y p LL J M, resL p (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ := by
  intro h hh
  rw [mem_y] at hh
  obtain ⟨hhP, hhY⟩ := hh
  have hresP : resL p (Fin.last K, ρ) 0 h ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 _ h hhP
  have key : ∀ j ≤ K, ∀ Mt : WithTop ℤ, ∀ x ∈ YCond p LL j Mt, resL p (Fin.last K, ρ) 0 x ∈ YCond p LL j Mt :=
    fun j hj Mt => ycond_keep LL j Mt (resL p (Fin.last K, ρ) 0)
      (fun c d x => resL_glAct LL j c d (Fin.last K, ρ) 0 (fun i hi =>
        ⟨fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm,
          fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _)
  have h0 := zero_mem_erase ρ hr hρ
  rw [mem_xsp]
  refine ⟨hresP, resL_free (Fin.last K, ρ) h, fun k => ⟨fun hk => ?_, fun hk => key (J k) (by omega) _ _ (hhY k)⟩⟩
  have h1 : h ∈ YCond p LL (K + 1) (M k) := by
    have := hhY k
    rw [ycond_min, min_eq_right hk] at this
    exact this
  refine ⟨key K le_rfl _ _ (condition_drop_holds p K r LL (M k) hv h hhP h1), ?_⟩
  obtain ⟨P, hP⟩ := hTP (M k)
  refine mem_typesLE_of_ycondC LL (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hresP⟩)
  refine ycondC_keep LL (K + 1) _ (M k) (resL p (Fin.last K, ρ) 0) (fun c hc d hd x =>
    resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ =>
      ⟨fun h' => (Finset.mem_erase.mp hc).1 (Prod.mk.inj h').2,
        fun h' => (Finset.mem_erase.mp hd).1 (Prod.mk.inj h').2⟩) x)
    (resL_keep_supp (Fin.last K, ρ) 0 _) h (ycond_le_ycondC LL (K + 1) _ (M k) h1)

theorem ycond_mono [NeZero r] {N : ℕ} (LL : Letters N) (j : ℕ) (Mt Mt' : WithTop ℤ) (h : Mt ≤ Mt') :
    YCond p (r := r) LL j Mt ≤ YCond p LL j Mt' := by
  refine le_ycond LL j Mt' _ ?_ (fun c d x hx => ycond_glStable LL j Mt c d x hx)
  intro x hx
  have h1 := ycond_le_supp LL j Mt hx
  rw [mem_restrictSupport_iff] at h1 ⊢
  intro m hm
  exact le_trans (h1 hm) h

theorem ycond_late [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (hj : K + 1 ≤ j) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt = YCond p LL (K + 1) Mt := by
  rw [ycond_min, min_eq_right hj]

theorem free_ycond_succ [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    YCond p LL K Mt ⊓ FreeLast p K r ≤ YCond p LL (K + 1) Mt := by
  refine le_ycond LL (K + 1) Mt _ ?_ ?_
  · intro x hx
    have h1 := ycond_le_supp LL K Mt (Submodule.mem_inf.mp hx).1
    have h2 := (Submodule.mem_inf.mp hx).2
    rw [FreeLast, mem_restrictSupport_iff] at h2
    rw [mem_restrictSupport_iff] at h1 ⊢
    intro m hm
    have h3 := h1 hm
    have h4 := h2 hm 0
    simp only [Set.mem_ofPred_eq] at h3 ⊢
    rw [wt_succ LL hv, h4]
    simpa using h3
  · intro c d x hx
    have h2 := (Submodule.mem_inf.mp hx).2
    have e : glAct p LL (K + 1) c d x = glAct p LL K c d x := by
      rw [glAct_succ LL hv, pderiv_freeLast x h2 d, mul_zero, add_zero]
    rw [e]
    refine Submodule.mem_inf.mpr ⟨ycond_glStable LL K Mt c d x (Submodule.mem_inf.mp hx).1, ?_⟩
    refine ops_keep_supp {v : Fin (K + 1) × Fin r | (v.1 : ℕ) < K}
      {m : Fin (K + 1) × Fin r →₀ ℕ | ∀ c, m (Fin.last K, c) = 0} (fun m m' hmm hm c' => ?_)
      (glAct_mem LL K c d) x h2
    rw [← hmm (Fin.last K, c') (by simp only [Set.mem_ofPred_eq, Fin.val_last, lt_irrefl, not_false_eq_true])]
    exact hm c'

theorem pol_zero_free (LL : Letters (K + 1)) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL 0)) : x ∈ FreeLast p K r := by
  rw [Pol, mem_restrictSupport_iff] at hx
  rw [FreeLast, mem_restrictSupport_iff]
  intro m hm c
  have h1 : ∑ c, m (Fin.last K, c) = (setLast LL 0).deg (Fin.last K) := hx hm (Fin.last K)
  have h2 : (setLast LL 0).deg (Fin.last K) = 0 := by simp [setLast]
  rw [h2] at h1
  exact Finset.sum_eq_zero_iff.mp h1 c (Finset.mem_univ c)

theorem restriction_surjective [NeZero r] (hΩ : OmegaInj) (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ (o : ℕ), ∀ x ∈ XSp p (setLast LL o) J M ρ,
      ∃ h ∈ Y p (setLast LL o) J M, resL p (Fin.last K, ρ) 0 h = x := by
  intro o
  induction o with
  | zero =>
    intro x hx
    rw [mem_xsp] at hx
    obtain ⟨hxP, hxF, hxk⟩ := hx
    refine ⟨x, (mem_y _ J M x).mpr ⟨hxP, fun k => ?_⟩, resL_of_free _ x hxF⟩
    by_cases hk : K + 1 ≤ J k
    · rw [ycond_late _ (J k) hk]
      exact free_ycond_succ LL hv (M k) (Submodule.mem_inf.mpr ⟨((hxk k).1 hk).1, pol_zero_free LL x hxP⟩)
    · exact (hxk k).2 hk
  | succ o ih =>
    by_cases hfin : ∃ k, K + 1 ≤ J k ∧ M k ≠ ⊤
    ·
      obtain ⟨k1, hk1, hM1⟩ := hfin
      have hne : (univ.filter fun k => K + 1 ≤ J k).Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ M hne
      have hk0' : K + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
      have hmin' : ∀ k, K + 1 ≤ J k → M k0 ≤ M k := fun k hk =>
        hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
      have hM0 : M k0 ≠ ⊤ := fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hM0
      set X1 := XSp p (setLast LL (o + 1)) J M ρ with hX1
      set R := (Y p (setLast LL (o + 1)) J M).map (resL p (Fin.last K, ρ) 0) with hR
      have hRle : R ≤ X1 := Submodule.map_le_iff_le_comap.mpr fun h hh =>
        restriction_mem_space (setLast LL (o + 1)) J M ρ hr hρ hv hTP h hh

      have hU : ∀ a : Fin r, ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by
        intro a h hh
        rw [mem_y] at hh ⊢
        refine ⟨raising_degree_holds p K r LL c univ a o h hh.1, fun k => ?_⟩
        by_cases hk : K + 1 ≤ J k
        · have h1 : h ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) := by
            have := hh.2 k0
            rw [ycond_late _ (J k0) hk0', ← hc] at this
            exact this
          rw [ycond_late _ (J k) hk]
          exact ycond_mono LL (K + 1) _ _ (hc ▸ hmin' k hk) (raising_keeps_last_letter p K r LL c a hv h h1)
        · exact raising_keeps_early_letters p K r LL c univ a (J k) (M k) (by omega) h (hh.2 k)
      have hOm : ∀ x ∈ X1, Omega p LL c ρ x ∈ R := by
        intro x hx
        unfold Omega
        rw [LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun a ha => ?_
        have haρ : a ≠ ρ := (Finset.mem_erase.mp ha).1
        obtain ⟨h, hh, hres⟩ := ih _ (pderiv_last_letter_mem LL J M ρ a o hr hρ hv hTP haρ x hx)
        rw [LinearMap.comp_apply]
        have e : dW p K a x = pderiv (Fin.last K, a) x := rfl
        rw [e, ← hres]
        have := restriction_raising_holds p K r LL c ρ a h haρ
        rw [resL_apply, ← this]
        exact Submodule.mem_map_of_mem (f := resL p (Fin.last K, ρ) 0) (hU a h hh)
      have hinj : ∀ x ∈ X1, Omega p LL c ρ x = 0 → x = 0 := by
        intro x hx h0
        have hx' := (mem_xsp _ J M ρ x).mp hx
        refine hΩ p K r LL ρ c o hr hρ hv x (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hx'.1, hx'.2.1⟩, ?_⟩) h0
        rw [hc]
        exact ((hx'.2.2 k0).1 hk0').2
      have hXP : X1 ≤ Pol p r (setLast LL (o + 1)) := fun x hx => ((mem_xsp _ J M ρ x).mp hx).1
      have := pol_finiteDimensional (p := p) (r := r) (setLast LL (o + 1))
      have : FiniteDimensional ℚ_[p] X1 := Submodule.finiteDimensional_of_le hXP
      let f : X1 →ₗ[ℚ_[p]] X1 := (Omega p LL c ρ).restrict (fun x hx => hRle (hOm x hx))
      have hfi : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro y hy
        have : Omega p LL c ρ (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = 0 := congrArg Subtype.val hy
        exact Subtype.ext (hinj y y.2 this)
      have hfs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hfi
      intro x hx
      obtain ⟨y, hy⟩ := hfs ⟨x, hx⟩
      have hxy : Omega p LL c ρ (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = x := congrArg Subtype.val hy
      have hxR : x ∈ R := hxy ▸ hOm y y.2
      obtain ⟨h, hh, hres⟩ := Submodule.mem_map.mp hxR
      exact ⟨h, hh, hres⟩
    ·
      intro x hx
      rw [mem_xsp] at hx
      obtain ⟨hxP, hxF, hxk⟩ := hx
      refine ⟨x, (mem_y _ J M x).mpr ⟨hxP, fun k => ?_⟩, resL_of_free _ x hxF⟩
      by_cases hk : K + 1 ≤ J k
      · have : M k = ⊤ := by
          by_contra hne
          exact hfin ⟨k, hk, hne⟩
        rw [this, Formalism.CountingSumsFrames.ycond_top]
        exact Submodule.mem_top
      · exact (hxk k).2 hk

end Onto

theorem derivative_keeps_space_holds : DKeepsX := by
  intro p _ K r _ LL q J M ρ a e1 o hr hρ hv hHP ha x hx
  have h0 := zero_mem_erase ρ hr hρ
  refine pderiv_last_letter_mem LL J M ρ a o hr hρ hv (fun Mt => ?_) ha x hx
  obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
    {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ Mt) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ Mt)
      rw [hl 0 h0])
  exact ⟨P, hP⟩

theorem resOntoKThm_of (hΩ : OmegaInj) : ResOntoKThm := by
  intro p _ K r _ LL q J M ρ e1 hr hρ hv hHP x hx
  have h0 := zero_mem_erase ρ hr hρ
  have key := restriction_surjective hΩ LL J M ρ hr hρ hv (fun Mt => by
    obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
      {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} (fun la la' hl => by
        show (((la 0 : ℤ) : WithTop ℤ) ≤ Mt) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ Mt)
        rw [hl 0 h0])
    exact ⟨P, hP⟩) (LL.deg (Fin.last K))
  rw [setLast_self] at key
  exact key x hx

end Formalism.InvariantFactorPaths.L4
