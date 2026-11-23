import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Triv
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem supp_le_of_monomial {σ : Type} (Q : Set (σ →₀ ℕ)) (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]))
    (h : ∀ m ∈ Q, monomial m (1 : ℚ_[p]) ∈ S) : restrictSupport ℚ_[p] Q ≤ S := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum]
  refine S.sum_mem fun m hm => ?_
  have hmon : monomial m (coeff m x) = coeff m x • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  exact S.smul_mem _ (h m (hx hm))

theorem glAct_none (LL : Letters N) (j : ℕ) (h : ∀ i : Fin N, ¬ (i : ℕ) < j) (c d : Fin r) :
    glAct p LL j c d = 0 := by
  simp [Formalism.GM.M.glAct, h]

theorem wt_none (LL : Letters N) (j : ℕ) (h : ∀ i : Fin N, ¬ (i : ℕ) < j) (c : Fin r)
    (m : Fin N × Fin r →₀ ℕ) : wt LL j c m = 0 := by
  simp [Formalism.GM.M.wt, h]

theorem glAct_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c d : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL 1 c d x =
      if LL.vec i0 then X (i0, c) * pderiv (i0, d) x else -(X (i0, d) * pderiv (i0, c) x) := by
  simp only [Formalism.GM.M.glAct]
  rw [Finset.sum_eq_single i0]
  · have hlt : (i0 : ℕ) < 1 := by omega
    rw [if_pos hlt]
    split_ifs <;> simp
  · intro b _ hb
    have hnb : ¬ (b : ℕ) < 1 := by
      intro hlt
      exact hb (Fin.ext (by omega))
    rw [if_neg hnb]
  · intro hn
    exact absurd (Finset.mem_univ i0) hn

theorem wt_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL 1 c m = if LL.vec i0 then (m (i0, c) : ℤ) else -(m (i0, c) : ℤ) := by
  simp only [Formalism.GM.M.wt]
  rw [Finset.sum_eq_single i0]
  · rw [if_pos (by omega)]
  · intro b _ hb
    have hnb : ¬ (b : ℕ) < 1 := by
      intro hlt
      exact hb (Fin.ext (by omega))
    rw [if_neg hnb]
  · intro hn
    exact absurd (Finset.mem_univ i0) hn

theorem move_mem (i0 : Fin N) (t : Fin r) (d : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ t → m (i0, c) = 0) → m (i0, t) = d →
      monomial m (1 : ℚ_[p]) ∈ S)
    (hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, t) x ∈ S) :
    ∀ (n : ℕ) (m : Fin N × Fin r →₀ ℕ), m (i0, t) + n = d → ∑ c, m (i0, c) = d →
      monomial m (1 : ℚ_[p]) ∈ S := by
  intro n
  induction n with
  | zero =>
    intro m hm hs
    refine hbase m (fun c hc => ?_) (by omega)
    have h1 := Finset.add_sum_erase Finset.univ (fun c => m (i0, c)) (Finset.mem_univ t)
    have h2 : ∑ x ∈ Finset.univ.erase t, m (i0, x) = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp h2 c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
  | succ n ih =>
    intro m hm hs
    obtain ⟨a, hat, ha⟩ : ∃ a, a ≠ t ∧ m (i0, a) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have hsum : ∑ c, m (i0, c) = m (i0, t) :=
        Finset.sum_eq_single t (fun c _ hc => hne c hc) (fun hn => absurd (Finset.mem_univ t) hn)
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : Fin N × Fin r →₀ ℕ,
        m' = m - Finsupp.single (i0, a) 1 + Finsupp.single (i0, t) 1 := ⟨_, rfl⟩
    have hle : Finsupp.single (i0, a) 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have heq : m' + Finsupp.single (i0, a) 1 = m + Finsupp.single (i0, t) 1 := by
      rw [hm', add_right_comm, tsub_add_cancel_of_le hle]
    have key : ∀ (f : Fin N × Fin r →₀ ℕ) (b : Fin r),
        ∑ c, ((f + Finsupp.single (i0, b) 1 : Fin N × Fin r →₀ ℕ)) (i0, c) = ∑ c, f (i0, c) + 1 := by
      intro f b
      simp [Finsupp.single_apply, Finset.sum_add_distrib]
    have hsum : ∑ c, m' (i0, c) = d := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => ∑ c, f (i0, c)) heq
      simp only [key] at h3
      omega
    have ht : m' (i0, t) = m (i0, t) + 1 := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => f (i0, t)) heq
      simp [Finsupp.single_apply, hat] at h3
      omega
    have hmem := ih m' (by omega) hsum
    have hX := hst a _ hmem
    have he : Finsupp.single (i0, a) 1 + (m' - Finsupp.single (i0, t) 1) = m := by
      rw [hm', add_tsub_cancel_right, add_tsub_cancel_of_le hle]
    have hcalc : X (i0, a) * pderiv (i0, t) (monomial m' (1 : ℚ_[p])) =
        ((m (i0, t) + 1 : ℕ) : ℚ_[p]) • monomial m (1 : ℚ_[p]) := by
      rw [pderiv_monomial, ← pow_one (X (i0, a)), ← monomial_single_add, he, smul_monomial, ht]
      simp
    rw [hcalc] at hX
    have hne : ((m (i0, t) + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m (i0, t))
    have h4 := S.smul_mem (((m (i0, t) + 1 : ℕ) : ℚ_[p]))⁻¹ hX
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4

theorem pol_le_iso (LL : Letters N) (j : ℕ) (hj : j ≤ 1) (hr : 1 ≤ r) :
    ∃ la : Fin r → ℤ, Pol p r LL ≤ IsoC p LL j univ la := by
  by_cases hex : ∃ i0 : Fin N, (i0 : ℕ) < j
  · obtain ⟨i0, hi0⟩ := hex
    have hj1 : j = 1 := by omega
    have h0 : (i0 : ℕ) = 0 := by omega
    subst hj1
    rcases Bool.eq_false_or_eq_true (LL.vec i0) with hv | hv
    ·
      refine ⟨fun c => if c = (⟨0, hr⟩ : Fin r) then (LL.deg i0 : ℤ) else 0, ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ (⟨0, hr⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨0, hr⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_pos rfl]
          by_cases hc : c = ⟨0, hr⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hd0 : d ≠ ⟨0, hr⟩ := by
            intro hd0
            have hlt := hcd.2.2
            rw [hd0, Fin.lt_def] at hlt
            exact Nat.not_lt_zero _ hlt
          rw [glAct_one LL i0 h0 c d, hv, if_pos rfl, pderiv_monomial, hz d hd0]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨0, hr⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS a (Finset.mem_univ _) ⟨0, hr⟩ (Finset.mem_univ _) x hx
        rwa [glAct_one LL i0 h0, hv, if_pos rfl] at h1
      have hle : m (i0, ⟨0, hr⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨0, hr⟩ (LL.deg i0) S hbase hst (LL.deg i0 - m (i0, ⟨0, hr⟩)) m
        (by omega) (hm' i0)
    ·
      refine ⟨fun c => -(if c = (⟨r - 1, by omega⟩ : Fin r) then (LL.deg i0 : ℤ) else 0), ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ,
          (∀ c, c ≠ (⟨r - 1, by omega⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨r - 1, by omega⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_neg Bool.false_ne_true]
          by_cases hc : c = ⟨r - 1, by omega⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hct : c ≠ ⟨r - 1, by omega⟩ := by
            intro hct
            have hlt := hcd.2.2
            rw [Fin.lt_def, hct] at hlt
            have hdr := d.isLt
            simp only at hlt
            omega
          rw [glAct_one LL i0 h0 c d, hv, if_neg Bool.false_ne_true, pderiv_monomial, hz c hct]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨r - 1, by omega⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS ⟨r - 1, by omega⟩ (Finset.mem_univ _) a (Finset.mem_univ _) x hx
        rw [glAct_one LL i0 h0, hv, if_neg Bool.false_ne_true] at h1
        have h2 := S.neg_mem h1
        rwa [neg_neg] at h2
      have hle : m (i0, ⟨r - 1, by omega⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨r - 1, by omega⟩ (LL.deg i0) S hbase hst
        (LL.deg i0 - m (i0, ⟨r - 1, by omega⟩)) m (by omega) (hm' i0)
  · push_neg at hex
    have hn : ∀ i : Fin N, ¬ (i : ℕ) < j := fun i => not_lt.mpr (hex i)
    refine ⟨0, fun F _ => ?_⟩
    refine Formalism.CountingSumsFrames.hwc_le_isoC (p := p) LL j 0 ?_
    simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
      LinearMap.mem_ker, MvPolynomial.mem_restrictSupport_iff]
    refine ⟨fun m _ => ?_, fun c d _ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      intro c _
      rw [wt_none LL j hn]
      rfl
    · simp [glAct_none LL j hn]

end Triv

theorem trivial_projection_holds : TrivProj := by
  intro p _ N r LL j T P hj hr hP
  obtain ⟨la, hla⟩ := pol_le_iso (p := p) LL j hj hr
  obtain ⟨hPP, hran, hker⟩ := hP
  by_cases hT : la ∈ T
  · left
    intro F hF
    have hFr : F ∈ LinearMap.range P := by
      rw [hran]
      exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hT (hla hF))
    obtain ⟨y, rfl⟩ := hFr
    have h1 := congrArg (fun f => f y) hPP
    simpa using h1
  · right
    intro F hF
    have hFk : F ∈ LinearMap.ker P := by
      rw [hker]
      exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hT (hla hF))
    exact hFk

theorem highest_vector_projection_holds : HighestVectorProjectionPos := by
  classical
  intro p _ K r _ LL q J M ρ w e1 hK hr hρ hv hHP hHE
  obtain ⟨hP1, hP2⟩ := hHP
  obtain ⟨PE, hE1, hE2, hE3, hE4, hE5⟩ := hHE (K + 1) le_rfl w
  set v : Fin (K + 1) × Fin r := (Fin.last K, ρ) with hvdef
  set Wt := WtSpC p LL (K + 1) univ w with hWtdef

  let Cs : Fin (K + 2) → Finset (Fin r) := fun i => if (i : ℕ) = K + 1 then univ.erase ρ else univ
  let s : Fin (K + 2) → Finset (Fin q) := fun i =>
    univ.filter fun k => J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)
  let thr : Fin (K + 2) → WithTop ℤ := fun i => (s i).inf M
  let T : Fin (K + 2) → Set (Fin r → ℤ) := fun i => {la | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i}
  have h0ρ : (0 : Fin r) ≠ ρ := by
    intro h
    have h' := congrArg Fin.val h
    have h0 : ((0 : Fin r) : ℕ) = 0 := by simp
    rw [hρ, h0] at h'
    omega
  have hCsT : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → Cs i = univ.erase ρ := fun i h => if_pos h
  have hCsL : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → Cs i = univ := fun i h => if_neg h
  have hCs : ∀ i, Cs i = univ ∨ Cs i = univ.erase ρ := by
    intro i
    by_cases h : (i : ℕ) = K + 1
    · exact Or.inr (hCsT i h)
    · exact Or.inl (hCsL i h)
  have h0Cs : ∀ i, (0 : Fin r) ∈ Cs i := by
    intro i
    rcases hCs i with h | h <;> rw [h]
    · exact mem_univ _
    · exact mem_erase.mpr ⟨h0ρ, mem_univ _⟩
  have hsat : ∀ i, CsSaturated (Cs i) (T i) := fun i la la' h => by
    show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i ↔ ((la' 0 : ℤ) : WithTop ℤ) ≤ thr i
    rw [h 0 (h0Cs i)]
  have hthrle : ∀ (i : Fin (K + 2)) (k : Fin q), (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) → thr i ≤ M k :=
    fun i k hk => Finset.inf_le (mem_filter.mpr ⟨mem_univ k, hk⟩)
  have hthrc : ∀ i : Fin (K + 2), thr i = ⊤ ∨
      ∃ k, (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) ∧ thr i = M k := by
    intro i
    rcases (s i).eq_empty_or_nonempty with he | hne
    · left
      show (s i).inf M = ⊤
      rw [he, Finset.inf_empty]
    · right
      obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_inf (s i) hne M
      exact ⟨k, (mem_filter.mp hk).2, hke⟩
  have hex : ∀ i : Fin (K + 2), ∃ P, IsTypeProj p LL i (Cs i) (T i) P ∧
      (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun i => hP1 i (Nat.lt_succ_iff.mp i.isLt) (Cs i) (hCs i) (T i) (hsat i)
  choose P hPt hPsa hPint using hex
  have hPlow : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → IsTypeProj p LL i univ (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsL i h] at this
  have hPtop : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → IsTypeProj p LL (K + 1) (univ.erase ρ) (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsT i h, h] at this
  have hPP : ∀ i x, P i (P i x) = P i x := fun i x => LinearMap.congr_fun (hPt i).1 x
  have hsub : ∀ i i' : Fin (K + 2), (i : ℕ) ≤ (i' : ℕ) → Cs i' ⊆ Cs i := by
    intro i i' h
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi, hCsT i' (by have := i'.isLt; omega)]
    · rw [hCsL i hi]; exact subset_univ _
  have hcomm : ∀ i i' x, P i (P i' x) = P i' (P i x) := by
    intro i i' x
    rcases le_total (i : ℕ) (i' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 i i' (Cs i) (Cs i') (T i) (T i') (P i) (P i') h (hsub i i' h) (hCs i)
        (hCs i') (hPt i) (hPt i')) x
    · exact (LinearMap.congr_fun (hP2 i' i (Cs i') (Cs i) (T i') (T i) (P i') (P i) h (hsub i' i h) (hCs i')
        (hCs i) (hPt i') (hPt i)) x).symm
  have hPpol : ∀ i, ∀ x ∈ Pol p r LL, P i x ∈ Pol p r LL := fun i => typeProj_polC LL i (Cs i) (T i) (P i) (hPt i)

  have hPgl : ∀ i, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      P i (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P i x) := by
    intro i c hc d hd x
    by_cases hi : (i : ℕ) = K + 1
    · exact typeProj_glActC LL (K + 1) _ (T i) (P i) (hPtop i hi) c hc d hd x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c d x
  have hPcar : ∀ i c x, P i (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P i x) := by
    intro i c x
    by_cases hi : (i : ℕ) = K + 1
    · by_cases hc : c = ρ
      · subst hc
        exact typeProj_commC LL (K + 1) _ (T i) (P i) (hPtop i hi) (glAct p LL (K + 1) c c)
          (fun a ha b hb x => cartan_comm_erase' LL (K + 1) c a ha b hb x) x
      · exact hPgl i c (mem_erase.mpr ⟨hc, mem_univ _⟩) c (mem_erase.mpr ⟨hc, mem_univ _⟩) x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c c x
  have hPWt : ∀ i, ∀ x ∈ Wt, P i x ∈ Wt := fun i => comm_wtsp LL (K + 1) (P i) (hPcar i) w
  have hPres : ∀ i x, P i (resL p v 0 x) = resL p v 0 (P i x) := by
    intro i
    refine typeProj_commC LL i (Cs i) (T i) (P i) (hPt i) (resL p v 0) (fun c hc d hd x => ?_)
    refine resL_glAct LL i c d v 0 (fun i' hi' => ?_) x
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi] at hc hd
      exact ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩
    · have hne : i' ≠ Fin.last K := by
        intro h
        rw [h, Fin.val_last] at hi'
        have := i.isLt
        omega
      exact ⟨fun h => hne (Prod.mk.inj h).1, fun h => hne (Prod.mk.inj h).1⟩
  have hPfree : ∀ i, ∀ x ∈ FreeOf p v, P i x ∈ FreeOf p v := by
    intro i x hx
    rw [← resL_fix' v x hx, hPres i x]
    exact resL_free v _

  have hEcomm := hwProj_comm' LL (K + 1) ρ w PE
  have hEP : ∀ i, ∀ x ∈ Wt, PE (P i x) = P i (PE x) := fun i => hEcomm (P i) hE1 hE2 hE3 (hPgl i) (hPWt i)
  have hEres : ∀ x ∈ Wt, PE (resL p v 0 x) = resL p v 0 (PE x) :=
    hEcomm (resL p v 0) hE1 hE2 hE3
      (fun c hc d hd x => resL_glAct LL (K + 1) c d v 0 (fun i' _ =>
        ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩) x)
      (resL_keep_supp v 0 _)
  have hEeul : ∀ i0 : Fin (K + 1), ∀ x ∈ Wt, PE (ProjS.eulL (fun c : Fin r => (i0, c)) x) =
      ProjS.eulL (fun c : Fin r => (i0, c)) (PE x) := fun i0 =>
    hEcomm (ProjS.eulL (fun c : Fin r => (i0, c))) hE1 hE2 hE3
      (fun c _ d _ x => eul_glAct LL (K + 1) i0 c d x)
      (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i0 c c x) w)
  have hEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt, PE g = g := by
    intro g hg
    rw [← hE2] at hg
    obtain ⟨z, rfl⟩ := hg
    exact LinearMap.congr_fun hE1 z

  have hgfix : ∀ g ∈ XSp p LL J M ρ, ∀ i, P i g = g := by
    intro g hg i
    obtain ⟨hg1, hgI⟩ := Submodule.mem_inf.mp hg
    have hgP := (Submodule.mem_inf.mp hg1).1
    rw [Submodule.mem_iInf] at hgI
    by_cases hi : (i : ℕ) = K + 1
    · rcases hthrc i with ht | ⟨k, hk, ht⟩
      · refine ycondC_fix LL (K + 1) (univ.erase ρ) (mem_erase.mpr ⟨h0ρ, mem_univ _⟩) ⊤ (T i) (P i) (hPtop i hi)
          (fun la _ => ?_) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
        · show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i
          rw [ht]; exact le_top
        · refine le_ycondC LL (K + 1) (univ.erase ρ) ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ _ _ => trivial) trivial
          rw [mem_restrictSupport_iff]
          intro m _
          exact (le_top : ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · have hk' : K + 1 ≤ J k := by omega
        have h1 := hgI k
        rw [if_pos hk'] at h1
        have h2 := (Submodule.mem_inf.mp h1).2
        have hT : T i = {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := by
          show {la : Fin r → ℤ | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i} = _
          rw [ht]
        have h3 : g ∈ LinearMap.range (P i) := by
          rw [(hPtop i hi).2.1, hT]
          exact h2
        obtain ⟨z, rfl⟩ := h3
        exact hPP i z
    · refine ycond_fix LL i (T i) (thr i) (P i) (hPlow i hi) (fun la h => h) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
      rcases hthrc i with ht | ⟨k, hk, ht⟩
      · rw [ht]
        refine le_ycond LL i ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ => trivial) trivial
        rw [mem_restrictSupport_iff]
        intro m _
        exact (le_top : ((wt LL i 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · rw [ht]
        have h1 := hgI k
        have := i.isLt
        rcases hk with hk | ⟨hk1, hk2⟩
        · rw [if_neg (by omega), hk] at h1
          exact h1
        · rw [if_pos hk2] at h1
          rw [show (i : ℕ) = K by omega]
          exact (Submodule.mem_inf.mp h1).1

  let Q := lcomp P (List.finRange (K + 2))
  let f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := fun m =>
    if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then PE (Q (monomial m 1)) else 0
  refine ⟨(basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, fun m hm hmv => ?_⟩
  have hPr : (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m := by
    have := (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m
    rwa [coe_basisMonomials] at this
  rw [hPr]
  by_cases hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c
  · rw [show f m = PE (Q (monomial m 1)) from if_pos hw]
    set u : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := monomial m 1 with hu
    have huP : u ∈ Pol p r LL := monomial_mem_supp' _ m hm
    have huZ : u ∈ PolZ p r LL := by
      refine Submodule.mem_inf.mpr ⟨huP, mem_intPol_of_norm _ fun m' => ?_⟩
      rw [hu, coeff_monomial]; split_ifs <;> simp
    have huW : u ∈ Wt := monomial_mem_supp' _ m hw
    have huF : u ∈ FreeOf p v := monomial_mem_supp' _ m hmv
    set y := Q u with hy
    have hyW : y ∈ Wt := lcomp_keep P (Wt : Set _) _ (fun j _ => hPWt j) u huW
    have hyF : y ∈ FreeOf p v := lcomp_keep P (FreeOf p v : Set _) _ (fun j _ => hPfree j) u huF
    have hyP : y ∈ Pol p r LL := lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
    have hyfix : ∀ i, P i y = y := fun i => lcomp_fix P hPP hcomm _ i (List.mem_finRange i) _

    have hl : List.finRange (K + 2) = 0 :: 1 :: ((List.finRange K).map Fin.succ).map Fin.succ := by
      rw [List.finRange_succ, List.finRange_succ]
      simp
    have hint0 := lcomp_int LL e1 P hPpol hPint (((List.finRange K).map Fin.succ).map Fin.succ) u huZ
    rw [List.length_map, List.length_map, List.length_finRange] at hint0
    have hy'P : lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∈ Pol p r LL :=
      lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
    have hyy : y = lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∨ y = 0 := by
      have hy2 : y = P 0 (P 1 (lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u)) := by
        rw [hy]
        show lcomp P (List.finRange (K + 2)) u = _
        rw [hl, lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [hy2]
      rcases trivial_projection_holds p (K + 1) r LL _ (T 1) (P 1) (by simp) (by omega) (hPlow 1 (by simp; omega)) with h1 | h1
      · rw [h1 _ hy'P]
        rcases trivial_projection_holds p (K + 1) r LL _ (T 0) (P 0) (by simp) (by omega) (hPlow 0 (by simp)) with h0 | h0
        · exact Or.inl (h0 _ hy'P)
        · exact Or.inr (h0 _ hy'P)
      · rw [h1 _ hy'P, map_zero]
        exact Or.inr rfl
    have hint : ((p : ℚ_[p]) ^ (e1 * K)) • y ∈ PolZ p r LL := by
      rcases hyy with h | h
      · rw [h]; exact hint0
      · rw [h, smul_zero]; exact Submodule.zero_mem _
    set z := PE y with hz
    have hzfix : ∀ i, P i z = z := fun i => by rw [hz, ← hEP i y hyW, hyfix i]
    have hzR : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt := hE2 ▸ LinearMap.mem_range_self PE y
    have hzP : z ∈ Pol p r LL := by
      rw [pol_iff_eul] at hyP ⊢
      intro i
      rw [hz, ← hEeul i y hyW, hyP i, map_smul]
    have hzF : z ∈ FreeOf p v := by
      have h1 : resL p v 0 z = z := by rw [hz, ← hEres y hyW, resL_fix' v y hyF]
      rw [← h1]
      exact resL_free v z
    have hzX : z ∈ XSp p LL J M ρ := by
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzP, hzF⟩, (Submodule.mem_iInf _).mpr fun k => ?_⟩
      split_ifs with hk
      · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := typeProj_range_le_ycond LL K (T ⟨K, by omega⟩) (M k) (P ⟨K, by omega⟩)
            (hPlow ⟨K, by omega⟩ (by simp))
            (fun la hla => le_trans hla (hthrle ⟨K, by omega⟩ k (Or.inr ⟨le_rfl, hk⟩))) z
          rwa [hzfix] at h1
        · have h1 : z ∈ LinearMap.range (P ⟨K + 1, by omega⟩) := ⟨z, hzfix _⟩
          rw [(hPtop ⟨K + 1, by omega⟩ rfl).2.1] at h1
          exact (iSup₂_le fun la hla => le_iSup₂_of_le (f := fun (la : Fin r → ℤ)
            (_ : ((la 0 : ℤ) : WithTop ℤ) ≤ M k) => IsoC p LL (K + 1) (univ.erase ρ) la) la
            (le_trans hla (hthrle ⟨K + 1, by omega⟩ k (Or.inr ⟨Nat.le_succ K, hk⟩))) le_rfl) h1
      · have h1 := typeProj_range_le_ycond LL (J k) (T ⟨J k, by omega⟩) (M k) (P ⟨J k, by omega⟩)
          (hPlow ⟨J k, by omega⟩ (by simp; omega))
          (fun la hla => le_trans hla (hthrle ⟨J k, by omega⟩ k (Or.inl rfl))) z
        rwa [hzfix] at h1
    refine ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzX, (Submodule.mem_inf.mp hzR).1⟩,
      (Submodule.mem_inf.mp hzR).2⟩, ?_, ?_⟩
    · have h5 := hE5 _ hint (Wt.smul_mem _ hyW)
      rw [map_smul, smul_smul, ← pow_add] at h5
      rw [show (K + 1) * e1 = e1 + e1 * K by ring]
      exact h5
    · intro g hg
      obtain ⟨hg1, hgW⟩ := Submodule.mem_inf.mp hg
      obtain ⟨hgX, hgH⟩ := Submodule.mem_inf.mp hg1
      rw [hz, ← hE4 g y hgW hyW, hEfix g (Submodule.mem_inf.mpr ⟨hgH, hgW⟩)]
      exact lcomp_fock P hPsa g (hgfix g hgX) _ u
  · rw [show f m = 0 from if_neg hw]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, fun g hg => ?_⟩
    rw [fock_right_zero', fock_monomial_zero']
    intro hmg
    have hgW := (Submodule.mem_inf.mp hg).2
    rw [WtSpC, mem_restrictSupport_iff] at hgW
    exact hw (hgW (Finset.mem_coe.mpr hmg))

end Formalism.InvariantFactorPaths.L4
