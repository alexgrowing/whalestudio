import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Abs
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem proj_comm_abs' (PE A : V →ₗ[k] V) (R W L : Submodule k V) (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = R ⊓ W) (h3 : LinearMap.ker PE ⊓ W = L ⊓ W)
    (hR : ∀ x ∈ R, A x ∈ R) (hW : ∀ x ∈ W, A x ∈ W) (hL : ∀ x ∈ L, A x ∈ L) :
    ∀ x ∈ W, PE (A x) = A (PE x) := by
  intro x hx
  have hfix : ∀ y ∈ LinearMap.range PE, PE y = y := by
    rintro y ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, h1]
  have hPx : PE x ∈ R ⊓ W := by
    rw [← h2]
    exact LinearMap.mem_range_self PE x
  have hA1 : A (PE x) ∈ R ⊓ W := ⟨hR _ hPx.1, hW _ hPx.2⟩
  have hA1' : PE (A (PE x)) = A (PE x) := hfix _ (by rw [h2]; exact hA1)
  have hker : x - PE x ∈ LinearMap.ker PE ⊓ W := by
    refine ⟨LinearMap.mem_ker.mpr ?_, W.sub_mem hx hPx.2⟩
    rw [map_sub, ← LinearMap.comp_apply, h1, sub_self]
  rw [h3] at hker
  have hA2 : A (x - PE x) ∈ LinearMap.ker PE ⊓ W := by
    rw [h3]
    exact ⟨hL _ hker.1, hW _ hker.2⟩
  have h0 : PE (A (x - PE x)) = 0 := hA2.1
  rw [map_sub, map_sub, hA1', sub_eq_zero] at h0
  exact h0

end Abs

section EC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def lowIm' (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
    Submodule.map (glAct p LL j c d) ⊤

theorem lowIm_keep' (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) :
    ∀ x ∈ lowIm' p LL j ρ, A x ∈ lowIm' p LL j ρ := by
  have key : lowIm' p LL j ρ ≤ (lowIm' p LL j ρ).comap A := by
    unfold lowIm'
    refine iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_
    rintro y ⟨z, -, rfl⟩
    rw [Submodule.mem_comap, hA c hcd.1 d hcd.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hcd ⟨A z, Submodule.mem_top, rfl⟩))
  intro x hx
  exact key hx

theorem hwProj_comm' (LL : Letters N) (j : ℕ) (ρ : Fin r) (la : Fin r → ℤ)
    (PE A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la)
    (h3 : LinearMap.ker PE ⊓ WtSpC p LL j univ la = lowIm' p LL j ρ ⊓ WtSpC p LL j univ la)
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x))
    (hW : ∀ x ∈ WtSpC p LL j univ la, A x ∈ WtSpC p LL j univ la) :
    ∀ x ∈ WtSpC p LL j univ la, PE (A x) = A (PE x) := by
  have hsub : WtSpC p LL j univ la ≤ WtSpC p LL j (univ.erase ρ) la := by
    intro x hx
    simp only [WtSpC, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx ⊢
    intro m hm c _
    exact hx (show m ∈ (↑x.support : Set _) from hm) c (Finset.mem_univ c)
  have hR : ∀ x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la,
      A x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la := by
    intro x hx
    have hAx := hW x hx.2
    refine ⟨?_, hAx⟩
    have hx1 : x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d) := hx.1
    show A x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)
    rw [Submodule.mem_inf] at hx1 ⊢
    refine ⟨hsub hAx, ?_⟩
    have hx2 := hx1.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, hx2 c d hcd, map_zero]
  have h2' : LinearMap.range PE
      = (HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la) ⊓ WtSpC p LL j univ la := by
    rw [h2, inf_assoc, inf_idem]
  exact proj_comm_abs' PE A _ _ _ h1 h2' h3 hR hW (lowIm_keep' LL j ρ A hA)

theorem resL_fix' {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by
  have hx' : ↑x.support ⊆ {m : σ →₀ ℕ | m v = 0} := by
    have h' := hx
    simp only [FreeOf, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'
    exact h'
  change initPart v 0 x = x
  unfold initPart
  conv_rhs => rw [x.as_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [if_pos (show m v = 0 from hx' (Finset.mem_coe.mpr hm))]

theorem fock_monomial_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (hm : m ∉ g.support) :
    fock p g (monomial m 1) = 0 := by
  classical
  unfold fock
  refine Finset.sum_eq_zero (fun n hn => ?_)
  have hne : m ≠ n := fun h => hm (by rw [h]; exact hn)
  rw [MvPolynomial.coeff_monomial, if_neg hne, mul_zero, zero_mul]

theorem fock_right_zero' {σ : Type} (g : MvPolynomial σ ℚ_[p]) : fock p g 0 = 0 := by
  unfold fock
  simp

theorem monomial_mem_supp' {σ : Type} (Q : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ Q) :
    monomial m (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] Q := by
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply]
  intro n hn
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (show n ∈ (monomial m (1 : ℚ_[p])).support from hn))]
  exact hm

theorem cartan_comm_erase' (LL : Letters N) (j : ℕ) (ρ : Fin r) (a : Fin r) (ha : a ∈ univ.erase ρ) (b : Fin r)
    (hb : b ∈ univ.erase ρ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j ρ ρ (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j ρ ρ x) := by
  have h := glAct_comm (p := p) LL j ρ ρ a b x
  have hda : ¬ (ρ = a) := fun h => (Finset.mem_erase.mp ha).1 h.symm
  have hbc : ¬ (b = ρ) := (Finset.mem_erase.mp hb).1
  rw [if_neg hda, if_neg hbc, sub_zero, sub_eq_zero] at h
  exact h

end EC

private lemma mem_of_mem_support_restrictSupport {p : ℕ} [Fact p.Prime] {σ : Type} {Q : Set (σ →₀ ℕ)}
    {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ MvPolynomial.restrictSupport ℚ_[p] Q) {m : σ →₀ ℕ}
    (hm : m ∈ x.support) : m ∈ Q := by
  have h' := hx
  simp only [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported,
    Submodule.mem_comap, LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at h'
  exact h' hm

private lemma idempotent_apply_eq_self_of_mem_range {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : V →ₗ[k] V)
    (hQ : Q ∘ₗ Q = Q) : ∀ x ∈ LinearMap.range Q, Q x = x := by
  rintro x ⟨y, rfl⟩
  rw [← LinearMap.comp_apply, hQ]

private lemma idempotent_apply_eq_self_of_ker_eq_bot {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (Q : V →ₗ[k] V)
    (hQ : Q ∘ₗ Q = Q) (hk : LinearMap.ker Q = ⊥) : ∀ x, Q x = x := by
  intro x
  have h : x - Q x ∈ LinearMap.ker Q := by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hQ, sub_self]
  rw [hk, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

theorem highest_vector_projection : ProjX := by
  classical
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hP hE
  have h0ρ : (0 : Fin r) ≠ ρ := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_zero] at h'
    omega
  have h0e : (0 : Fin r) ∈ univ.erase ρ := Finset.mem_erase.mpr ⟨h0ρ, Finset.mem_univ _⟩
  obtain ⟨Tu, hTu⟩ : ∃ Tu : ℕ → Set (Fin r → ℤ),
      Tu = fun j => {la | ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := ⟨_, rfl⟩
  obtain ⟨Te, hTe⟩ : ∃ Te : Set (Fin r → ℤ),
      Te = {la | ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := ⟨_, rfl⟩
  have hTu' : ∀ j la, la ∈ Tu j ↔ ∀ k, min (J k) K = j → ((la 0 : ℤ) : WithTop ℤ) ≤ M k := by
    intro j la; rw [hTu]; rfl
  have hTe' : ∀ la, la ∈ Te ↔ ∀ k, K + 1 ≤ J k → ((la 0 : ℤ) : WithTop ℤ) ≤ M k := by
    intro la; rw [hTe]; rfl
  have hsatU : ∀ T : Set (Fin r → ℤ), CsSaturated (univ : Finset (Fin r)) T := by
    intro T la la' h
    have : la = la' := funext fun c => h c (Finset.mem_univ c)
    rw [this]
  have hsatE : CsSaturated (univ.erase ρ) Te := by
    intro la la' h
    have h0 : la 0 = la' 0 := h 0 h0e
    rw [hTe', hTe', h0]
  obtain ⟨hPex, hPcomm⟩ := hP
  choose Pu hPu using fun (j : ℕ) (hj : j ≤ K) => hPex j (by omega) univ (Or.inl rfl) (Tu j) (hsatU _)
  obtain ⟨Pe, hPe1, hPe2, hPe3⟩ := hPex (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl) Te hsatE
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), P = fun j => if h : j ≤ K then Pu j h else Pe := ⟨_, rfl⟩
  have hPu_eq : ∀ j (hj : j ≤ K), P j = Pu j hj := by intro j hj; rw [hPdef]; simp [hj]
  have hPe_eq : ∀ j, ¬ j ≤ K → P j = Pe := by intro j hj; rw [hPdef]; simp [hj]
  have hTPu : ∀ j (hj : j ≤ K), IsTypeProj p LL j univ (Tu j) (P j) := by
    intro j hj; rw [hPu_eq j hj]; exact (hPu j hj).1
  have hTPe : ∀ j, ¬ j ≤ K → IsTypeProj p LL (K + 1) (univ.erase ρ) Te (P j) := by
    intro j hj; rw [hPe_eq j hj]; exact hPe1
  have hPP : ∀ j x, P j (P j x) = P j x := by
    intro j x
    by_cases hj : j ≤ K
    · exact LinearMap.congr_fun (hTPu j hj).1 x
    · exact LinearMap.congr_fun (hTPe j hj).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    by_cases hj : j ≤ K <;> by_cases hj' : j' ≤ K
    · rcases le_total j j' with h | h
      · exact LinearMap.congr_fun (hPcomm j j' univ univ (Tu j) (Tu j') (P j) (P j') h subset_rfl
          (Or.inl rfl) (Or.inl rfl) (hTPu j hj) (hTPu j' hj')) x
      · exact (LinearMap.congr_fun (hPcomm j' j univ univ (Tu j') (Tu j) (P j') (P j) h subset_rfl
          (Or.inl rfl) (Or.inl rfl) (hTPu j' hj') (hTPu j hj)) x).symm
    · exact LinearMap.congr_fun (hPcomm j (K + 1) univ (univ.erase ρ) (Tu j) Te (P j) (P j') (by omega)
          (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j hj) (hTPe j' hj')) x
    · exact (LinearMap.congr_fun (hPcomm j' (K + 1) univ (univ.erase ρ) (Tu j') Te (P j') (P j) (by omega)
          (Finset.erase_subset _ _) (Or.inl rfl) (Or.inr rfl) (hTPu j' hj') (hTPe j hj)) x).symm
    · rw [hPe_eq j hj, hPe_eq j' hj']
  have hPsa : ∀ j F G, fock p (P j F) G = fock p F (P j G) := by
    intro j F G
    by_cases hj : j ≤ K
    · rw [hPu_eq j hj]; exact (hPu j hj).2.1 F G
    · rw [hPe_eq j hj]; exact hPe2 F G
  have hPint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin (K + 1) × Fin r) := by
    intro j F hF
    by_cases hj : j ≤ K
    · rw [hPu_eq j hj]; exact (hPu j hj).2.2 F hF
    · rw [hPe_eq j hj]; exact hPe3 F hF
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := by
    intro j x hx
    by_cases hj : j ≤ K
    · exact typeProj_polC LL j univ (Tu j) (P j) (hTPu j hj) x hx
    · exact typeProj_polC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) x hx
  have hPgl : ∀ j, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      P j (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P j x) := by
    intro j c hc d hd x
    by_cases hj : j ≤ K
    · exact typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c d x
    · exact typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc d hd x
  have hPdiag : ∀ j c x, P j (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P j x) := by
    intro j c x
    by_cases hj : j ≤ K
    · exact typeProj_comm_later LL j (K + 1) (by omega) (Tu j) (P j) (hTPu j hj) c c x
    · by_cases hc : c = ρ
      · rw [hc]
        exact typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (glAct p LL (K + 1) ρ ρ)
          (fun a ha b hb y => cartan_comm_erase' LL (K + 1) ρ a ha b hb y) x
      · have hc' : c ∈ univ.erase ρ := Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩
        exact typeProj_glActC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) c hc' c hc' x
  have hPws : ∀ j, ∀ x ∈ WtSpC p LL (K + 1) univ w, P j x ∈ WtSpC p LL (K + 1) univ w :=
    fun j => comm_wtsp LL (K + 1) (P j) (hPdiag j) w
  have hPres : ∀ j x, P j (resL p (Fin.last K, ρ) 0 x) = resL p (Fin.last K, ρ) 0 (P j x) := by
    intro j x
    by_cases hj : j ≤ K
    · refine typeProj_commC LL j univ (Tu j) (P j) (hTPu j hj) (resL p (Fin.last K, ρ) 0)
        (fun c _ d _ y => resL_glAct LL j c d (Fin.last K, ρ) 0 ?_ y) x
      intro i hi
      have hne : i ≠ Fin.last K := by
        intro h
        rw [h, Fin.val_last] at hi
        omega
      exact ⟨fun h => hne (Prod.ext_iff.mp h).1, fun h => hne (Prod.ext_iff.mp h).1⟩
    · refine typeProj_commC LL (K + 1) (univ.erase ρ) Te (P j) (hTPe j hj) (resL p (Fin.last K, ρ) 0)
        (fun c hc d hd y => resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 ?_ y) x
      intro i _
      exact ⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2,
        fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩
  obtain ⟨PE, hE1, hE2, hE3, hE4, hE5⟩ := hE (K + 1) le_rfl w
  have hPEc : ∀ A : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
        A (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (A x)) →
      (∀ x ∈ WtSpC p LL (K + 1) univ w, A x ∈ WtSpC p LL (K + 1) univ w) →
      ∀ x ∈ WtSpC p LL (K + 1) univ w, PE (A x) = A (PE x) :=
    fun A hA hW => hwProj_comm' LL (K + 1) ρ w PE A hE1 hE2 hE3 hA hW
  have hPEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w, PE g = g := by
    intro g hg
    exact idempotent_apply_eq_self_of_mem_range PE hE1 g (by rw [hE2]; exact hg)
  have hPEpol : ∀ y ∈ Pol p r LL ⊓ WtSpC p LL (K + 1) univ w, PE y ∈ Pol p r LL := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [pol_iff_eul] at hy1 ⊢
    intro i
    have hc := hPEc (ProjS.eulL (fun c : Fin r => (i, c)))
      (fun c _ d _ x => eul_glAct LL (K + 1) i c d x)
      (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i c c x) w) y hy2
    rw [← hc, hy1 i, map_smul]

  have hXH : ∀ g ∈ XH p LL J M ρ w, g ∈ Pol p r LL ∧ g ∈ FreeOf p (Fin.last K, ρ) ∧
      (∀ k, K + 1 ≤ J k → g ∈ YCond p LL K (M k) ∧ g ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧
      (∀ k, ¬ K + 1 ≤ J k → g ∈ YCond p LL (J k) (M k)) ∧
      g ∈ HWC p LL (K + 1) (univ.erase ρ) w ∧ g ∈ WtSpC p LL (K + 1) univ w := by
    intro g hg
    have hg' : g ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
        ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
          else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w := hg
    simp only [Submodule.mem_inf, Submodule.mem_iInf] at hg'
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hg'
    refine ⟨h1, h2, fun k hk => ?_, fun k hk => ?_, h4, h5⟩
    · have := h3 k
      rw [if_pos hk] at this
      exact Submodule.mem_inf.mp this
    · have := h3 k
      rw [if_neg hk] at this
      exact this
  have hYmin : ∀ g ∈ XH p LL J M ρ w, ∀ k, g ∈ YCond p LL (min (J k) K) (M k) := by
    intro g hg k
    obtain ⟨-, -, h3, h4, -⟩ := hXH g hg
    by_cases hk : K + 1 ≤ J k
    · rw [show min (J k) K = K by omega]; exact (h3 k hk).1
    · rw [show min (J k) K = J k by omega]; exact h4 k hk

  have hPg : ∀ g ∈ XH p LL J M ρ w, ∀ j, P j g = g := by
    intro g hg j
    obtain ⟨hgP, -, hgT, -, -, -⟩ := hXH g hg
    by_cases hj : j ≤ K
    · by_cases hex : ∃ k, min (J k) K = j
      · obtain ⟨k, hk⟩ := hex
        obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image (univ.filter fun k => min (J k) K = j) M
          ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
        have hk0' : min (J k0) K = j := (Finset.mem_filter.mp hk0).2
        refine ycond_fix LL j (Tu j) (M k0) (P j) (hTPu j hj) (fun la hla => ?_) g ⟨?_, hgP⟩
        · rw [hTu']
          intro k' hk'
          exact hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))
        · have := hYmin g hg k0
          rwa [hk0'] at this
      · refine idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPu j hj).1 ?_ g
        rw [(hTPu j hj).2.2]
        refine le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le
        rw [hTu']
        intro k hk
        exact absurd ⟨k, hk⟩ hex
    · by_cases hex : ∃ k, K + 1 ≤ J k
      · obtain ⟨k, hk⟩ := hex
        obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image (univ.filter fun k => K + 1 ≤ J k) M
          ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
        have hk0' : K + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
        refine idempotent_apply_eq_self_of_mem_range (P j) (hTPe j hj).1 g ?_
        rw [(hTPe j hj).2.1]
        have hgt := (hgT k0 hk0').2
        unfold TypesLE at hgt
        refine SetLike.le_def.mp (iSup_le fun la => iSup_le fun hla => ?_) hgt
        refine le_iSup₂_of_le (f := fun la (_ : la ∈ Te) => IsoC p LL (K + 1) (univ.erase ρ) la) la ?_ le_rfl
        rw [hTe']
        intro k' hk'
        exact hla.trans (hmin k' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩))
      · refine idempotent_apply_eq_self_of_ker_eq_bot (P j) (hTPe j hj).1 ?_ g
        rw [(hTPe j hj).2.2]
        refine le_antisymm (iSup_le fun la => iSup_le fun hla => absurd ?_ hla) bot_le
        rw [hTe']
        intro k hk
        exact absurd ⟨k, hk⟩ hex

  obtain ⟨G, hG⟩ : ∃ G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      G = fun u => resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) u)) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      f = fun m => if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then G (monomial m 1) else 0 :=
    ⟨_, rfl⟩
  refine ⟨(MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, ?_⟩
  intro m hm hm0
  have hPr : (MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m := by
    have h := (MvPolynomial.basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m
    rwa [MvPolynomial.coe_basisMonomials] at h
  rw [hPr]
  by_cases hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c
  swap
  · have h0 : f m = 0 := by rw [hf]; exact if_neg hw
    rw [h0, smul_zero]
    refine ⟨zero_mem _, zero_mem _, fun g hg => ?_⟩
    rw [fock_right_zero', fock_monomial_zero']
    intro hmg
    obtain ⟨-, -, -, -, -, hgw⟩ := hXH g hg
    exact hw (mem_of_mem_support_restrictSupport hgw hmg)
  have hfm : f m = resL p (Fin.last K, ρ) 0 (PE (lcomp P (List.range (K + 2)) (monomial m 1))) := by
    rw [hf, hG]; exact if_pos hw
  rw [hfm]

  have hu_pol : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ Pol p r LL :=
    monomial_mem_supp' {m | MultiDeg LL m} m hm
  have hu_ws : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ WtSpC p LL (K + 1) univ w :=
    monomial_mem_supp' _ m hw
  have hu_int : (monomial m 1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ IntPol p (Fin (K + 1) × Fin r) := by
    rw [intPol_iff_norm]
    intro n
    rw [MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  set y := lcomp P (List.range (K + 2)) (monomial m 1) with hy
  have hy_ws : y ∈ WtSpC p LL (K + 1) univ w :=
    lcomp_keep P (WtSpC p LL (K + 1) univ w : Set _) _ (fun j _ u hu => hPws j u hu) _ hu_ws
  have hy_pol : y ∈ Pol p r LL :=
    lcomp_keep P (Pol p r LL : Set _) _ (fun j _ u hu => hPpol j u hu) _ hu_pol
  have hy_fix : ∀ j, j ≤ K + 1 → P j y = y := fun j hj =>
    lcomp_fix P hPP hcomm _ j (List.mem_range.mpr (by omega)) _
  set z := PE y with hz
  have hz_rng : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w := by
    rw [← hE2]; exact LinearMap.mem_range_self PE y
  have hz_pol : z ∈ Pol p r LL := hPEpol y ⟨hy_pol, hy_ws⟩
  have hz_fix : ∀ j, j ≤ K + 1 → P j z = z := by
    intro j hj
    rw [hz, ← hPEc (P j) (hPgl j) (hPws j) y hy_ws, hy_fix j hj]
  set x := resL p (Fin.last K, ρ) 0 z with hx
  have hx_fix : ∀ j, j ≤ K + 1 → P j x = x := by
    intro j hj
    rw [hx, hPres, hz_fix j hj]

  have hx_pol : x ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 {m | MultiDeg LL m} z hz_pol
  have hx_free : x ∈ FreeOf p (Fin.last K, ρ) := resL_free _ z
  have hx_ws : x ∈ WtSpC p LL (K + 1) univ w := resL_keep_supp _ 0 _ z hz_rng.2
  have hres : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ u,
      resL p (Fin.last K, ρ) 0 (glAct p LL (K + 1) c d u) = glAct p LL (K + 1) c d (resL p (Fin.last K, ρ) 0 u) := by
    intro c hc d hd u
    refine resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ => ?_) u
    exact ⟨fun h => (Finset.mem_erase.mp hc).1 (Prod.ext_iff.mp h).2,
      fun h => (Finset.mem_erase.mp hd).1 (Prod.ext_iff.mp h).2⟩
  have hx_hwc : x ∈ HWC p LL (K + 1) (univ.erase ρ) w := by
    have hzh : z ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d),
          LinearMap.ker (glAct p LL (K + 1) c d) := hz_rng.1
    show x ∈ WtSpC p LL (K + 1) (univ.erase ρ) w ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d),
          LinearMap.ker (glAct p LL (K + 1) c d)
    rw [Submodule.mem_inf] at hzh ⊢
    refine ⟨resL_keep_supp _ 0 _ z hzh.1, ?_⟩
    have h2 := hzh.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro c d hcd
    rw [hx, ← hres c hcd.1 d hcd.2.1 z, h2 c d hcd, map_zero]
  have hxY : ∀ k, x ∈ YCond p LL (min (J k) K) (M k) := by
    intro k
    rw [← hx_fix (min (J k) K) (by omega)]
    exact typeProj_range_le_ycond LL _ (Tu _) (M k) (P _) (hTPu _ (by omega))
      (fun la hla => (hTu' _ la).mp hla k rfl) x
  have hxT : ∀ k, K + 1 ≤ J k → x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k) := by
    intro k hk
    have h1 : x ∈ ⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la := by
      rw [← (hTPe (K + 1) (by omega)).2.1, ← hx_fix (K + 1) le_rfl]
      exact LinearMap.mem_range_self _ x
    have hle : (⨆ (la : Fin r → ℤ) (_ : la ∈ Te), IsoC p LL (K + 1) (univ.erase ρ) la)
        ≤ TypesLE p LL (K + 1) (univ.erase ρ) (M k) := by
      unfold TypesLE
      exact iSup₂_le fun la hla => le_iSup₂_of_le la ((hTe' la).mp hla k hk) le_rfl
    exact hle h1
  refine ⟨?_, ?_, ?_⟩
  · show x ∈ ((Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
        ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
          else YCond p LL (J k) (M k))) ⊓ HWC p LL (K + 1) (univ.erase ρ) w) ⊓ WtSpC p LL (K + 1) univ w
    refine ⟨⟨⟨⟨hx_pol, hx_free⟩, ?_⟩, hx_hwc⟩, hx_ws⟩
    apply (Submodule.mem_iInf _).mpr
    intro k
    split_ifs with hk
    · have h1 := hxY k
      rw [show min (J k) K = K by omega] at h1
      exact ⟨h1, hxT k hk⟩
    · have h1 := hxY k
      rwa [show min (J k) K = J k by omega] at h1
  · have hyZ := lcomp_int LL e1 P hPpol hPint (List.range (K + 2)) (monomial m 1) ⟨hu_pol, hu_int⟩
    rw [List.length_range] at hyZ
    have hzI := hE5 _ hyZ (Submodule.smul_mem _ _ hy_ws)
    rw [map_smul, smul_smul, ← pow_add] at hzI
    have hxI := initPart_int (Fin.last K, ρ) 0 _ hzI
    have he : ((p : ℚ_[p]) ^ ((K + 3) * e1)) • x
        = resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (e1 + e1 * (K + 2))) • z) := by
      rw [map_smul, hx, show (K + 3) * e1 = e1 + e1 * (K + 2) by ring]
    rw [he]
    exact hxI
  · intro g hg
    obtain ⟨-, hgF, -, -, hgH, hgW⟩ := hXH g hg
    have f1 : fock p g x = fock p g z := by
      rw [hx]
      unfold fock
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have h1 : (resL p (Fin.last K, ρ) 0 z).coeff n = z.coeff n := by
        show (initPart (Fin.last K, ρ) 0 z).coeff n = _
        rw [coeff_initPart, if_pos (show n (Fin.last K, ρ) = 0 from mem_of_mem_support_restrictSupport hgF hn)]
      rw [h1]
    have f2 : fock p g z = fock p g y := by
      rw [hz, ← hE4 g y hgW hy_ws, hPEfix g ⟨hgH, hgW⟩]
    have f3 : fock p g y = fock p g (monomial m 1) := lcomp_fock P hPsa g (hPg g hg) _ _
    rw [f1, f2, f3]

end Formalism.InvariantFactorPaths.L4
