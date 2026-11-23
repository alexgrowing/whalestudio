import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open Filter PeriodPair Polynomial
open scoped Topology

noncomputable section

namespace GlobalTheory

variable (L : PeriodPair)

private lemma exists_polynomial_weierstrass (n : ℕ) : ∀ (g h : ℂ → ℂ),
    (∀ z ∉ L.lattice, DifferentiableAt ℂ g z) → (∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) →
    (∀ z, g (-z) = g z) → AnalyticAt ℂ h 0 → (∀ᶠ z in 𝓝[≠] 0, h z = z ^ (2 * n) * g z) →
    ∃ A : ℂ[X], ∀ z ∉ L.lattice, g z = A.eval (℘[L] z) := by
  induction n with
  | zero =>
    intro g h hd hp _ hh he
    simp only [mul_zero, pow_zero, one_mul] at he
    classical
    let G : ℂ → ℂ := fun z => if z ∈ L.lattice then h 0 else g z
    have hG : Differentiable ℂ G := by
      intro z
      by_cases hz : z ∈ L.lattice
      · have ht : Tendsto (fun w : ℂ => w - z) (𝓝[≠] z) (𝓝[≠] 0) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have h0 : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 (z - z)) := tendsto_id.sub_const z
            rw [sub_self] at h0
            exact h0.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with w hw using sub_ne_zero.mpr hw
        have h1 : ∀ᶠ w in 𝓝[≠] z, G w = h (w - z) := by
          filter_upwards [ht.eventually he, eventually_ne_notMem_periodLattice L z] with w hw hw'
          simp only [G, if_neg hw']
          rw [hw, ← hp (w - z) z hz, sub_add_cancel]
        have h2 : G =ᶠ[𝓝 z] h ∘ fun w => w - z := by
          rw [eventually_nhdsWithin_iff] at h1
          filter_upwards [h1] with w hw
          by_cases hwz : w = z
          · subst hwz
            simp [G, hz]
          · exact hw hwz
        have h3 : DifferentiableAt ℂ h ((fun w : ℂ => w - z) z) := by
          simp only [sub_self]
          exact hh.differentiableAt
        have h4 : DifferentiableAt ℂ (fun w : ℂ => w - z) z := differentiableAt_id.sub_const z
        exact (DifferentiableAt.comp (g := h) (f := fun w : ℂ => w - z) z h3 h4).congr_of_eventuallyEq h2
      · have h1 : G =ᶠ[𝓝 z] g := by
          filter_upwards [eventually_notMem_periodLattice L hz] with w hw
          simp [G, hw]
        exact (hd z hz).congr_of_eventuallyEq h1
    have hGp : ∀ z, ∀ l ∈ L.lattice, G (z + l) = G z := by
      intro z l hl
      by_cases hz : z ∈ L.lattice
      · have : z + l ∈ L.lattice := L.lattice.add_mem hz hl
        simp [G, hz, this]
      · have : z + l ∉ L.lattice := fun h' => hz (by simpa using L.lattice.sub_mem h' hl)
        simp [G, hz, this, hp z l hl]
    refine ⟨C (G 0), fun z hz => ?_⟩
    rw [eval_C, ← eq_of_differentiable_of_periodic L hG hGp z 0]
    simp [G, hz]
  | succ n ih =>
    intro g h hd hp hev hh he
    let q : ℂ → ℂ := fun z => z ^ 2 * L.weierstrassPExcept 0 z + 1
    have hq : AnalyticAt ℂ q 0 := by
      have := L.analyticAt_weierstrassPExcept 0
      fun_prop
    have hq_eq : ∀ z, z ≠ 0 → z ^ 2 * ℘[L] z = q z := by
      intro z hz
      have h1 := L.weierstrassPExcept_add (0 : L.lattice) z
      have h0 : ((0 : L.lattice) : ℂ) = 0 := rfl
      rw [h0, sub_zero] at h1
      rw [← h1]
      simp only [q, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero]
      rw [mul_add, mul_one_div_cancel (pow_ne_zero 2 hz)]
    have hE : ∀ z, L.weierstrassPExcept 0 (-z) = L.weierstrassPExcept 0 z := fun z => by
      rw [L.weierstrassPExcept_neg, neg_zero]
    have hqn : ∀ z, q (-z) = q z := fun z => by simp only [q, hE, neg_sq]
    let k : ℂ → ℂ := fun z => h z - h 0 * q z ^ (n + 1)
    have hk : AnalyticAt ℂ k 0 := by fun_prop
    have hk0 : k 0 = 0 := by simp [k, q]
    have hhe : ∀ᶠ z in 𝓝[≠] 0, h (-z) = h z := by
      have ht : Tendsto (fun z : ℂ => -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h0 : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 (-0)) := tendsto_id.neg
          rw [neg_zero] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz using neg_ne_zero.mpr hz
      filter_upwards [he, ht.eventually he] with z h1 h2
      rw [h2, h1, hev, Even.neg_pow (even_two_mul _)]
    have hkev : ∀ᶠ z in 𝓝 0, k (-z) = k z := by
      rw [eventually_nhdsWithin_iff] at hhe
      filter_upwards [hhe] with z hz
      by_cases hz0 : z = 0
      · subst hz0
        simp
      · simp only [k, hqn, hz hz0]
    have hkd : deriv k 0 = 0 := by
      have h1 : deriv (fun z => k (-z)) 0 = deriv k 0 := Filter.EventuallyEq.deriv_eq hkev
      rw [deriv_comp_neg, neg_zero] at h1
      linear_combination -h1 / 2
    have hkfac : ∀ z, k z = z ^ 2 * dslope (dslope k 0) 0 z := by
      intro z
      have e1 := sub_smul_dslope k 0 z
      have e2 := sub_smul_dslope (dslope k 0) 0 z
      rw [dslope_same k 0, hkd] at e2
      rw [hk0] at e1
      simp only [sub_zero, smul_eq_mul] at e1 e2
      rw [← e1, ← e2]
      ring
    have hm : AnalyticAt ℂ (dslope (dslope k 0) 0) 0 := by
      have hs : {z | AnalyticAt ℂ k z} ∈ 𝓝 (0 : ℂ) := hk.eventually_analyticAt
      have hso : IsOpen {z | AnalyticAt ℂ k z} := isOpen_analyticAt ℂ k
      have hks : DifferentiableOn ℂ k {z | AnalyticAt ℂ k z} :=
        fun z hz => hz.differentiableAt.differentiableWithinAt
      have d2 := (Complex.differentiableOn_dslope hs).mpr ((Complex.differentiableOn_dslope hs).mpr hks)
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hs] with z hz using d2.differentiableAt (hso.mem_nhds hz)
    obtain ⟨A', hA'⟩ := ih (fun z => g z - h 0 * ℘[L] z ^ (n + 1)) (dslope (dslope k 0) 0)
      (fun z hz => (hd z hz).sub
        ((hasDerivAt_weierstrassP L hz).differentiableAt.pow (n + 1) |>.const_mul (h 0)))
      (fun z l hl => by
        have h℘ : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
        simp only [hp z l hl, h℘])
      (fun z => by simp only [hev, L.weierstrassP_neg])
      hm
      (by
        filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
        have hz0' : z ≠ 0 := hz0
        apply mul_left_cancel₀ (pow_ne_zero 2 hz0')
        rw [← hkfac z]
        simp only [k]
        rw [hz, ← hq_eq z hz0']
        ring)
    refine ⟨A' + C (h 0) * X ^ (n + 1), fun z hz => ?_⟩
    have := hA' z hz
    rw [eval_add, eval_mul, eval_C, eval_pow, eval_X, ← this]
    ring

theorem exists_eq_polynomial_weierstrassP {g : ℂ → ℂ} (h0 : MeromorphicAt g 0)
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z) (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z)
    (hev : ∀ z, g (-z) = g z) : ∃ A : ℂ[X], ∀ z ∉ L.lattice, g z = A.eval (℘[L] z) := by
  obtain ⟨N, hN⟩ := h0
  refine exists_polynomial_weierstrass L N g (fun z => z ^ (2 * N) * g z) hd hp hev ?_
    (Eventually.of_forall fun z => rfl)
  have : (fun z => z ^ (2 * N) * g z) = fun z => z ^ N * ((z - 0) ^ N • g z) := by
    funext z
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [this]
  exact (analyticAt_id.pow N).mul hN

theorem exists_mul_eq_polynomial_weierstrassP {f : ℂ → ℂ} (hf : Meromorphic f)
    (hp : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) (hev : ∀ z, f (-z) = f z) :
    ∃ A D : ℂ[X], D.Monic ∧ ∀ z ∉ L.lattice, f z * D.eval (℘[L] z) = A.eval (℘[L] z) := by
  classical
  have hK : IsCompact (closure (ZSpan.fundamentalDomain L.basis)) :=
    (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  have hBc : IsClosed {z | ¬ AnalyticAt ℂ f z} := (isOpen_analyticAt ℂ f).isClosed_compl
  have hfin : (closure (ZSpan.fundamentalDomain L.basis) ∩ {z | ¬ AnalyticAt ℂ f z}).Finite := by
    refine (hK.inter_right hBc).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    intro x _
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [(hf x).eventually_analyticAt] with y hy
    exact fun hyS => hyS.2 hy
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, ∀ a, a ∈ S ↔
      a ∈ closure (ZSpan.fundamentalDomain L.basis) ∩ {z | ¬ AnalyticAt ℂ f z} :=
    ⟨hfin.toFinset, fun a => hfin.mem_toFinset⟩
  choose n hn using hf
  let D : ℂ[X] := ∏ a ∈ S, (X - C (℘[L] a)) ^ (n a + 1)
  have hD : D.Monic := monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow _
  let g : ℂ → ℂ := fun z => f z * D.eval (℘[L] z)
  have h℘d : ∀ z ∉ L.lattice, DifferentiableAt ℂ ℘[L] z :=
    fun z hz => (hasDerivAt_weierstrassP L hz).differentiableAt
  have hPd : ∀ (p : ℂ[X]) (z : ℂ), z ∉ L.lattice → DifferentiableAt ℂ (fun w => p.eval (℘[L] w)) z :=
    fun p z hz => (p.differentiableAt (x := ℘[L] z)).comp z (h℘d z hz)
  have hPm : ∀ p : ℂ[X], MeromorphicAt (fun w => p.eval (℘[L] w)) 0 := by
    intro p
    have h℘m := L.meromorphic_weierstrassP 0
    refine Polynomial.induction_on (motive := fun p => MeromorphicAt (fun w => p.eval (℘[L] w)) 0)
      p ?_ ?_ ?_
    · intro a
      simp
    · intro p q hp hq
      simp only [eval_add]
      exact hp.add hq
    · intro k a _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      fun_prop
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := by
    intro z l hl
    have h℘ : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
    simp only [g, hp z l hl, h℘]
  have hgev : ∀ z, g (-z) = g z := fun z => by simp only [g, hev, L.weierstrassP_neg]
  have hgS : ∀ a ∈ S, a ∉ L.lattice → DifferentiableAt ℂ g a := by
    intro a ha hal
    have hψ : DifferentiableAt ℂ (dslope ℘[L] a) a := by
      have hs : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 a := L.isClosed_lattice.isOpen_compl.mem_nhds hal
      exact ((Complex.differentiableOn_dslope hs).mpr L.differentiableOn_weierstrassP).differentiableAt hs
    have hDR : D = (X - C (℘[L] a)) ^ (n a + 1) * ∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1) :=
      (Finset.mul_prod_erase S (fun b => (X - C (℘[L] b)) ^ (n b + 1)) ha).symm
    have hfun : g = fun w => (w - a) * ((w - a) ^ (n a) • f w) * (dslope ℘[L] a w) ^ (n a + 1) *
        (∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1)).eval (℘[L] w) := by
      funext w
      have e := sub_smul_dslope ℘[L] a w
      rw [smul_eq_mul] at e
      simp only [g, hDR, eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [← e, mul_pow]
      ring
    rw [hfun]
    have h1 := (hn a).differentiableAt
    have h3 := hPd (∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1)) a hal
    have h0 : DifferentiableAt ℂ (fun w : ℂ => w - a) a := differentiableAt_id.sub_const a
    exact ((h0.mul h1).mul (hψ.pow _)).mul h3
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := by
    intro z hz
    by_cases hfa : AnalyticAt ℂ f z
    · exact hfa.differentiableAt.mul (hPd D z hz)
    obtain ⟨a, l, hlL, rfl, haK⟩ : ∃ a l, l ∈ L.lattice ∧ z = a + l ∧
        a ∈ closure (ZSpan.fundamentalDomain L.basis) :=
      ⟨ZSpan.fract L.basis z, ZSpan.floor L.basis z,
        by rw [L.lattice_eq_span_range_basis]; exact (ZSpan.floor L.basis z).2,
        by rw [ZSpan.fract_apply]; ring,
        subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z)⟩
    have hal : a ∉ L.lattice := fun h => hz (L.lattice.add_mem h hlL)
    have haB : ¬ AnalyticAt ℂ f a := by
      intro hfa'
      apply hfa
      have htf : (fun w => f (w - l)) = f := funext fun w => by
        have := hp (w - l) l hlL
        rw [sub_add_cancel] at this
        exact this.symm
      rw [← htf]
      have h2 : AnalyticAt ℂ (fun w : ℂ => w - l) (a + l) := by fun_prop
      exact hfa'.comp_of_eq h2 (by simp)
    have haS : a ∈ S := (hS a).mpr ⟨haK, haB⟩
    have hga := hgS a haS hal
    have htr : g = fun w => g (w - l) := funext fun w => by
      have := hgp (w - l) l hlL
      rw [sub_add_cancel] at this
      exact this
    rw [htr]
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - l) (a + l) := differentiableAt_id.sub_const l
    have h3 : DifferentiableAt ℂ g ((fun w : ℂ => w - l) (a + l)) := by simpa using hga
    exact DifferentiableAt.comp (g := g) (f := fun w : ℂ => w - l) (a + l) h3 h2
  have hg0 : MeromorphicAt g 0 := (show MeromorphicAt f 0 from ⟨n 0, hn 0⟩).mul (hPm D)
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hg0 hgd hgp hgev
  exact ⟨A, D, hD, hA⟩

end GlobalTheory
