import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.PartnerDeterminantHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictionMinMaxIntHolds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {σ : Type}

private theorem coeff_initPart_eq_ite (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (n : σ →₀ ℕ) :
    coeff n (initPart v e f) = if n v = e then coeff n f else 0 := by
  classical
  unfold initPart
  rw [coeff_sum]
  simp only [apply_ite (coeff n), coeff_monomial, coeff_zero]
  rw [Finset.sum_eq_single n]
  · by_cases h : n v = e <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro hn
    have h0 : coeff n f = 0 := by simpa [mem_support_iff] using hn
    simp [h0]

theorem p_pow_ne_zero (n : ℕ) : ((p : ℚ_[p]) ^ n) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

noncomputable def strip (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun f := (initPart v e f).divMonomial (Finsupp.single v e)
  map_add' x y := by
    rw [initPart_add]; ext m; simp only [coeff_divMonomial, coeff_add]
  map_smul' a x := by
    rw [initPart_smul]; ext m; simp only [coeff_divMonomial, coeff_smul, RingHom.id_apply]

theorem coeff_strip (v : σ) (e : ℕ) (n : σ →₀ ℕ) (f : MvPolynomial σ ℚ_[p]) :
    coeff n (strip p v e f) = if n v = 0 then coeff (Finsupp.single v e + n) f else 0 := by
  classical
  show coeff n ((initPart v e f).divMonomial (Finsupp.single v e)) = _
  rw [coeff_divMonomial, coeff_initPart_eq_ite]
  by_cases h : n v = 0 <;> simp [h]

theorem strip_monomial_ne (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v ≠ e) :
    strip p v e (monomial m 1) = 0 := by
  classical
  ext n
  rw [coeff_strip, coeff_zero]
  split_ifs with h
  · rw [coeff_monomial, if_neg]
    rintro rfl
    apply hm
    simp [h]
  · rfl

theorem strip_monomial_eq (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    strip p v e (monomial (Finsupp.single v e + m) 1) = monomial m 1 := by
  classical
  ext n
  rw [coeff_strip, coeff_monomial, coeff_monomial]
  by_cases h1 : n v = 0
  · rw [if_pos h1]
    by_cases h2 : m = n
    · subst h2
      simp
    · rw [if_neg h2, if_neg]
      intro h3
      exact h2 (add_left_cancel h3)
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 hm

theorem monomial_single_add (v : σ) (e : ℕ) (m : σ →₀ ℕ) :
    (monomial (Finsupp.single v e + m) 1 : MvPolynomial σ ℚ_[p]) = X v ^ e * monomial m 1 := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

private theorem prod_factorial_single_add_eq_mul (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    ((Finsupp.single v e + m).prod fun _ k => (k.factorial : ℚ_[p])) =
      (e.factorial : ℚ_[p]) * m.prod fun _ k => (k.factorial : ℚ_[p]) := by
  classical
  have hdisj : Disjoint (Finsupp.single v e).support m.support := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' := Finsupp.support_single_subset ha
    rw [Finset.mem_singleton] at ha'
    subst ha'
    exact (Finsupp.mem_support_iff.mp hb) hm
  rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]

private theorem fock_eq_sum_coeff_mul_factorial (F G : MvPolynomial σ ℚ_[p]) (S : Finset (σ →₀ ℕ)) (hS : F.support ⊆ S) :
    fock p F G = ∑ m ∈ S, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  unfold fock
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa [mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fock_eq_zero_of (F G : MvPolynomial σ ℚ_[p]) (h : ∀ m, coeff m F = 0 ∨ coeff m G = 0) : fock p F G = 0 := by
  unfold fock
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases h m with h1 | h1 <;> simp [h1]

theorem coeff_pow_mul_ne (v : σ) (e : ℕ) (y : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) (m : σ →₀ ℕ)
    (hm : m v ≠ e) : coeff m (X v ^ e * y) = 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [one_mul]
    by_contra hc
    have hmem : (m - Finsupp.single v e) ∈ y.support := mem_support_iff.mpr hc
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    have h0 : (m - Finsupp.single v e) v = 0 := hy (Finset.mem_coe.mpr hmem)
    have hle : Finsupp.single v e v ≤ m v := (Finsupp.le_def.1 h) v
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at h0 hle
    omega
  · rfl

theorem fock_pow_mul (v : σ) (e : ℕ) (y z : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) :
    fock p (X v ^ e * y) (X v ^ e * z) = (e.factorial : ℚ_[p]) * fock p y z := by
  classical
  have hy' : ∀ m ∈ y.support, m v = 0 := by
    intro m hm
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    exact hy (Finset.mem_coe.mpr hm)
  have hcoeff : ∀ (u : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ),
      coeff (Finsupp.single v e + m) (X v ^ e * u) = coeff m u := by
    intro u m
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
  have hsub : (X v ^ e * y).support ⊆ y.support.image (fun m => Finsupp.single v e + m) := by
    intro m hm
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
    split_ifs at hm with h
    · rw [Finset.mem_image]
      refine ⟨m - Finsupp.single v e, mem_support_iff.mpr (by simpa using hm), ?_⟩
      exact add_tsub_cancel_of_le h
    · exact absurd rfl hm
  rw [fock_eq_sum_coeff_mul_factorial _ _ _ hsub, Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hcoeff, hcoeff, prod_factorial_single_add_eq_mul v e m (hy' m hm)]
  ring

end Gen

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem xH_le_free (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hy : y ∈ XH p LL J M ρ w) :
    y ∈ FreeOf p (Fin.last K, ρ) := by
  unfold XH XSp at hy
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1).1).2

private theorem exists_prime_pow_smul_mem_intPol {τ : Type} (x : MvPolynomial τ ℚ_[p]) :
    ∃ n : ℕ, ((p : ℚ_[p]) ^ n) • x ∈ IntPol p τ := by
  classical
  refine MvPolynomial.induction_on' x (fun u a => ?_) (fun f g hf hg => ?_)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖a‖
      (show (1 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine ⟨n, ?_⟩
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hpos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp0 n
    have hle : ‖(p : ℚ_[p]) ^ n * a‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      calc ((p : ℝ) ^ n)⁻¹ * ‖a‖ ≤ ((p : ℝ) ^ n)⁻¹ * (p : ℝ) ^ n := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    unfold IntPol
    rw [LinearMap.mem_range]
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], (c : ℚ_[p]) = (p : ℚ_[p]) ^ n * a := ⟨⟨_, hle⟩, rfl⟩
    refine ⟨monomial u c, ?_⟩
    rw [smul_monomial, smul_eq_mul, ← hc]
    show MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) _ = _
    rw [map_monomial]
    rfl
  · obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    refine ⟨a + b, ?_⟩
    have key : ((p : ℚ_[p]) ^ (a + b)) • (f + g) =
        ((p : ℤ_[p]) ^ b) • (((p : ℚ_[p]) ^ a) • f) + ((p : ℤ_[p]) ^ a) • (((p : ℚ_[p]) ^ b) • g) := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ b) (((p : ℚ_[p]) ^ a) • f),
        ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ a) (((p : ℚ_[p]) ^ b) • g)]
      simp only [map_pow, map_natCast, smul_smul, smul_add, ← pow_add, add_comm b a]
    rw [key]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem resOntoK_of_resSat (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (h : ResSat p LL J M ρ) : ResOntoK p LL J M ρ := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_prime_pow_smul_mem_intPol (p := p) x
  obtain ⟨h', hY, -, hinit⟩ := h _ (Submodule.smul_mem _ _ hx) hn
  refine ⟨((p : ℚ_[p]) ^ n)⁻¹ • h', Submodule.smul_mem _ _ hY, ?_⟩
  rw [initPart_smul, hinit, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul]

theorem grSpan_eq (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ grSpan p LLw J M ρ w e ↔
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * y := by
  have hMM := restriction_min_max_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hr hρ hv hP hE hO
  have hGr := graded_eq_holds p K r LLw J M ρ w e hv he
  constructor
  · intro hx
    have hle : grSpan p LLw J M ρ w e ≤
        (XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
          (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
      unfold grSpan
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨h, hh, rfl⟩ := (hGr z).mp hz
      refine Submodule.mem_map.mpr ⟨initPart (Fin.last K, ρ) 0 h, (hMM _).mpr ⟨h, ?_, rfl⟩, rfl⟩
      exact (Submodule.mem_inf.mp hh).1
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hle hx)
    exact ⟨y, hy, hyx.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := (hMM y).mp hy
    obtain ⟨n, hn⟩ := exists_pow_smul_intPol h
    have h1 : ((p : ℚ_[p]) ^ n) • h ∈
        MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ hh, hn⟩
    have h2 : X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ n) • h) ∈
        grSpan p LLw J M ρ w e := Submodule.subset_span ((hGr _).mpr ⟨_, h1, rfl⟩)
    have h3 := (grSpan p LLw J M ρ w e).smul_mem (((p : ℚ_[p]) ^ n)⁻¹) h2
    rwa [initPart_smul, mul_smul_comm, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul] at h3

end Last

theorem saturation_at_holds : SatAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 hr hρ hv he hP hE hS x hx hxI
  obtain ⟨y, hy, rfl⟩ := (grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSat _ J _ ρ hS) x).mp hx
  rw [pow_mul_int_iff] at hxI
  obtain ⟨h, hh, hres⟩ := restriction_min_max_int_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 hr hρ hv hP hE hS y hy hxI
  refine (graded_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, ?_⟩
  rw [hres, mul_smul_comm]

theorem projAtOf_of (hX : ProjX) : ProjAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 h1 h2 h3 h5 h6
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  have hgr := grSpan_eq LLw J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  have hfree : ∀ g ∈ grSpan p LLw J M ρ w e,
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        y ∈ FreeOf p (Fin.last K, ρ) ∧ g = X (Fin.last K, ρ) ^ e * y := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hgr g).mp hg
    exact ⟨y, hy, xH_le_free _ J _ ρ _ y hy, rfl⟩
  by_cases hme : m (Fin.last K, ρ) = e
  · have hle : Finsupp.single (Fin.last K, ρ) e ≤ m := by
      rw [Finsupp.single_le_iff]
      exact hme.ge
    obtain ⟨m', hm'v, hmm⟩ : ∃ m' : Fin (K + 1) × Fin r →₀ ℕ, m' (Fin.last K, ρ) = 0 ∧
        m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, by simp [hme], (add_tsub_cancel_of_le hle).symm⟩
    subst hmm
    have hMD : MultiDeg (setLast LLw (LLw.deg (Fin.last K) - e)) m' := by
      unfold MultiDeg at hm ⊢
      intro i
      have hi := hm i
      change _ = Function.update LLw.deg (Fin.last K) (LLw.deg (Fin.last K) - e) i
      rw [Function.update_apply]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
        Prod.mk.injEq] at hi
      by_cases hik : i = Fin.last K
      · subst hik
        simp at hi
        rw [if_pos rfl]
        omega
      · have hik' : ¬ Fin.last K = i := fun h => hik h.symm
        simp [hik'] at hi
        rw [if_neg hik]
        exact hi
    obtain ⟨hP1, hP2, hP3⟩ := hPr' m' hMD hm'v
    have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial (Finsupp.single (Fin.last K, ρ) e + m') 1) = X (Fin.last K, ρ) ^ e * Pr' (monomial m' 1) := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, strip_monomial_eq _ _ _ hm'v]
    rw [hPr]
    refine ⟨(hgr _).mpr ⟨_, hP1, rfl⟩, ?_, ?_⟩
    · unfold IntPol at hP2 ⊢
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hP2
      refine LinearMap.mem_range.mpr ⟨X (Fin.last K, ρ) ^ e * z, ?_⟩
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) z = _ at hz
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (X (Fin.last K, ρ) ^ e * z) = _
      rw [map_mul, map_pow, map_X, hz, mul_smul_comm]
    · intro g hg
      obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
      rw [fock_pow_mul _ _ _ _ hyf, hP3 y hy, monomial_single_add, fock_pow_mul _ _ _ _ hyf]
  · have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial m 1) = 0 := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, strip_monomial_ne _ _ _ hme, map_zero, map_zero]
    rw [hPr]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
    rw [fock_eq_zero_of _ _ (fun n => Or.inr (coeff_zero n)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · subst hn
      exact Or.inl (coeff_pow_mul_ne _ _ _ hyf _ hme)
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]

theorem gram_bound_of_restriction_of_proj (hX : ProjX) : GramBoundOfRestriction := by
  intro p _ K r _ LLw q J M ρ e1 κ hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 3) * e1) e1 κ
      (projAtOf_of hX p K r LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSat _ J _ ρ (hS e he)))
      (saturation_at_holds p K r LLw J M ρ w e e1 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 3) * e1 + 2 * e1 = (K + 5) * e1 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

end Formalism.InvariantFactorPaths.L4
