import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.FiniteCoverGrowth

theorem exists_norm_eval_le {d : ℕ} (c : MvPolynomial (Fin d) ℂ) :
    ∃ (K : ℝ) (M : ℕ), 0 ≤ K ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x c‖ ≤ K * (1 + ‖x‖) ^ M := by
  induction c using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨K, M, hK, h⟩ := hp
    obtain ⟨K', M', hK', h'⟩ := hq
    refine ⟨K + K', M + M', by positivity, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 + ‖x‖) ^ M ≤ (1 + ‖x‖) ^ (M + M') := pow_le_pow_right₀ h1 (by omega)
    have h3 : (1 + ‖x‖) ^ M' ≤ (1 + ‖x‖) ^ (M + M') := pow_le_pow_right₀ h1 (by omega)
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left h2 hK
    have := mul_le_mul_of_nonneg_left h3 hK'
    nlinarith [h x, h' x]
  | mul_X p i hp =>
    obtain ⟨K, M, hK, h⟩ := hp
    refine ⟨K, M + 1, hK, fun x => ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X, pow_succ, ← mul_assoc]
    have : ‖x i‖ ≤ 1 + ‖x‖ := by linarith [norm_le_pi_norm x i]
    exact mul_le_mul (h x) this (norm_nonneg _) (by positivity)

theorem exists_norm_root_le {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic) :
    ∃ (K : ℝ) (M : ℕ), 0 ≤ K ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ K * (1 + ‖x‖) ^ M := by
  choose K M hK h using fun i : ℕ => exists_norm_eval_le (p.coeff i)
  refine ⟨∑ i ∈ Finset.range p.natDegree, K i + 1, ∑ i ∈ Finset.range p.natDegree, M i,
    add_nonneg (Finset.sum_nonneg fun i _ => hK i) zero_le_one, fun x y hy => ?_⟩
  have hm : (p.map (MvPolynomial.eval x)).Monic := hp.map _
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hm.ne_zero hy
  have h2 : (p.map (MvPolynomial.eval x)).cauchyBound ≤
      ∑ i ∈ Finset.range p.natDegree, ‖MvPolynomial.eval x (p.coeff i)‖₊ + 1 := by
    simp only [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one,
      add_le_add_iff_right, hp.natDegree_map, Finset.sup_le_iff, Polynomial.coeff_map]
    intro i hi
    exact Finset.single_le_sum (f := fun i => ‖MvPolynomial.eval x (p.coeff i)‖₊)
      (fun _ _ => zero_le) hi
  have h3 : ‖y‖ ≤ ∑ i ∈ Finset.range p.natDegree, ‖MvPolynomial.eval x (p.coeff i)‖ + 1 := by
    have := NNReal.coe_le_coe.2 (h1.le.trans h2)
    simpa using this
  have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  refine h3.trans ?_
  rw [add_mul, Finset.sum_mul, one_mul]
  refine add_le_add (Finset.sum_le_sum fun i hi => (h i x).trans ?_) (one_le_pow₀ h0)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h0
    (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) hi)) (hK i)

theorem exists_map_eq_of_eval {d N : ℕ} (U : Set (Fin d → ℂ)) (S : (Fin d → ℂ) → Polynomial ℂ)
    (hdeg : ∀ x ∈ U, (S x).degree < N)
    (hev : ∀ t : ℂ, ∃ g : MvPolynomial (Fin d) ℂ, ∀ x ∈ U, (S x).eval t = MvPolynomial.eval x g) :
    ∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.degree < N ∧
      ∀ x ∈ U, s.map (MvPolynomial.eval x) = S x := by
  classical
  choose g hg using hev
  have hinj : Set.InjOn (fun i : ℕ => (i : ℂ)) (Finset.range N) :=
    fun a _ b _ h => Nat.cast_injective (R := ℂ) h
  refine ⟨∑ i ∈ Finset.range N, Polynomial.C (g i) *
    (Lagrange.basis (Finset.range N) (fun i : ℕ => (i : ℂ)) i).map MvPolynomial.C, ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    rw [← Polynomial.smul_eq_C_mul]
    refine (Polynomial.degree_smul_le _ _).trans_lt (Polynomial.degree_map_le.trans_lt ?_)
    rw [Lagrange.degree_basis hinj hi, Finset.card_range]
    have := Finset.mem_range.1 hi
    exact_mod_cast (by omega : N - 1 < N)
  · intro x hx
    rw [Lagrange.eq_interpolate (f := S x) hinj (by simpa using hdeg x hx),
      Lagrange.interpolate_apply, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hg _ x hx]
    congr 1
    have : (MvPolynomial.eval x).comp (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, Polynomial.map_id]

theorem contDiff_eval_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (fun z : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval z.1)).eval z.2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.map_add] using hp.add hq
  | monomial n a =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial]
    refine ContDiff.mul ?_ (contDiff_snd.pow n)
    have : ContDiff ℂ 1 (fun x : Fin d → ℂ => MvPolynomial.eval x a) :=
      (AnalyticOnNhd.eval_mvPolynomial a).contDiff
    exact this.comp contDiff_fst

theorem exists_local_root {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ)
    (a : ℂ) (ha : (p.map (MvPolynomial.eval x₀)).eval a = 0)
    (ha' : (p.map (MvPolynomial.eval x₀)).derivative.eval a ≠ 0) :
    ∃ y : (Fin d → ℂ) → ℂ, y x₀ = a ∧ DifferentiableAt ℂ y x₀ ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (y x) = 0 := by
  have hs := (contDiff_eval_map p).contDiffAt.hasStrictFDerivAt (x := (x₀, a)) one_ne_zero
  set L := fderiv ℂ (fun z : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval z.1)).eval z.2) (x₀, a)
  have h1 : HasFDerivAt (fun y : ℂ => (p.map (MvPolynomial.eval x₀)).eval y)
      (L ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
    hs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
  have h2 := ((p.map (MvPolynomial.eval x₀)).hasDerivAt a).hasFDerivAt
  have h3 := h1.unique h2
  have hinv : (L ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [h3]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ ha'), ?_⟩
    ext; simp
  refine ⟨hs.implicitFunctionOfProdDomain hinv, ?_, ?_, ?_⟩
  · exact (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  · exact (hs.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
  · have := hs.eventually_apply_implicitFunctionOfProdDomain hinv
    simpa [ha] using this

theorem separable_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (x : Fin d → ℂ) (hx : MvPolynomial.eval x q ≠ 0) :
    (p.map (MvPolynomial.eval x)).Separable := by
  obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 hq
  have h' := congrArg (Polynomial.map (MvPolynomial.eval x)) h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h'
  refine ⟨Polynomial.C (MvPolynomial.eval x q)⁻¹ * a.map (MvPolynomial.eval x),
    Polynomial.C (MvPolynomial.eval x q)⁻¹ * b.map (MvPolynomial.eval x), ?_⟩
  rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h', ← Polynomial.C_mul,
    inv_mul_cancel₀ hx, Polynomial.C_1]

theorem eq_nodal {P : Polynomial ℂ} (hm : P.Monic) (hs : P.Separable) :
    P = Lagrange.nodal P.roots.toFinset id := by
  classical
  rw [Lagrange.nodal_eq, Finset.prod, Multiset.toFinset_val,
    (Polynomial.nodup_roots hs).dedup]
  exact (IsAlgClosed.splits P).eq_prod_roots_of_monic hm

theorem card_roots {P : Polynomial ℂ} (hm : P.Monic) (hs : P.Separable) :
    P.roots.toFinset.card = P.natDegree := by
  conv_rhs => rw [eq_nodal hm hs, Lagrange.natDegree_nodal]

theorem exists_local_roots {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic)
    (x₀ : Fin d → ℂ) (hs : (p.map (MvPolynomial.eval x₀)).Separable) :
    ∃ y : Fin p.natDegree → (Fin d → ℂ) → ℂ, (∀ i, DifferentiableAt ℂ (y i) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (fun i => y i x) ∧
        (p.map (MvPolynomial.eval x)).roots.toFinset = Finset.univ.image (fun i => y i x) := by
  classical
  have hc := card_roots (hp.map (MvPolynomial.eval x₀)) hs
  rw [hp.natDegree_map] at hc
  let e := (Finset.equivFinOfCardEq hc).symm
  have hroot : ∀ i, (p.map (MvPolynomial.eval x₀)).eval (e i : ℂ) = 0 := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  choose y hy0 hyd hyr using fun i => exists_local_root p x₀ (e i) (hroot i)
    (by simpa using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := (e i : ℂ)) (by simpa using hroot i))
  refine ⟨y, hyd, ?_⟩
  have hne : ∀ᶠ x in 𝓝 x₀, ∀ i j, i ≠ j → y i x ≠ y j x := by
    simp only [eventually_all]
    intro i j hij
    refine ((hyd i).continuousAt.ne_iff_eventually_ne (hyd j).continuousAt).1 ?_
    rw [hy0, hy0]
    exact fun h => hij (e.injective (Subtype.ext h))
  filter_upwards [hne, eventually_all.2 hyr] with x h1 h2
  have hinj : Function.Injective (fun i => y i x) := fun i j h => by
    by_contra hij; exact h1 i j hij h
  refine ⟨hinj, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 (h2 i))
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    rw [hp.natDegree_map]

theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ) (n : ℕ) (hB : 1 ≤ B)
    (hs : s.card ≤ n) (h : ∀ i ∈ s, ‖f i‖ ≤ B) : ‖∏ i ∈ s, f i‖ ≤ B ^ n := by
  rw [norm_prod]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) h).trans ?_
  rw [Finset.prod_const]
  exact pow_le_pow_right₀ hB hs

theorem integral_and_rational_of_polynomial_growth :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 → IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧ Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) → (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 → DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} → (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) → ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) → (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map (MvPolynomial.eval z.1)).eval z.2) := by
  classical
  intro _ hpoly d m p q φ C hp hq0 hq hφ hb
  set U : Set (Fin d → ℂ) := {x | MvPolynomial.eval x q ≠ 0} with hU
  set Z : Set ((Fin d → ℂ) × ℂ) := {z | MvPolynomial.eval z.1 q ≠ 0 ∧
    (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} with hZ
  set n := p.natDegree with hn
  let T : (Fin d → ℂ) → Finset ℂ := fun x => (p.map (MvPolynomial.eval x)).roots.toFinset
  have hT : ∀ x y, y ∈ T x ↔ (p.map (MvPolynomial.eval x)).eval y = 0 := fun x y => by
    simp only [T, Multiset.mem_toFinset]
    exact Polynomial.mem_roots (hp.map _).ne_zero
  have hsep : ∀ x ∈ U, (p.map (MvPolynomial.eval x)).Separable :=
    fun x hx => separable_map p q hq x hx
  have hcard : ∀ x ∈ U, (T x).card = n := fun x hx => by
    rw [hn, ← hp.natDegree_map (MvPolynomial.eval x)]
    exact card_roots (hp.map _) (hsep x hx)
  have hUo : IsOpen U := isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const

  have hloc : ∀ x₀ ∈ U, ∃ y ψ : Fin n → (Fin d → ℂ) → ℂ, (∀ i, DifferentiableAt ℂ (y i) x₀) ∧
      (∀ i, DifferentiableAt ℂ (ψ i) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (fun i => y i x) ∧
        T x = Finset.univ.image (fun i => y i x) ∧ ∀ i, φ (x, y i x) = ψ i x := by
    intro x₀ hx₀
    obtain ⟨y, hyd, hy⟩ := exists_local_roots p hp x₀ (hsep x₀ hx₀)
    have hmem : ∀ᶠ x in 𝓝 x₀, ∀ i, (x, y i x) ∈ Z := by
      filter_upwards [hy, hUo.mem_nhds hx₀] with x h1 h2 i
      refine ⟨h2, (hT x _).1 ?_⟩
      change _ ∈ (p.map (MvPolynomial.eval x)).roots.toFinset
      rw [h1.2]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    choose F hF hF' using fun i => hφ _ (hmem.self_of_nhds i)
    refine ⟨y, fun i x => F i (x, y i x), hyd, fun i => ?_, ?_⟩
    · exact (hF i).differentiableAt.comp x₀ (differentiableAt_id.prodMk (hyd i))
    · have : ∀ i, ∀ᶠ x in 𝓝 x₀, φ (x, y i x) = F i (x, y i x) := fun i => by
        have ht : Tendsto (fun x => (x, y i x)) (𝓝 x₀) (𝓝[Z] (x₀, y i x₀)) :=
          tendsto_nhdsWithin_iff.2 ⟨(continuousAt_id.prodMk (hyd i).continuousAt).tendsto,
            hmem.mono fun x h => h i⟩
        exact ht.eventually (hF' i)
      filter_upwards [hy, eventually_all.2 this] with x h1 h2
      exact ⟨h1.1, h1.2, h2⟩

  have hgrow : ∀ t : ℂ, ∃ (K : ℝ) (M : ℕ), ∀ x ∈ U, 1 ≤ K * (1 + ‖x‖) ^ M ∧ ∀ y ∈ T x,
      ‖φ (x, y)‖ ≤ K * (1 + ‖x‖) ^ M ∧ ‖t - φ (x, y)‖ ≤ K * (1 + ‖x‖) ^ M ∧
        ‖t - y‖ ≤ K * (1 + ‖x‖) ^ M := by
    intro t
    obtain ⟨K, M, hK, h⟩ := exists_norm_root_le p hp
    refine ⟨1 + ‖t‖ + |C| + K, m + M, fun x hx => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ (m + M) := pow_le_pow_right₀ h1 (by omega)
    have h3 : (1 + ‖x‖) ^ M ≤ (1 + ‖x‖) ^ (m + M) := pow_le_pow_right₀ h1 (by omega)
    have h4 : 1 ≤ (1 + ‖x‖) ^ (m + M) := one_le_pow₀ h1
    have h5 : ‖t‖ ≤ ‖t‖ * (1 + ‖x‖) ^ (m + M) := le_mul_of_one_le_right (norm_nonneg _) h4
    have h6 : 0 ≤ |C| * (1 + ‖x‖) ^ (m + M) := by positivity
    have h7 : 0 ≤ K * (1 + ‖x‖) ^ (m + M) := by positivity
    have h8 := norm_nonneg t
    simp only [add_mul, one_mul]
    refine ⟨by linarith, fun y hy => ?_⟩
    have h9 : ‖φ (x, y)‖ ≤ |C| * (1 + ‖x‖) ^ (m + M) :=
      (hb (x, y) ⟨hx, (hT x y).1 hy⟩).trans
        (mul_le_mul (le_abs_self C) h2 (by positivity) (abs_nonneg C))
    have h10 : ‖y‖ ≤ K * (1 + ‖x‖) ^ (m + M) :=
      (h x y ((hT x y).1 hy)).trans (mul_le_mul_of_nonneg_left h3 hK)
    refine ⟨by linarith, ?_, ?_⟩
    · linarith [norm_sub_le t (φ (x, y))]
    · linarith [norm_sub_le t y]
  constructor
  · refine Exists.elim (exists_map_eq_of_eval (N := n) U
      (fun x => Lagrange.nodal (T x) (fun y => φ (x, y)) - Polynomial.X ^ n) ?_ ?_) ?_
    rotate_right
    · rintro s ⟨hs, hs'⟩
      refine ⟨Polynomial.X ^ n + s, Polynomial.monic_X_pow_add hs, fun z hz => ?_⟩
      rw [Polynomial.map_add, hs' z.1 hz.1, Polynomial.map_pow, Polynomial.map_X, add_sub_cancel]
      exact Lagrange.eval_nodal_at_node (v := fun y => φ (z.1, y)) ((hT _ _).2 hz.2)
    · intro x hx
      have h1 : (Lagrange.nodal (T x) (fun y => φ (x, y))).degree = n := by
        rw [Lagrange.degree_nodal, hcard x hx]
      rw [← h1]
      refine Polynomial.degree_sub_lt (by rw [h1, Polynomial.degree_X_pow])
        Lagrange.nodal_monic.ne_zero ?_
      rw [Lagrange.nodal_monic.leadingCoeff, (Polynomial.monic_X_pow n).leadingCoeff]
    · intro t
      obtain ⟨K, M, hK⟩ := hgrow t
      refine Exists.elim (hpoly d (M * n) q (fun x => ∏ y ∈ T x, (t - φ (x, y))) (K ^ n) hq0 ?_ ?_) ?_
      rotate_right
      · rintro g hg
        refine ⟨g - MvPolynomial.C (t ^ n), fun x hx => ?_⟩
        simp [Lagrange.eval_nodal, ← hg x hx]
      · intro x₀ hx₀
        obtain ⟨y, ψ, hy, hψ, h⟩ := hloc x₀ hx₀
        have : DifferentiableAt ℂ (fun x => ∏ i, (t - ψ i x)) x₀ := by fun_prop
        refine (this.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [h] with x hx
        rw [hx.2.1, Finset.prod_image fun i _ j _ h => hx.1 h]
        simp only [hx.2.2]
      · intro x hx
        rw [pow_mul, ← mul_pow]
        exact norm_prod_le_pow _ _ _ _ (hK x hx).1 (hcard x hx).le
          fun y hy => ((hK x hx).2 y hy).2.1
  · refine Exists.elim (exists_map_eq_of_eval (N := n + 1) U
      (fun x => ∑ y ∈ T x, Polynomial.C (φ (x, y)) * Lagrange.nodal ((T x).erase y) id) ?_ ?_) ?_
    rotate_right
    · rintro r ⟨-, hr⟩
      refine ⟨r, fun z hz => ?_⟩
      have hz' : z.2 ∈ T z.1 := (hT _ _).2 hz.2
      rw [hr z.1 hz.1, ← Polynomial.derivative_map, eq_nodal (hp.map _) (hsep z.1 hz.1),
        Polynomial.eval_finset_sum, Finset.sum_eq_single z.2]
      · rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
        congr 1
        exact Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hz'
      · intro y _ hy
        rw [Polynomial.eval_mul]
        exact mul_eq_zero_of_right _ (Lagrange.eval_nodal_at_node (v := id)
          (Finset.mem_erase.2 ⟨hy.symm, hz'⟩))
      · exact fun h => absurd hz' h
    · intro x hx
      refine (Polynomial.degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro y hy
      rw [← Polynomial.smul_eq_C_mul]
      refine (Polynomial.degree_smul_le _ _).trans_lt ?_
      rw [Lagrange.degree_nodal]
      have : ((T x).erase y).card < n + 1 :=
        Nat.lt_succ_of_le (Finset.card_erase_le.trans (hcard x hx).le)
      exact_mod_cast this
    · intro t
      obtain ⟨K, M, hK⟩ := hgrow t
      refine Exists.elim (hpoly d (M * (n + 1)) q
        (fun x => ∑ y ∈ T x, φ (x, y) * ∏ y' ∈ (T x).erase y, (t - y')) (n * K ^ (n + 1)) hq0 ?_ ?_) ?_
      rotate_right
      · rintro g hg
        refine ⟨g, fun x hx => ?_⟩
        simp [Lagrange.eval_nodal, ← hg x hx, Polynomial.eval_finset_sum]
      · intro x₀ hx₀
        obtain ⟨y, ψ, hy, hψ, h⟩ := hloc x₀ hx₀
        have : DifferentiableAt ℂ
          (fun x => ∑ i, ψ i x * ∏ j ∈ Finset.univ.erase i, (t - y j x)) x₀ := by fun_prop
        refine (this.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [h] with x hx
        rw [hx.2.1, Finset.sum_image fun i _ j _ h => hx.1 h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hx.2.2, ← Finset.image_erase hx.1, Finset.prod_image fun i _ j _ h => hx.1 h]
      · intro x hx
        rw [pow_mul, mul_assoc, ← mul_pow]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ ((K * (1 + ‖x‖) ^ M) ^ (n + 1)) fun y hy => ?_).trans
          (by rw [hcard x hx, nsmul_eq_mul])
        rw [norm_mul, pow_succ']
        refine mul_le_mul ((hK x hx).2 y hy).1 (norm_prod_le_pow _ _ _ _ (hK x hx).1
          (Finset.card_erase_le.trans (hcard x hx).le)
          fun y' hy' => ((hK x hx).2 y' (Finset.mem_of_mem_erase hy')).2.2) (norm_nonneg _)
          (zero_le_one.trans (hK x hx).1)

end GlobalTheory.FiniteCoverGrowth
