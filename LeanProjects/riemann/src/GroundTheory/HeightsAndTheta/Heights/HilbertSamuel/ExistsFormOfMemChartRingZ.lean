import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

noncomputable section

namespace ArithmeticVolumeMultiplicative

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have h0 : m = 0 := by
    by_contra h
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_neg (Ne.symm h)] at hm
    exact hm rfl
  subst h0
  simp

open Classical in
theorem mh_X (k : K) (i : ι k) : IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem mh_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using mh_C (ι := ι) 1
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mh_mul ih hf

theorem mh_coordProd (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using mh_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact mh_mul (mh_pow (mh_X k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordProd_add (c : ∀ k, ι k) (d e : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (d + e) k) =
      (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k := by
  rw [← Finset.prod_mul_distrib]
  simp [pow_add]

open Classical in

theorem exists_form_of_mem_chartRingZ {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Ω} (hs : s ∈ chartRingZ y c) :
    ∃ (d : K → ℕ) (G : MRing ι), IsMultiHomog G d ∧
      aeval y G = s * aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) := by
  classical
  unfold chartRingZ at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨k, i⟩ := p
    refine ⟨Pi.single k 1, X ⟨k, i⟩, mh_X k i, ?_⟩
    have hm : aeval y (∏ k', (X ⟨k', c k'⟩ : MRing ι) ^ (Pi.single k 1 : K → ℕ) k') = y ⟨k, c k⟩ := by
      rw [map_prod, Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [hm, aeval_X, div_mul_cancel₀ _ (hc k)]
  | algebraMap r =>
    exact ⟨0, C r, mh_C r, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨d1, G1, hG1, e1⟩ := hs
    obtain ⟨d2, G2, hG2, e2⟩ := ht
    refine ⟨d1 + d2, G1 * (∏ k, X ⟨k, c k⟩ ^ d2 k) + G2 * (∏ k, X ⟨k, c k⟩ ^ d1 k), ?_, ?_⟩
    · refine mh_add (mh_mul hG1 (mh_coordProd c d2)) ?_
      rw [add_comm d1 d2]
      exact mh_mul hG2 (mh_coordProd c d1)
    · rw [coordProd_add, map_add, map_mul, map_mul, map_mul, e1, e2]
      ring
  | mul s t _ _ hs ht =>
    obtain ⟨d1, G1, hG1, e1⟩ := hs
    obtain ⟨d2, G2, hG2, e2⟩ := ht
    refine ⟨d1 + d2, G1 * G2, mh_mul hG1 hG2, ?_⟩
    rw [coordProd_add, map_mul, map_mul, e1, e2]
    ring

theorem exists_chart {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hz1 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  choose c hc using hz1
  refine ⟨c, hc, fun k hy => hc k ?_⟩
  have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
    unfold mCoordIdeal
    rw [RingHom.mem_ker]
    simp only [mConeMap, aeval_X, hy, map_zero, zero_mul]
  have := hz.2 _ hX
  simpa using this

theorem mul_mem_chartLat {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {θ s : Ω} {a : K → ℤ} {τ : ℕ}
    (hθ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → θ ∈ chartRingZ y c) (hs : s ∈ chartLat y a τ) :
    θ * s ∈ chartLat y a τ := by
  have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c := hs
  show ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      θ * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c
  intro c hc
  rw [mul_assoc]
  exact Subalgebra.mul_mem _ (hθ c hc) (hs' c hc)

theorem blocks_ne_zero_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ᶠ w in 𝓝 z, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
  refine Filter.eventually_all.2 fun k => ?_
  obtain ⟨i, hi⟩ := hz k
  exact ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).continuousAt.eventually_ne hi).mono fun w hw => ⟨i, hw⟩

theorem levi_congr {N : Type} [Fintype N] {φ ψ : (N → ℂ) → ℝ} {z : N → ℂ} (c : ℝ)
    (h : φ =ᶠ[𝓝 z] fun w => ψ w + c) (w : N → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := by
    have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
      h.fderiv.trans (Eventually.of_forall fun x => fderiv_add_const c)
    exact h1.fderiv_eq
  unfold leviForm
  rw [h2]

theorem ratio_step {a1 a2 hn nv nw ℓ E r N : ℝ} {n : ℕ} (ha2 : 0 < a2) (hhn : 0 < hn) (hnw : 0 ≤ nw)
    (hℓ : 0 < ℓ) (hN : 0 < N) (hvw : nw * nv = 1)
    (h1 : a1 * (N * nv * hn) / (N ^ 2 * a2 * hn * ℓ ^ n) ≤ E * r) :
    a1 / (a2 * ℓ ^ n) ≤ N * nw * (E * r) := by
  have hℓn : 0 < ℓ ^ n := pow_pos hℓ n
  have e : a1 * (N * nv * hn) / (N ^ 2 * a2 * hn * ℓ ^ n) = a1 / (a2 * ℓ ^ n) * nv / N := by
    field_simp
  rw [e] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ N * nw)
  have e2 : N * nw * (a1 / (a2 * ℓ ^ n) * nv / N) = a1 / (a2 * ℓ ^ n) * (nw * nv) := by
    field_simp
  rw [e2, hvw, mul_one] at h2
  exact h2

theorem final_step {X N nw r s t η C : ℝ} {n : ℕ} (hX : X ≤ N * nw * (Real.exp (n * (t + η / 2)) * r))
    (hnw : nw ≤ Real.exp (n * (s - t) + C)) (hlog : Real.log N + C ≤ n * (η / 2)) (hr : 0 ≤ r)
    (hN : 0 < N) : X / Real.exp s ^ n ≤ Real.exp (n * η) * r := by
  have hE : N * Real.exp (n * (s - t) + C) * Real.exp (n * (t + η / 2)) ≤ Real.exp (n * η) * Real.exp (n * s) := by
    rw [← Real.exp_log hN, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h3 : X ≤ Real.exp (n * η) * Real.exp (n * s) * r := by
    calc X ≤ N * nw * (Real.exp (n * (t + η / 2)) * r) := hX
      _ ≤ N * Real.exp (n * (s - t) + C) * (Real.exp (n * (t + η / 2)) * r) := by gcongr
      _ = N * Real.exp (n * (s - t) + C) * Real.exp (n * (t + η / 2)) * r := by ring
      _ ≤ Real.exp (n * η) * Real.exp (n * s) * r := by gcongr
  rw [← Real.exp_nat_mul, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem proof (hG3 : G3.Statement) (hW : EmbeddingWeight.Statement) (hT : TwistIntersectionInt.Statement)
    (hU : UnitApprox.Statement) (hR : ConstantsRegular.Statement) : ArithmeticVolumeMultiplicative.Statement := by
  intro K _ ι _ Ω _ _ F _ _ _ y D M L P0 P0' II a iota Λ t hD hII hY hB hM hP0' hsemi hconj hdeg huniq
    hΛ hΛc htc hgen hmean ha hmaps hbd

  have hNpos : (0 : ℝ) < Fintype.card (F →+* ℂ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((∑ sg, t sg) - ∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ) :=
    ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg (sub_nonneg.2 hmean) hNpos.le
  obtain ⟨s, hs⟩ : ∃ s : (F →+* ℂ) → ℝ, ∀ sg, s sg = Real.log (Λ sg) + m := ⟨_, fun _ => rfl⟩
  have hsc : ∀ sg, s (ComplexEmbedding.conjugate sg) = s sg := fun sg => by rw [hs, hs, hΛc]
  have hssum : ∑ sg, s sg = ∑ sg, t sg := by
    simp only [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hm, mul_div_cancel₀ _ hNpos.ne']
    ring

  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hW K ι Ω F y (fun sg => Real.exp (s sg))
    (fun sg => Real.exp_pos _) (fun sg => by simp only [hsc]) huniq
  have hLa : (L.tensor B).a = L.a := by
    rw [show (L.tensor B).a = L.a + B.a from rfl, hBa, add_zero]
  have hLh : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg, LiesOver y sg z →
      (L.tensor B).h z = L.h z * Real.exp (s sg) := by
    intro z hz sg hsg
    show L.h z * B.h z = _
    rw [(hBloc z hz sg hsg).eq_of_nhds]
  have hsemi' : IsSemipositiveRel P0' (mCoordIdeal y) (L.tensor B) := by
    refine ⟨hsemi.1.mul hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hev : (fun x => Real.log ((L.tensor B).h x)) =ᶠ[𝓝 z] fun x => Real.log (L.h x) + s sg := by
      filter_upwards [hBloc z hz sg hsg, blocks_ne_zero_nhds hz.1] with x h1 h2
      rw [show (L.tensor B).h x = L.h x * B.h x from rfl, h1,
        Real.log_mul (L.pos x h2).ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [levi_congr _ hev]
    exact hsemi.2 z hz w hw
  have hconj' : IsConjInvariantH (L.tensor B) := fun z => by
    show L.h _ * B.h _ = L.h z * B.h z
    rw [hconj z, hBc z]
  have hsmall : IsSmallGeneratedDatum P0' y D (L.tensor B) := by
    obtain ⟨q, w, hw, hgw, hwb⟩ := hgen
    refine ⟨hP0', hsemi', by rw [hLa]; exact hdeg, q, w, by rw [hLa]; exact hw, by rw [hLa]; exact hgw,
      fun j => ?_⟩
    intro dg dh g h z hg hh hd hgy hz
    rw [hLa] at hd
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have h1 := hwb j sg dg dh g h z hg hh hd hgy hz hsg
    rw [hLh z hz sg hsg]
    have hle : Λ sg ≤ Real.exp (s sg) := by
      rw [hs sg, Real.exp_add, Real.exp_log (hΛ sg)]
      exact le_mul_of_one_le_right (hΛ sg).le (Real.one_le_exp hm0)
    have hpos := (L.pos z hz.1).le
    have hn := norm_nonneg (eval z (map (Int.castRingHom ℂ) h))
    simp only [pow_one] at h1 ⊢
    have key := mul_le_mul_of_nonneg_right hle (mul_nonneg hn hpos)
    nlinarith

  obtain ⟨N, hN1, hNreg⟩ := hR K ι Ω F y huniq
  obtain ⟨Cu, hC⟩ := hU F (fun sg => s sg - t sg) (fun sg => by simp only [hsc, htc]) (by
    simp only [Finset.sum_sub_distrib, hssum, sub_self])
  choose u hu using hC
  have hu' : ∀ (n : ℕ) sg, |Real.log ‖sg ((u n : 𝓞 F) : F)‖ - n * (s sg - t sg)| ≤ Cu := hu
  have hmul : ∀ n, ((u n : 𝓞 F) : F) * ((((u n)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := fun n => by
    simp only [RingOfIntegers.coe_eq_algebraMap, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → Ω, ∀ n, θ n = (N : Ω) * algebraMap F Ω ((u n : 𝓞 F) : F) := ⟨_, fun _ => rfl⟩
  have hθreg : ∀ n (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → θ n ∈ chartRingZ y c := fun n c hc => by
    rw [hθ]; exact hNreg (u n) c hc
  have hθne : ∀ n, θ n ≠ 0 := fun n => by
    rw [hθ]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      ((map_ne_zero _).mpr (left_ne_zero_of_mul_eq_one (hmul n)))
  obtain ⟨iota', hi'⟩ : ∃ iota' : ℕ → Ω →+ Ω, ∀ n f, iota' n f = θ n * iota n f :=
    ⟨fun n => (AddMonoidHom.mulLeft (θ n)).comp (iota n), fun _ _ => rfl⟩
  have hmaps' : ∀ n, a ∣ n → Set.InjOn (iota' n) (chartLat y M.a n) ∧
      Set.MapsTo (iota' n) (chartLat y M.a n) (chartLat y (L.tensor B).a n) := by
    intro n hn
    obtain ⟨hinj, hmap, -⟩ := hmaps n hn
    refine ⟨fun f hf g hg he => hinj hf hg ?_, fun f hf => ?_⟩
    · rw [hi', hi'] at he
      exact mul_left_cancel₀ (hθne n) he
    · rw [hi', hLa]
      exact mul_mem_chartLat (hθreg n) (hmap hf)
  have hbd' : ∀ η : ℝ, 0 < η → ∃ (n₀ : ℕ) (O : Set ((Σ k, ι k) → ℂ)), IsOpen O ∧
      mcPts (mCoordIdeal y) ⊆ closure (O ∩ mcPts (mCoordIdeal y)) ∧
      ∀ n, n₀ ≤ n → a ∣ n → ∀ f ∈ chartLat y M.a n,
        PtBoundOn y M (L.tensor B) n (O ∩ mcPts (mCoordIdeal y)) (Real.exp (n * η)) f (iota' n f) := by
    intro η hη
    obtain ⟨n₀, O, hO, hdn, hb⟩ := hbd (η / 2) (half_pos hη)
    obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((Real.log N + Cu) / (η / 2))
    refine ⟨max n₀ n₁, O, hO, hdn, fun n hn han f hf => ?_⟩
    have hn0 : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : (n₁ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have hlogN : Real.log N + Cu ≤ n * (η / 2) := by
      have h1 := (div_lt_iff₀ (half_pos hη)).1 hn₁
      have h2 := mul_le_mul_of_nonneg_right hn1 (half_pos hη).le
      linarith
    intro dg dh dg' dh' g h g' h' hg hh hdd hgy hg' hh' hdd' hgy' z hz h0 h0'
    rw [hLa] at hdd'
    have hz2 : z ∈ mcPts (mCoordIdeal y) := hz.2
    obtain ⟨sg, hsg, -⟩ := huniq z hz2

    obtain ⟨c, hcz, hcy⟩ := exists_chart hz2
    obtain ⟨d, G, hG, hGy⟩ := exists_form_of_mem_chartRingZ hcy (hNreg ((u n)⁻¹ : (𝓞 F)ˣ) c hcy)
    have hH := mh_coordProd c d
    have hHz : eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) ≠ 0 := by
      simp only [map_prod, map_pow, map_X, eval_X]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcz k)
    have hGz : eval z (map (Int.castRingHom ℂ) G) = (N : ℂ) * sg ((((u n)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) *
        eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) := by
      have := hsg d G _ ((N : F) * ((((u n)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) hG hH
        (by rw [hGy, map_mul, map_natCast])
      rw [this, map_mul, map_natCast]

    have hrep : aeval y (g' * G) =
        iota n f * aeval y (C ((N : ℤ) ^ 2) * h' * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) := by
      have e1 := hgy'
      rw [hi', hθ] at e1
      have e2 : algebraMap F Ω ((u n : 𝓞 F) : F) * algebraMap F Ω ((((u n)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
        rw [← map_mul, hmul n, map_one]
      simp only [map_mul, e1, hGy, eq_intCast, Int.cast_pow, Int.cast_natCast, map_pow, map_natCast]
      linear_combination ((N : Ω) * N * iota n f * aeval y h' *
        aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) * e2
    have hdeg'' : ∀ k, (((dg' + d) k : ℕ) : ℤ) = ((0 + dh' + d) k : ℕ) + (n : ℤ) * L.a k := by
      intro k
      have := hdd' k
      simp only [Pi.add_apply, Pi.zero_apply, zero_add]
      push_cast
      linarith
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : eval z (map (Int.castRingHom ℂ) (C ((N : ℤ) ^ 2) * h' * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k))
        ≠ 0 := by
      simp only [map_mul, eval_mul]
      refine mul_ne_zero (mul_ne_zero ?_ h0') hHz
      simpa using pow_ne_zero 2 hNc
    have h1 := hb n hn0 han f hf sg dg dh (dg' + d) (0 + dh' + d) g h (g' * G)
      (C ((N : ℤ) ^ 2) * h' * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) hg hh hdd hgy (mh_mul hg' hG)
      (mh_mul (mh_mul (mh_C _) hh') hH) hdeg'' hrep z ⟨hz, hsg⟩ h0 hden
    simp only [map_mul, eval_mul, map_C, eval_C, hGz, norm_mul, eq_intCast, Int.cast_pow, Int.cast_natCast,
      map_pow, map_natCast, norm_pow, RCLike.norm_natCast] at h1

    have hw0 : 0 < ‖sg ((u n : 𝓞 F) : F)‖ := by
      rw [norm_pos_iff, map_ne_zero]
      exact left_ne_zero_of_mul_eq_one (hmul n)
    have hwv : ‖sg ((u n : 𝓞 F) : F)‖ * ‖sg ((((u n)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)‖ = 1 := by
      rw [← norm_mul, ← map_mul, hmul n, map_one, norm_one]
    have hwle : ‖sg ((u n : 𝓞 F) : F)‖ ≤ Real.exp (n * (s sg - t sg) + Cu) := by
      have := (abs_le.1 (hu' n sg)).2
      rw [← Real.exp_log hw0]
      exact Real.exp_le_exp.2 (by linarith)
    have hX := ratio_step (norm_pos_iff.mpr h0') (norm_pos_iff.mpr hHz) hw0.le (L.pos z hz2.1)
      (by exact_mod_cast hN1 : (0 : ℝ) < N) hwv h1
    rw [hLh z hz2 sg hsg, mul_pow, ← mul_assoc, ← div_div]
    exact final_step hX hwle hlogN (by have := M.pos z hz2.1; positivity) (by exact_mod_cast hN1)

  have key := hG3 K ι Ω y D M (L.tensor B) P0 P0' II a iota' hD hII hY hB hM hsmall hconj' ha hmaps' hbd'
  have hTw := hT K ι Ω F y D L B II (fun sg => Real.exp (s sg)) hD hII hY hB hsemi.1 hBa hBs
    (fun _ => Real.exp_pos _) huniq hBloc
  simp only [Real.log_exp] at hTw
  rw [hTw, hssum] at key
  exact key

end ArithmeticVolumeMultiplicative

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
