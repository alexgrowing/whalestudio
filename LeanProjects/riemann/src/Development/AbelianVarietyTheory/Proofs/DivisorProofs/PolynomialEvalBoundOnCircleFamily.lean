import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootMapMinpolyIffExistsRingHomExtensionStatement

namespace GlobalTheory

open MvPolynomial

open Polynomial in
private lemma norm_apply_zero_le_of_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ}
    (h : ∀ w : ℂ, ‖w‖ = 1 → ‖f w‖ ≤ C) : ‖f 0‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1)
    Metric.isBounded_ball hf.diffContOnCl
  · intro w hw
    rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
    exact h w hw
  · exact subset_closure (Metric.mem_ball_self one_pos)

private lemma differentiable_eval_mvPolynomial_line {d : ℕ} (z v : Fin d → ℂ) (a : MvPolynomial (Fin d) ℚ) :
    Differentiable ℂ
      (fun t : ℂ => MvPolynomial.eval₂ (algebraMap ℚ ℂ) (fun i => z i + t * v i) a) := by
  induction a using MvPolynomial.induction_on with
  | C q => simp only [MvPolynomial.eval₂_C]; exact differentiable_const _
  | add p q hp hq => simp only [MvPolynomial.eval₂_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (by fun_prop)

private lemma differentiable_eval_mvPolynomial_line₂ {d r : ℕ} (z v : Fin d → ℂ) (c : Fin r → ℂ)
    (a : MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) :
    Differentiable ℂ (fun t : ℂ => MvPolynomial.eval₂
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (fun i => z i + t * v i)) c a) := by
  induction a using MvPolynomial.induction_on with
  | C q =>
    simp only [MvPolynomial.eval₂_C, MvPolynomial.coe_eval₂Hom]
    exact differentiable_eval_mvPolynomial_line z v q
  | add p q hp hq => simp only [MvPolynomial.eval₂_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (differentiable_const _)

open Polynomial in
private lemma norm_multiset_prod_le_pow_card' {s : Multiset ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ a ∈ s, ‖a‖ ≤ ρ) : ‖s.prod‖ ≤ ρ ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _) hρ

open Polynomial in
private lemma norm_coeff_le_choose_mul_pow_of_roots_le {q : ℂ[X]} {n : ℕ} (hq : q.Monic)
    (hn : q.natDegree = n) {ρ : ℝ} (hρ : 0 ≤ ρ) (hr : ∀ a, q.IsRoot a → ‖a‖ ≤ ρ) (k : ℕ)
    (hk : k ≤ n) : ‖q.coeff k‖ ≤ (n.choose k : ℝ) * ρ ^ (n - k) := by
  subst hn
  rw [Polynomial.coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hk,
    hq.leadingCoeff, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hmem : ∀ a ∈ q.roots, ‖a‖ ≤ ρ := fun a ha => hr a (Polynomial.isRoot_of_mem_roots ha)
  rw [Multiset.esymm]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ (ρ ^ (q.natDegree - k)) ?_).trans ?_
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hb
    rw [Multiset.mem_powersetCard] at hs
    have := norm_multiset_prod_le_pow_card' hρ (fun a ha => hmem a (Multiset.mem_of_le hs.1 ha))
    simpa [Function.comp, hs.2] using this
  · rw [Multiset.card_map, Multiset.card_powersetCard, IsAlgClosed.card_roots_eq_natDegree,
      nsmul_eq_mul, Nat.choose_symm hk]

open Polynomial in
private lemma norm_root_le_two_pow_mul_of_coeff_le {p : ℂ[X]} {n : ℕ} (hp : p.Monic)
    (hn : p.natDegree = n) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hc : ∀ k < n, ‖p.coeff k‖ ≤ (n.choose k : ℝ) * ρ ^ (n - k)) {a : ℂ} (ha : p.IsRoot a) :
    ‖a‖ ≤ 2 ^ n * ρ := by
  by_cases hle : ‖a‖ ≤ ρ
  · exact hle.trans (le_mul_of_one_le_left hρ (one_le_pow₀ (by norm_num)))
  push_neg at hle
  have hpos : 0 < ‖a‖ := hρ.trans_lt hle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have h1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
      rw [h1] at ha
      simp at ha
    · exact ⟨m, rfl⟩
  have hlead : p.coeff (m + 1) = 1 := by rw [← hn]; exact hp.coeff_natDegree
  have heval : p.eval a = 0 := ha
  rw [Polynomial.eval_eq_sum_range, hn, Finset.sum_range_succ, hlead, one_mul] at heval
  have hneg : a ^ (m + 1) = -∑ k ∈ Finset.range (m + 1), p.coeff k * a ^ k := by
    linear_combination heval
  have hsum : ‖a‖ ^ (m + 1) ≤ ∑ k ∈ Finset.range (m + 1), ‖p.coeff k‖ * ‖a‖ ^ k := by
    rw [← norm_pow, hneg, norm_neg]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul, norm_pow]
  have hterm : ∀ k ∈ Finset.range (m + 1),
      ‖p.coeff k‖ * ‖a‖ ^ k ≤ ((m + 1).choose k : ℝ) * (ρ * ‖a‖ ^ m) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := hc k (Finset.mem_range.mp hk)
    have h2 : ρ ^ (m + 1 - k) * ‖a‖ ^ k ≤ ρ * ‖a‖ ^ m := by
      have he : m + 1 - k = (m - k) + 1 := by omega
      rw [he, pow_succ]
      calc ρ ^ (m - k) * ρ * ‖a‖ ^ k ≤ ‖a‖ ^ (m - k) * ρ * ‖a‖ ^ k := by gcongr
        _ = ρ * ‖a‖ ^ m := by
          rw [mul_comm (‖a‖ ^ (m - k)) ρ, mul_assoc, ← pow_add, Nat.sub_add_cancel hk']
    calc ‖p.coeff k‖ * ‖a‖ ^ k ≤ ((m + 1).choose k : ℝ) * ρ ^ (m + 1 - k) * ‖a‖ ^ k := by
          gcongr
      _ = ((m + 1).choose k : ℝ) * (ρ ^ (m + 1 - k) * ‖a‖ ^ k) := by ring
      _ ≤ ((m + 1).choose k : ℝ) * (ρ * ‖a‖ ^ m) := by gcongr
  have hchoose : ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℝ) ≤ 2 ^ (m + 1) := by
    have h' : ∑ k ∈ Finset.range (m + 1), (m + 1).choose k ≤ 2 ^ (m + 1) := by
      rw [← Nat.sum_range_choose (m + 1)]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ _))
    exact_mod_cast h'
  have hmain : ‖a‖ ^ (m + 1) ≤ 2 ^ (m + 1) * ρ * ‖a‖ ^ m := by
    calc ‖a‖ ^ (m + 1) ≤ ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℝ) * (ρ * ‖a‖ ^ m) :=
          hsum.trans (Finset.sum_le_sum hterm)
      _ = (∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℝ)) * (ρ * ‖a‖ ^ m) := by
          rw [Finset.sum_mul]
      _ ≤ 2 ^ (m + 1) * (ρ * ‖a‖ ^ m) := by gcongr
      _ = 2 ^ (m + 1) * ρ * ‖a‖ ^ m := by ring
  have hmain' : ‖a‖ * ‖a‖ ^ m ≤ (2 ^ (m + 1) * ρ) * ‖a‖ ^ m := by
    rw [← pow_succ']; exact hmain
  exact le_of_mul_le_mul_right hmain' (pow_pos hpos m)

open Polynomial in
private lemma natDegree_minpoly_pow_le {A S : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [Algebra A S] [Module.IsTorsionFree A S]
    {g : S} (hg : IsIntegral A g) (N : ℕ) :
    (minpoly A (g ^ N)).natDegree ≤ (minpoly A g).natDegree := by
  have hf : (minpoly A g).Monic := minpoly.monic hg
  let pb := AdjoinRoot.powerBasis' hf
  haveI : Module.Free A (AdjoinRoot (minpoly A g)) := Module.Free.of_basis pb.basis
  haveI : Module.Finite A (AdjoinRoot (minpoly A g)) := Module.Finite.of_basis pb.basis
  let L := Algebra.lmul A (AdjoinRoot (minpoly A g)) (AdjoinRoot.root (minpoly A g) ^ N)
  have hq : aeval (AdjoinRoot.root (minpoly A g) ^ N) L.charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly L
    have h2 : Algebra.lmul A (AdjoinRoot (minpoly A g))
        (aeval (AdjoinRoot.root (minpoly A g) ^ N) L.charpoly) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]; exact h
    have h3 := congrArg (fun F : Module.End A (AdjoinRoot (minpoly A g)) => F 1) h2
    simpa using h3
  let φ : AdjoinRoot (minpoly A g) →ₐ[A] S :=
    AdjoinRoot.liftAlgHom (minpoly A g) (Algebra.ofId A S) g
      (by rw [← minpoly.aeval A g, Polynomial.aeval_def]; rfl)
  have hφ : φ (AdjoinRoot.root (minpoly A g)) = g := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hq' : aeval (g ^ N) L.charpoly = 0 := by
    have hmap : aeval (g ^ N) L.charpoly =
        φ (aeval (AdjoinRoot.root (minpoly A g) ^ N) L.charpoly) := by
      rw [← Polynomial.aeval_algHom_apply, map_pow, hφ]
    rw [hmap, hq, map_zero]
  have hdvd := minpoly.isIntegrallyClosed_dvd (hg.pow N) hq'
  calc (minpoly A (g ^ N)).natDegree ≤ L.charpoly.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic L).ne_zero
    _ = (minpoly A g).natDegree := by
        rw [LinearMap.charpoly_natDegree, pb.finrank, AdjoinRoot.powerBasis'_dim]

open MvPolynomial in

theorem _root_.GlobalTheory.maxPrinciple_line_eval₂ : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → ∀ (r : ℕ) (G : MvPolynomial (Fin r) B) (c : Fin r → ℂ) (z v : Fin d → ℂ) (R : ℝ), (∀ (x : B →+* ℂ) (w : ℂ), ‖w‖ = 1 → (∀ i, x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) = z i + w * v i) → ‖MvPolynomial.eval₂ x c G‖ ≤ R) → ∀ x : B →+* ℂ, (∀ i, x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) = z i) → ‖MvPolynomial.eval₂ x c G‖ ≤ R := by
  intro d B _ _ _ _ hinj r G c z v R hR x hx
  letI : Algebra (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (MvPolynomial (Fin r) B) :=
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin d) ℚ) B)).toAlgebra
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ))
      (MvPolynomial (Fin r) B)) := MvPolynomial.map_injective _ hinj
  haveI : Module.IsTorsionFree (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ))
      (MvPolynomial (Fin r) B) := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj'
  haveI : Algebra.IsIntegral (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ))
      (MvPolynomial (Fin r) B) := by
    constructor
    intro a
    induction a using MvPolynomial.induction_on with
    | C b =>
      have hb : IsIntegral (MvPolynomial (Fin d) ℚ) b := Algebra.IsIntegral.isIntegral b
      exact IsIntegral.map_of_comp_eq (MvPolynomial.C : MvPolynomial (Fin d) ℚ →+* _)
        (MvPolynomial.C : B →+* MvPolynomial (Fin r) B)
        (RingHom.ext fun a => MvPolynomial.map_C _ _) hb
    | add p q hp hq => exact hp.add hq
    | mul_X p i hp =>
      have hXi : (MvPolynomial.X i : MvPolynomial (Fin r) B) =
          algebraMap (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (MvPolynomial (Fin r) B)
            (MvPolynomial.X i) := (MvPolynomial.map_X _ _).symm
      rw [hXi]
      exact hp.mul isIntegral_algebraMap
  have hg : IsIntegral (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) G :=
    Algebra.IsIntegral.isIntegral G
  let φ : ℂ → (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ) →+* ℂ) := fun t =>
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (fun i => z i + t * v i)) c
  have lift : ∀ (t : ℂ) (X' : MvPolynomial (Fin r) B →+* ℂ),
      X'.comp (algebraMap (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (MvPolynomial (Fin r) B))
        = φ t →
      (∀ i, (X'.comp MvPolynomial.C) (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))
        = z i + t * v i) ∧ X' G = MvPolynomial.eval₂ (X'.comp MvPolynomial.C) c G := by
    intro t X' hX'
    have hC : ∀ a, X' (algebraMap (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ))
        (MvPolynomial (Fin r) B) a) = φ t a := fun a => RingHom.congr_fun hX' a
    constructor
    · intro i
      have h1 := hC (MvPolynomial.C (MvPolynomial.X i))
      rw [RingHom.algebraMap_toAlgebra, MvPolynomial.map_C] at h1
      simpa [φ] using h1
    · have hX : ∀ j, X' (MvPolynomial.X j) = c j := by
        intro j
        have h1 := hC (MvPolynomial.X j)
        rw [RingHom.algebraMap_toAlgebra, MvPolynomial.map_X] at h1
        simpa [φ] using h1
      have hext : X' = MvPolynomial.eval₂Hom (X'.comp MvPolynomial.C) c := by
        apply MvPolynomial.ringHom_ext
        · intro b; simp
        · intro j; simp [hX]
      conv_lhs => rw [hext]
      rfl
  have hA : x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (fun i => z i + 0 * v i) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      exact RingHom.congr_fun (RingHom.ext_rat
        ((x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B)).comp MvPolynomial.C)
        ((MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (fun i => z i + 0 * v i)).comp MvPolynomial.C)) q
    · intro i; simp [hx i]
  have h0 : (MvPolynomial.eval₂Hom x c).comp (algebraMap
      (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (MvPolynomial (Fin r) B)) = φ 0 := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := RingHom.congr_fun hA a
      simp only [RingHom.comp_apply] at this
      simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, MvPolynomial.map_C,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, φ]
      exact this
    · intro j
      simp [φ, RingHom.algebraMap_toAlgebra]
  have hR0 : 0 ≤ R := by
    have hdeg : ((minpoly _ G).map (φ 1)).degree ≠ 0 := by
      rw [(minpoly.monic hg).degree_map]; exact (minpoly.degree_pos hg).ne'
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg
    obtain ⟨X', hX', -⟩ := (_root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension _ _ hinj' G (φ 1) a).1 ha
    obtain ⟨hgen, -⟩ := lift 1 X' hX'
    exact (norm_nonneg _).trans (hR _ 1 norm_one hgen)
  set n := (minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) G).natDegree with hn_def
  have key : ∀ N : ℕ, ‖MvPolynomial.eval₂ x c G‖ ^ N ≤ 2 ^ n * R ^ N := by
    intro N
    have hmon := minpoly.monic (hg.pow N)
    have hroots : ∀ w : ℂ, ‖w‖ = 1 → ∀ a,
        ((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).map (φ w)).IsRoot a →
        ‖a‖ ≤ R ^ N := by
      intro w hw a ha
      obtain ⟨X', hX', rfl⟩ := (_root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension _ _ hinj' (G ^ N) (φ w) a).1 ha
      obtain ⟨hgen, hval⟩ := lift w X' hX'
      rw [map_pow, norm_pow, hval]
      exact pow_le_pow_left₀ (norm_nonneg _) (hR _ w hw hgen) N
    have hcoef : ∀ k ≤ (minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).natDegree,
        ‖(φ 0) ((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).coeff k)‖ ≤
        (((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).natDegree).choose k
          : ℝ) * (R ^ N) ^
          ((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).natDegree - k) := by
      intro k hk
      apply norm_apply_zero_le_of_circle (f := fun t =>
        φ t ((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).coeff k))
      · exact differentiable_eval_mvPolynomial_line₂ z v c _
      · intro w hw
        have := norm_coeff_le_choose_mul_pow_of_roots_le (hmon.map (φ w)) (hmon.natDegree_map (φ w))
          (pow_nonneg hR0 N) (hroots w hw) k hk
        rwa [Polynomial.coeff_map] at this
    have hroot0 : ((minpoly (MvPolynomial (Fin r) (MvPolynomial (Fin d) ℚ)) (G ^ N)).map
        (φ 0)).IsRoot (MvPolynomial.eval₂ x c G ^ N) :=
      (_root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension _ _ hinj' (G ^ N) (φ 0) _).2 ⟨_, h0, by simp⟩
    have hb := norm_root_le_two_pow_mul_of_coeff_le (hmon.map (φ 0)) (hmon.natDegree_map (φ 0))
      (pow_nonneg hR0 N) (fun k hk => by rw [Polynomial.coeff_map]; exact hcoef k hk.le) hroot0
    rw [norm_pow] at hb
    refine hb.trans ?_
    gcongr
    · norm_num
    · exact natDegree_minpoly_pow_le hg N
  by_contra hlt
  push_neg at hlt
  rcases hR0.eq_or_lt with hR00 | hRpos
  · have h1 := key 1
    rw [← hR00] at h1 hlt
    rw [pow_one, pow_one, mul_zero] at h1
    linarith
  · set y := ‖MvPolynomial.eval₂ x c G‖ with hy
    set δ := y / R - 1 with hδ_def
    have hδ : 0 < δ := by rw [hδ_def, sub_pos, one_lt_div hRpos]; exact hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) ^ n / δ)
    have h1 := key N
    have hRδ : R * (1 + δ) = y := by rw [hδ_def]; field_simp; ring
    have h2 : y ^ N = R ^ N * (1 + δ) ^ N := by rw [← mul_pow, hRδ]
    have h3 : 1 + (N : ℝ) * δ ≤ (1 + δ) ^ N := one_add_mul_le_pow (by linarith) N
    have h4 : (2 : ℝ) ^ n < N * δ := by rwa [div_lt_iff₀ hδ] at hN
    have hRN : 0 < R ^ N := pow_pos hRpos N
    have h5 : R ^ N * 2 ^ n < R ^ N * (1 + δ) ^ N := mul_lt_mul_of_pos_left (by linarith) hRN
    linarith [mul_comm (R ^ N) ((2 : ℝ) ^ n)]

end GlobalTheory
