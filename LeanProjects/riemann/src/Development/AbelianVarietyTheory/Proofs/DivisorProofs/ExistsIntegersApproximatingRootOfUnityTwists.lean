import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGeStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

theorem v_pow_sub_pow_lt_one {C : Type} [Field C] (v : Valuation C NNReal) {x y : C} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  rw [← geom_sum₂_mul x y n, map_mul]
  have hs : v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le hx) zero_le (pow_le_one₀ zero_le hy)
  calc v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * v (x - y) ≤ 1 * v (x - y) :=
        mul_le_mul_of_nonneg_right hs zero_le
    _ = v (x - y) := one_mul _
    _ < 1 := hxy

private lemma exists_mem_sub_one_mem_of_maximal_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (h : P ≠ Q) : ∃ a ∈ P, a - 1 ∈ Q := by
  have htop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hQ h
  have h1 : (1 : R) ∈ P ⊔ Q := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  refine ⟨a, ha, ?_⟩
  have hb' : a - 1 = -b := by rw [← hab]; ring
  rw [hb']
  exact Q.neg_mem hb

theorem exists_sub_one_mem_and_mem {R ι : Type} [CommRing R] [Finite ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsMaximal)
    (t : ι) : ∃ e : R, e - 1 ∈ P t ∧ ∀ i, P i ≠ P t → e ∈ P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hc : ∀ i, ∃ a : R, (P i ≠ P t → a ∈ P i) ∧ a - 1 ∈ P t := by
    intro i
    by_cases hi : P i = P t
    · exact ⟨1, fun h => absurd hi h, by simp⟩
    · obtain ⟨a, ha, ha1⟩ := exists_mem_sub_one_mem_of_maximal_ne (hP i) (hP t) hi
      exact ⟨a, fun _ => ha, ha1⟩
  choose a ha using hc
  refine ⟨∏ i, a i, ?_, ?_⟩
  · refine Ideal.Quotient.eq.1 ?_
    rw [map_prod, map_one]
    exact Finset.prod_eq_one fun i _ => by
      rw [← map_one (Ideal.Quotient.mk (P t))]
      exact Ideal.Quotient.eq.2 (ha i).2
  · intro i hi
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ ((ha i).1 hi)

private lemma pow_pow_mul_eq_self_of_pow_sub_one_eq_one {C : Type} [Field C] {z : C} {h : ℕ} (p : ℕ) (hp : 0 < p)
    (hz : z ^ (p ^ h - 1) = 1) (M : ℕ) : z ^ p ^ (h * M) = z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    have hph : p ^ h = p ^ h - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [hph, pow_succ, hz, one_mul]

theorem exists_approx_root_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  intro E _ _ _ H l c p _ T io X τ h hh lab hlab z hz ha₀ r
  classical
  obtain ⟨a₀, ha₀⟩ := ha₀
  have hp : p.Prime := Fact.out
  haveI : NeZero h := ⟨hh.ne'⟩
  obtain ⟨e, he1, he⟩ := exists_sub_one_mem_and_mem (fun σ : E →+* ℂ => primeBelow io X σ)
    (fun σ => (primeBelow_isMaximal_card E H l c p T io X σ).1) τ
  have hv1 : ∀ σ a, X.v (embX io X σ a) ≤ 1 := fun σ a => v_embX_le_one io X σ a
  have hvz : X.v z ≤ 1 := by
    have hn : p ^ h - 1 ≠ 0 := by
      have : 2 ≤ p ^ h := le_trans hp.two_le (Nat.le_self_pow hh.ne' p)
      omega
    have h1 : X.v z ^ (p ^ h - 1) ≤ 1 := by rw [← map_pow, hz, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le hn).1 h1
  have hvzs : ∀ n : ℕ, X.v (z ^ n) ≤ 1 := fun n => by rw [map_pow]; exact pow_le_one₀ zero_le hvz
  have he1' : X.v (embX io X τ e - 1) < 1 := by
    have : X.v (embX io X τ (e - 1)) < 1 := he1
    rwa [map_sub, map_one] at this
  have hτb : X.v (embX io X τ (e * a₀) - z) < 1 := by
    have hsplit : embX io X τ (e * a₀) - z =
        (embX io X τ e - 1) * embX io X τ a₀ + (embX io X τ a₀ - z) := by rw [map_mul]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ha₀
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le he1' (hv1 τ a₀)
  have hlabb : ∀ s : ZMod h, X.v (embX io X (lab s) (e * a₀) - z ^ p ^ s.val) < 1 := by
    intro s
    have hsplit : embX io X (lab s) (e * a₀) - z ^ p ^ s.val =
        (embX io X (lab s) (e * a₀) - embX io X τ (e * a₀) ^ p ^ s.val) +
          (embX io X τ (e * a₀) ^ p ^ s.val - z ^ p ^ s.val) := by ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (hlab s (e * a₀))
      (v_pow_sub_pow_lt_one X.v (hv1 τ _) hvz hτb _)
  have hoth : ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → X.v (embX io X σ (e * a₀)) < 1 := by
    intro σ hσ
    have hmem : X.v (embX io X σ e) < 1 := he σ hσ
    rw [map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hmem (hv1 σ a₀)
  have hs : ∀ s : ZMod h, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤
      vX_vp X (embX io X (lab s) (e * a₀) ^ p ^ N - (z ^ p ^ s.val) ^ p ^ N) := by
    intro s
    exact GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ _ ((isIntV_iff X _).2 (hv1 _ _))
      ((isIntV_iff X _).2 (hvzs _)) ((vX_vp_pos_iff X _).2 (hlabb s)) r
  have hσ : ∀ σ : E →+* ℂ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → primeBelow io X σ ≠ primeBelow io X τ →
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ (e * a₀) ^ p ^ N) := by
    intro σ
    by_cases hne : primeBelow io X σ = primeBelow io X τ
    · exact ⟨0, fun _ _ h' => absurd hne h'⟩
    · have hlt : X.v (embX io X σ (e * a₀) - 0) < 1 := by rw [sub_zero]; exact hoth σ hne
      obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ 0 ((isIntV_iff X _).2 (hv1 _ _))
        ((isIntV_iff X _).2 (by simp)) ((vX_vp_pos_iff X _).2 hlt) r
      refine ⟨N₀, fun N hN _ => ?_⟩
      have := hN₀ N hN
      rwa [zero_pow (pow_ne_zero _ hp.ne_zero), sub_zero] at this
  choose Ns hNs using hs
  choose Nσ hNσ using hσ
  set M := (∑ s, Ns s) + ∑ σ, Nσ σ with hM
  have hMN : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  refine ⟨(e * a₀) ^ p ^ (h * M), fun s => ?_, fun σ hne => ?_⟩
  · have hzN : (z ^ p ^ s.val) ^ p ^ (h * M) = z ^ p ^ s.val := by
      rw [← pow_mul, mul_comm, pow_mul, pow_pow_mul_eq_self_of_pow_sub_one_eq_one p hp.pos hz M]
    have hle : Ns s ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        (Nat.le_add_right _ _)) hMN
    have := hNs s (h * M) hle
    rwa [hzN, ← map_pow] at this
  · have hle : Nσ σ ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ))
        (Nat.le_add_left _ _)) hMN
    have := hNσ σ (h * M) hle hne
    rwa [← map_pow] at this

end GlobalTheory.PrimePart
