import Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem norm_psi_one (b w : ℂ) : ‖G.psi b w‖ = 1 := by
  unfold G.psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem isCompact_roots (n : ℕ) (hn : 0 < n) (K : Set ℂ) (hK : IsCompact K) :
    IsCompact {z : ℂ | z ^ n ∈ K} := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage (continuous_pow n)) ?_
  refine isBounded_iff_forall_norm_le.2 ⟨max 1 R, fun z hz => ?_⟩
  have h1 : ‖z ^ n‖ ≤ R := hR _ hz
  rw [norm_pow] at h1
  by_cases hz1 : ‖z‖ ≤ 1
  · exact le_trans hz1 (le_max_left _ _)
  · push Not at hz1
    have : ‖z‖ ≤ ‖z‖ ^ n := by
      calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z‖ ^ n := pow_le_pow_right₀ hz1.le hn
    exact le_trans (le_trans this h1) (le_max_right _ _)

theorem germ_core (m p : ℕ) (σh : Equiv.Perm (Fin p)) (dh : Fin p → ℂ) (hdh : ∀ i, dh i ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ0 : G.Mat (p + (m + 1 + 1)) → V) (hΦ0 : PBJ.KCls Φ0)
    (l1 l2 : ℂ) (hl1 : l1 ≠ 0) (hl : l2 ^ (m + 2) = (-1) ^ (m + 3) * l1 ^ (m + 1))
    (βL : ℝ) (hψ : ∀ w : ℂ, G.psi U.betaU (l2 / l1 * w) = conj (G.psi (βL : ℂ) w))
    (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) (ρ : ℂ → ℂ → ℝ) (R0 L : ℝ)
    (hρ : ∀ x D : ℂ, x ≠ 0 → D ∈ K →
      G.OmBlock U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l1 * x⁻¹) (x ^ (m + 1) * D) ≠ 0 →
      |ρ x D| ≤ R0 ∧ |ρ x D - 1| ≤ L * ‖x‖⁻¹ ^ (2 * (m + 1))) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x D : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l1 * x⁻¹) (x ^ (m + 1) * D) -
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l2 * z)‖ ≤ C * ‖x‖⁻¹ := by
  classical
  set Ψ := U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0 with hΨ
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1

  obtain ⟨C₁, C₂, hUG⟩ := Formalism.FourierDecayAlt.P.germ_expansion_top_level
  set Nr : ℝ := ((p + (m + 1 + 1) : ℕ) : ℝ) with hNr
  have hN0 : 0 < 5 * Nr := by rw [hNr]; positivity
  set A : ℝ := (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 with hA
  set E : ℝ := 5 * Nr * (|A| + 2 * Nr ^ 2 + 1) with hEdef
  have hEq : E / (5 * Nr) = |A| + 2 * Nr ^ 2 + 1 := by
    have hNr0 : Nr ≠ 0 := by intro h0; rw [h0] at hN0; simp at hN0
    rw [hEdef]; field_simp
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hE : ∀ i ≤ C₂ * (m + 2) ^ 2, A ≤ (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) ∧
      2 * ((p + (m + 1 + 1) : ℕ) : ℝ) ^ 2 < (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) := by
    intro i _
    simp only
    rw [← hNr, hEq]
    constructor
    · have := le_abs_self A; nlinarith [sq_nonneg Nr]
    · have := abs_nonneg A; linarith
  have hl1p : l1 ^ (m + 1) ≠ 0 := pow_ne_zero _ hl1
  set Kc : Set ℂ := (fun D => l1 ^ (m + 1) * D) '' K with hKc
  have hKcc : IsCompact Kc := hK.image (continuous_const.mul continuous_id)
  have hKc0 : (0 : ℂ) ∉ Kc := by
    rintro ⟨D, hD, hD0⟩
    rcases mul_eq_zero.1 hD0 with h | h
    · exact hl1p h
    · exact hK0 (h ▸ hD)
  obtain ⟨Cst, hC⟩ := hUG p m U.betaU hβ σh dh hdh (fun _ => E) A le_rfl hE Kc hKcc hKc0
  obtain ⟨K0, hK0d⟩ := PBJ.Asm.decayAll_of_cls Φ0 hΦ0 (C₂ * (m + 2) ^ 2) E hE0
  have hct : ∀ x : ℂ, x ≠ 0 → ∀ D : ℂ, x ^ (m + 1) * D * (l1 * x⁻¹) ^ (m + 1) = l1 ^ (m + 1) * D := by
    intro x hx D
    have hxp : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    rw [mul_pow, inv_pow]
    field_simp
  set B1 : ℝ := |Cst * K0| * ‖l1‖ with hB1def
  have hB1 : 0 ≤ B1 := by positivity
  have hrem : ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖G.remainder U.betaU m (fun _ => 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D)‖ ≤ B1 * ‖x‖⁻¹ := by
    intro x hx D hD
    have ht : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)
    have h := hC V Φ0 K0 hK0d (l1 * x⁻¹) (x ^ (m + 1) * D) ht (by rw [hct x hx D]; exact ⟨D, hD, rfl⟩)
    rw [norm_mul, norm_inv] at h
    calc _ ≤ Cst * K0 * (‖l1‖ * ‖x‖⁻¹) := h
      _ ≤ |Cst * K0| * (‖l1‖ * ‖x‖⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = B1 * ‖x‖⁻¹ := by rw [hB1def]; ring

  have hm2 : ((m : ℂ) + 2) ≠ 0 := by
    have h : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [h]; exact_mod_cast (by omega : m + 2 ≠ 0)
  have hneg : ((-1 : ℂ)) ^ (m + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hl2 : l2 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hl
    exact (mul_ne_zero hneg hl1p) hl.symm
  have hs : 0 < m + 2 := by omega
  have hroots : ∀ D : ℂ, G.rootSet (m + 2) ((-1) ^ (m + 3) * (l1 ^ (m + 1) * D)) =
      (G.rootSet (m + 2) D).image (fun z => l2 * z) := by
    intro D; ext ζ
    rw [Finset.mem_image, Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs]
    constructor
    · intro hζ
      refine ⟨ζ / l2, (Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).2 ?_, by field_simp⟩
      rw [div_pow, hζ, hl]
      field_simp
    · rintro ⟨z, hz, rfl⟩
      rw [Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs] at hz
      rw [mul_pow, hl, hz]; ring
  have hmain : ∀ x : ℂ, x ≠ 0 → ∀ D : ℂ,
      G.mainTerm U.betaU m (fun _ => 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D * (l1 * x⁻¹) ^ (m + 1)) =
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) Ψ (l2 * z) := by
    intro x hx D
    unfold G.mainTerm
    rw [hct x hx D, hroots D, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hl2 h)]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    have harg : ((m : ℂ) + 2) * (l2 * z) / (l1 * x⁻¹) = l2 / l1 * (((m : ℂ) + 2) * z * x) := by
      field_simp
    rw [mul_one, harg, hψ]

  obtain ⟨KΨ, hΨc, hΨd⟩ := LastBlockContinuity.lastBlock_decay U.betaU p (m + 1 + 1) (by omega) σh dh hdh Φ0 hΦ0
    (2 * ((((m + 1 : ℕ) : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1)) + 1)
  have hOmc : ContinuousOn (G.OmLong U.betaU (m + 1) Ψ) {0}ᶜ :=
    LastBlockContinuity.omLong_continuousOn U.betaU (m + 1) Ψ hΨc KΨ _ (by linarith) hΨd
  set Kz : Set ℂ := {z : ℂ | z ^ (m + 2) ∈ K} with hKz
  have hKzc : IsCompact Kz := isCompact_roots (m + 2) hs K hK
  have hKz0 : ∀ z ∈ Kz, z ≠ 0 := by
    intro z hz h0
    rw [hKz, Set.mem_ofPred_eq, h0, zero_pow (by omega)] at hz
    exact hK0 hz
  have hfc : ContinuousOn (fun z : ℂ => ‖l2 * z‖ ^ ((m + 1) ^ 2) * ‖G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖) Kz := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    refine ContinuousOn.norm ?_
    refine hOmc.comp (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
    exact mul_ne_zero hl2 (hKz0 z hz)
  obtain ⟨M1, hM1⟩ := hKzc.exists_bound_of_continuousOn hfc
  set M : ℝ := ((m : ℝ) + 2) * max M1 0 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hmb : ∀ x : ℂ, ∀ D ∈ K, ‖((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
      (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
        G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖ ≤ M := by
    intro x D hD
    have hterm : ∀ z ∈ G.rootSet (m + 2) D, ‖(((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) *
        conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) • G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖ ≤ max M1 0 := by
      intro z hz
      have hzK : z ∈ Kz := by
        show z ^ (m + 2) ∈ K
        rw [(Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).1 hz]
        exact hD
      rw [norm_smul, norm_mul, Complex.norm_conj, norm_psi_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have := hM1 z hzK
      rw [Real.norm_eq_abs] at this
      exact le_trans (le_trans (le_abs_self _) this) (le_max_left _ _)
    have hcard : ((G.rootSet (m + 2) D).card : ℝ) ≤ (m : ℝ) + 2 := by
      have h1 : (G.rootSet (m + 2) D).card ≤ m + 2 :=
        le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots (m + 2) D)
      exact_mod_cast h1
    have hsum := norm_sum_le_of_le (G.rootSet (m + 2) D) hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [norm_smul, norm_inv]
    have hn2 : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
      have h : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn2]
    have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    calc ((m : ℝ) + 2)⁻¹ * ‖∑ z ∈ G.rootSet (m + 2) D, _‖
        ≤ 1 * (((m : ℝ) + 2) * max M1 0) := by
          apply mul_le_mul (inv_le_one_of_one_le₀ (by linarith)) _ (norm_nonneg _) zero_le_one
          exact hsum.trans (mul_le_mul_of_nonneg_right hcard (le_max_right _ _))
      _ = M := by rw [one_mul]

  refine ⟨B1 + (|L| + |R0| + 1) * (B1 + M), fun x hx D hD => ?_⟩
  set X : V := ((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D)
    with hX
  set main : V := ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
      (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
        G.OmLong U.betaU (m + 1) Ψ (l2 * z) with hmaindef
  have hXm : ‖X - main‖ ≤ B1 * ‖x‖⁻¹ := by
    have h := hrem x hx D hD
    unfold G.remainder at h
    rw [hmain x hx D] at h
    exact h
  have hmM : ‖main‖ ≤ M := hmb x D hD
  have hexpr : ((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x D : ℝ) : ℂ) •
      G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D) = ((ρ x D : ℝ) : ℂ) • X := by
    rw [hX, smul_smul]; push_cast; ring_nf
  rw [hexpr]
  set y : ℝ := ‖x‖⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hC0 : 0 ≤ (|L| + |R0| + 1) * (B1 + M) := by positivity
  by_cases hOm : G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D) = 0
  · have hX0 : X = 0 := by rw [hX, hOm, smul_zero]
    rw [hX0, smul_zero]
    rw [hX0] at hXm
    calc ‖0 - main‖ ≤ B1 * y := hXm
      _ ≤ (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := mul_le_mul_of_nonneg_right (by linarith) hy0
  · obtain ⟨hR, hLb⟩ := hρ x D hx hD hOm
    have key : ((ρ x D : ℝ) : ℂ) • X - main = (X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [key]
    have hXb : ‖X‖ ≤ B1 * y + M := by
      calc ‖X‖ = ‖(X - main) + main‖ := by rw [sub_add_cancel]
        _ ≤ ‖X - main‖ + ‖main‖ := norm_add_le _ _
        _ ≤ B1 * y + M := add_le_add hXm hmM
    have hsc : ‖((ρ x D - 1 : ℝ) : ℂ) • X‖ = |ρ x D - 1| * ‖X‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have htri := norm_add_le (X - main) (((ρ x D - 1 : ℝ) : ℂ) • X)
    rw [hsc] at htri
    have hR0 : 0 ≤ R0 := le_trans (abs_nonneg _) hR
    by_cases hx1 : 1 ≤ ‖x‖
    · have hy1 : y ≤ 1 := by rw [hy]; exact inv_le_one_of_one_le₀ hx1
      have hpow : y ^ (2 * (m + 1)) ≤ y := by
        calc y ^ (2 * (m + 1)) ≤ y ^ 1 := pow_le_pow_of_le_one hy0 hy1 (by omega)
          _ = y := pow_one y
      have h1 : |ρ x D - 1| ≤ |L| * y := by
        calc |ρ x D - 1| ≤ L * y ^ (2 * (m + 1)) := hLb
          _ ≤ |L| * y ^ (2 * (m + 1)) := mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
          _ ≤ |L| * y := mul_le_mul_of_nonneg_left hpow (abs_nonneg L)
      have h2 : ‖X‖ ≤ B1 + M := by
        have : B1 * y ≤ B1 := mul_le_of_le_one_right hB1 hy1
        linarith
      have h3 : |ρ x D - 1| * ‖X‖ ≤ |L| * y * (B1 + M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖(X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X‖ ≤ ‖X - main‖ + |ρ x D - 1| * ‖X‖ := htri
        _ ≤ B1 * y + |L| * y * (B1 + M) := add_le_add hXm h3
        _ = B1 * y + (|L| * (B1 + M)) * y := by ring
        _ ≤ B1 * y + ((|L| + |R0| + 1) * (B1 + M)) * y := by
          have : |L| * (B1 + M) ≤ (|L| + |R0| + 1) * (B1 + M) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg R0]) (by positivity)
          linarith [mul_le_mul_of_nonneg_right this hy0]
        _ = (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := by ring
    · push Not at hx1
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hy1 : 1 ≤ y := by rw [hy]; exact (one_le_inv₀ hxpos).2 hx1.le
      have h1 : |ρ x D - 1| ≤ |R0| + 1 := by
        have hr := abs_le.1 hR
        have hR' := le_abs_self R0
        exact abs_le.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have h2 : ‖X‖ ≤ (B1 + M) * y := by
        have : M ≤ M * y := le_mul_of_one_le_right hM0 hy1
        calc ‖X‖ ≤ B1 * y + M := hXb
          _ ≤ B1 * y + M * y := by linarith
          _ = (B1 + M) * y := by ring
      have h3 : |ρ x D - 1| * ‖X‖ ≤ (|R0| + 1) * ((B1 + M) * y) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖(X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X‖ ≤ ‖X - main‖ + |ρ x D - 1| * ‖X‖ := htri
        _ ≤ B1 * y + (|R0| + 1) * ((B1 + M) * y) := add_le_add hXm h3
        _ = B1 * y + ((|R0| + 1) * (B1 + M)) * y := by ring
        _ ≤ B1 * y + ((|L| + |R0| + 1) * (B1 + M)) * y := by
          have : (|R0| + 1) * (B1 + M) ≤ (|L| + |R0| + 1) * (B1 + M) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) (by positivity)
          linarith [mul_le_mul_of_nonneg_right this hy0]
        _ = (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := by ring

end

end Formalism.FourierDecayAlt.P.GermRateSplit
