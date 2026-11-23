import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyEqRankPartMul

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open Polynomial ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CharpolyFrobDense

namespace GlobalTheory.ExpFrame.CongrBlock

theorem norm_le_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (t : Γ →* Kˣ) (ht : Continuous t) (g : Γ) : ‖((t g : Kˣ) : K)‖ ≤ 1 := by
  have hc : Continuous fun g => ‖((t g : Kˣ) : K)‖ := (Units.continuous_val.comp ht).norm
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  have hpow : ∀ k : ℕ, ‖((t g : Kˣ) : K)‖ ^ k ≤ M := fun k => by
    have := hM ⟨g ^ k, Set.mem_univ _, rfl⟩
    simpa [map_pow, Units.val_pow_eq_pow_val, norm_pow] using this
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M).exists
  exact absurd (hpow k) (not_le.2 hk)

theorem continuous_character_of_rankOneRep_continuous {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    (χ : Γ →* Kˣ) (h : Continuous (GlobalTheory.TripleGal.rk1 χ)) : Continuous fun g => ((χ g : Kˣ) : K) := by
  have h1 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 :=
    (Units.continuous_val.comp h).matrix_elem 0 0
  convert h1 using 1
  funext g
  simp [GlobalTheory.TripleGal.rk1]

theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (j : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff j =
      if j ≤ n then (-1) ^ j * (q : L) ^ (j * (j - 1) / 2) * a j else 0 := by
  simp only [Formalism.L2.Col.heckePolyOf, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_sub_eq_reverse {K : Type} [Field K] {p q : K[X]} {n : ℕ} (hp : p.natDegree = n)
    (hq : q.natDegree = n) (k : ℕ) (hk : k ≤ n) :
    (p - q).coeff k = (p.reverse - q.reverse).coeff (n - k) := by
  simp only [coeff_sub, coeff_reverse, hp, hq, revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk]

theorem norm_sysOf_sub_lt {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) {θ θ0 : I → Qbar l}
    (h : ∀ i, ‖θ i - θ0 i‖ < 1) (P : Pl) (k : ℕ) : ‖sysOf n pt θ P k - sysOf n pt θ0 P k‖ < 1 := by
  unfold sysOf
  split_ifs
  · exact h _
  · simp

theorem norm_coeff_hecke_sub_lt {l : ℕ} [Fact l.Prime] (n q : ℕ) (a b : ℕ → Qbar l) (w : Qbar l) (hw : ‖w‖ ≤ 1)
    (hab : ∀ k, ‖a k - b k‖ < 1) (j : ℕ) :
    ‖(Formalism.L2.Col.heckePolyOf n q (fun k => a k * w ^ k) -
      Formalism.L2.Col.heckePolyOf n q (fun k => b k * w ^ k)).coeff j‖ < 1 := by
  rw [coeff_sub, coeff_heckePolyOf, coeff_heckePolyOf]
  split_ifs
  · have e : (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (a j * w ^ j) -
        (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (b j * w ^ j) =
        (-1) ^ j * ((q : Qbar l) ^ (j * (j - 1) / 2) * w ^ j) * (a j - b j) := by ring
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖(q : Qbar l)‖ ^ (j * (j - 1) / 2) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    have h2 : ‖w‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    calc _ ≤ ‖a j - b j‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h1 (pow_nonneg (norm_nonneg _) _) h2)
      _ < 1 := hab j
  · simp

theorem blockFor_of_congr : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  intro hC E Ω _ _ _ _ _ _ l _ ι _ inc P W F Bk hG mu θ θ0 hmu hθ hθ0 hBk hcl
  obtain ⟨Pl, pt, Fn, ep, hep, h1, h2⟩ := hG
  obtain ⟨r, J, hJ, hr, hrR⟩ := h1 mu θ hmu hθ
  obtain ⟨a, ρ, χ, bot, hat, hρ, hχ, hbot, hρR⟩ := h2 θ0 hθ0 hBk
  refine ⟨ep, J, bot, hep, ⟨r, a, ρ, χ, hat, hr, hρ, hχ, ?_⟩, fun τ => ⟨fun b => hJ τ b, hbot τ⟩⟩

  set p : G E Ω → Polynomial (Qbar l) := fun σ => (r σ).val.charpoly with hp
  set q : G E Ω → Polynomial (Qbar l) := fun σ =>
    (ρ σ).val.charpoly * ∏ s, (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)) with hq
  have dp : ∀ σ, (p σ).natDegree = P.Nr := fun σ => by
    simp [hp, Matrix.charpoly_natDegree_eq_dim]
  have dq : ∀ σ, (q σ).natDegree = P.Nr := fun σ => by
    simp only [hq]
    rw [(Matrix.charpoly_monic _).natDegree_mul (monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _),
      Matrix.charpoly_natDegree_eq_dim, natDegree_finset_prod_X_sub_C_eq_card, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, hat]

  have cp : CoeffCont p := fun k =>
    (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix P.Nr k).comp (Units.continuous_val.comp hr.1)
  have cq : CoeffCont q := by
    have c1 : CoeffCont fun σ : G E Ω => (ρ σ).val.charpoly := fun k =>
      (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a k).comp (Units.continuous_val.comp hρ)
    have c2 := coeffCont_prod Finset.univ (fun s (σ : G E Ω) => (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)))
      (fun s _ => coeffCont_X_sub_C (continuous_character_of_rankOneRep_continuous (χ s) (hχ s).1))
    exact c1.mul c2

  set good : G E Ω → Prop := fun σ => ∀ k, ‖(p σ - q σ).coeff k‖ < 1 with hgood
  have hclosed : IsClosed {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    have : {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} =
        ⋂ k, (fun σ : G E Ω => (p (σ ^ (Fn.sgn : ℤ)) - q (σ ^ (Fn.sgn : ℤ))).coeff k) ⁻¹' Metric.ball 0 1 := by
      ext σ; simp [hgood]
    rw [this]
    refine isClosed_iInter fun k => (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage ?_
    have hz := continuous_zpow (G := G E Ω) (Fn.sgn : ℤ)
    simp only [coeff_sub]
    exact ((cp k).comp hz).sub ((cq k).comp hz)

  have hS := Fn.cofin
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) hC hS
  have hsub : {σ : G E Ω | ∃ v : HeightOneSpectrum (𝓞 E),
      v ∉ {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range Fn.lab} ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ IsFrob B (normV v) σ} ⊆
      {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    rintro σ ⟨v, hv, hd, B, hB, hσ⟩
    have hpr : (Ideal.absNorm v.asIdeal).Prime := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    have hv' : v ∈ Set.range Fn.lab := by
      by_contra h; exact hv ⟨hpr, h⟩
    obtain ⟨P0, rfl⟩ := hv'
    have e1 := hrR P0 B σ hB hσ
    have e2 := hρR P0 B σ hB hσ
    have hw := norm_le_one_of_compact Fn.tw Fn.cont (σ ^ (Fn.sgn : ℤ))
    intro k
    by_cases hk : k ≤ P.Nr
    · rw [coeff_sub_eq_reverse (dp _) (dq _) k hk]
      simp only [hp, hq]
      rw [e1, e2]
      exact norm_coeff_hecke_sub_lt _ _ _ _ _ hw (norm_sysOf_sub_lt P.Nr pt hcl P0) _
    · push_neg at hk
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [dp]; exact hk),
        coeff_eq_zero_of_natDegree_lt (by rw [dq]; exact hk)]
      simp
  have hall : ∀ σ : G E Ω, good (σ ^ (Fn.sgn : ℤ)) := fun σ => by
    have h := closure_minimal hsub hclosed
    rw [hD.closure_eq] at h
    exact h (Set.mem_univ σ)
  intro σ k
  have h := hall (σ ^ (Fn.sgn : ℤ)) k
  have e : (σ ^ (Fn.sgn : ℤ)) ^ (Fn.sgn : ℤ) = σ := by
    rw [← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one]
  rw [e] at h
  exact h

end GlobalTheory.ExpFrame.CongrBlock
