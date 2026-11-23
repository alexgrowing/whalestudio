import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.InvBuild
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitO

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma omega_fin {E : Type} [Field E] [NumberField E] [IsCMField E] :
    ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
      ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E) := by
  obtain ⟨n, ω, hωB, hspan⟩ := omega_exists' (E := E)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := ℚ) (fun j => (ω j : E))
  have htop : Submodule.span ℚ (Set.range ((fun j => (ω j : E)) ∘ a)) = ⊤ := by
    rw [hsp, eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hspan _
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank ℚ E := by
    rw [← finrank_span_eq_card hli, htop, finrank_top]
  let e : Fin (Module.finrank ℚ E) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun j => ω (a (e j)), hli.comp e e.injective, fun j τ => hωB _ τ⟩

set_option maxHeartbeats 1000000 in
theorem char_main (hx : Ext.All) : CharStatement := by
  intro E _ _ _ X DF P I hI σ ρ hρ
  classical
  have hNP : Ext.NearestPlane := hx.2.2.2.2.1
  obtain ⟨ω, hω, hωB⟩ := omega_fin (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hF1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hrd := P.hrd
  have hmf : ((P.m : ℝ)) ^ 4 ≤ PT.f E := by exact_mod_cast P.hmf
  have hf2 := P.hf2
  have hdR : (dstar (E := E) P.m : ℝ) = 2 * PT.f E * P.m := by simp [dstar]
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hFd : (PT.f E : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hΩ2 : omStar (E := E) ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hK0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E := by positivity
  have hK : (dstar (E := E) P.m : ℝ) * omStar (E := E) ^ 2 / 4 ≤
      ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ^ 2 := by
    rw [hΩ2]
    have h3 : (PT.f E : ℝ) ^ 3 ≤ (dstar (E := E) P.m : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hFd 3
    have h4 : 0 ≤ (dstar (E := E) P.m : ℝ) * PT.rd E ^ 2 := by positivity
    calc (dstar (E := E) P.m : ℝ) * (4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2) / 4
        = ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (PT.f E : ℝ) ^ 3 := by ring
      _ ≤ ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (dstar (E := E) P.m : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 h4
      _ = _ := by ring
  have hD : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
    obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
    rw [hρ', dstar, mul_assoc, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hρ'm)
  obtain ⟨xb, ub, hxub, hspan, hbnd⟩ := exists_short_real_span hI
  have hex : ∀ W : Submodule ℂ (Vsp X.dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg X.L I, prj σ y ∉ W ∧
        ‖y‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
    intro W hW
    obtain ⟨j, hj⟩ := exists_out (by exact hρ) ub hspan W hW
    exact ⟨ub j, ⟨xb j, (hxub j).1, (hxub j).2⟩, hj, hbnd j⟩
  have hρm : ρ ≤ P.m := rho_le hI ω hω (by exact hρ)
  have hρmR : (ρ : ℝ) ≤ P.m := by exact_mod_cast hρm
  obtain ⟨χ, w, R, μ, ε, hinv⟩ := inv_build hNP X.stable hI.stable hI.iso (sep_X hI) ω hω
    (omStar (E := E)) hωB (dstar (E := E) P.m) hD σ ρ _ _ hK0 hK hex ρ le_rfl
  obtain ⟨hχX, hwW, hort, hdec, hεz, hεn, hRb, hred, hflag, hμB⟩ := hinv
  have hph : 0 ≤ P.ph := by
    rw [Par.ph, PT.ph]; split_ifs
    · positivity
    · exact le_rfl
  have hs2 : Real.sqrt 2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

  have hcmp : ∀ s : Fin ρ, 30 ≤ 30 * (ρ : ℝ) ^ 2 ∧
      Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) := by
    intro s
    have : (1 : ℝ) ≤ ρ := by exact_mod_cast (show 1 ≤ ρ by have := s.2; omega)
    constructor <;> nlinarith [Real.sqrt_nonneg 2]
  have hχn : ∀ s : Fin ρ, ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by
    intro s
    have h1 := (hRb s s.2).2
    have h2 := (hcmp s).2
    have hμ := (hred s s.2).1
    have h3 : 0 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by positivity
    have := mul_le_mul_of_nonneg_right h2 h3
    nlinarith
  refine ⟨fun s => w s, fun s => (hχX s s.2).choose, fun s => χ s, fun s => R s,
    fun s s' => ε s s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have := Wk_le hI.stable σ χ (s + 1) (fun j hj => hχX j (by omega)) (hwW s s.2)
    exact ⟨(Submodule.mem_inf.mp this).2, (Submodule.mem_inf.mp this).1⟩
  · intro s s'
    show Hf (w s) (w s') = _
    rw [Hf_eq_inner, hort s' s'.2 s s.2]
    by_cases h : s = s'
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.ext e).symm), if_neg h]
  · intro s
    exact (hχX s s.2).choose_spec
  · intro s s' h
    exact hεz s s.2 s' (Fin.lt_def.mp h).le
  · intro s
    have hsum : ∑ s' : Fin ρ, ‖ε s s'‖ ^ 2 = ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := by
      rw [show (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) = ∑ i ∈ Finset.range ρ, ‖ε s i‖ ^ 2 from
        Fin.sum_univ_eq_sum_range (fun i => ‖ε s i‖ ^ 2) ρ]
      symm
      refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
      rw [hεz s s.2 i (by simpa using hi), norm_zero]; norm_num
    have hb := hεn s s.2
    have hA := (hcmp s).1
    have hq : 0 ≤ 1 / (30 * (ρ : ℝ) ^ 2) := by positivity
    constructor
    · show Real.sqrt (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) ≤ _
      rw [hsum, ← Real.sqrt_sq hq]; exact Real.sqrt_le_sqrt hb
    · show ∑ s' : Fin ρ, ‖ε s s'‖ ≤ _
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s' : Fin ρ => ‖ε s s'‖)
      simp only [Finset.card_univ, Fintype.card_fin] at hcs
      rw [hsum] at hcs
      have h0 : 0 ≤ ∑ s' : Fin ρ, ‖ε s s'‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h1 : (∑ s' : Fin ρ, ‖ε s s'‖) ^ 2 ≤ (Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        calc _ ≤ (ρ : ℝ) * ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := hcs
          _ ≤ (ρ : ℝ) * (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = _ := by ring
      have hb0 : 0 ≤ Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2) := by positivity
      nlinarith
  · intro s v hv
    have hR : (R s : ℂ) ≠ 0 := by
      have h1 := (hRb s s.2).1
      have hμ := (hred s s.2).1
      have hA := (hcmp s).1
      have h2 : 0 < (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := mul_pos (mul_pos (by linarith) hK0) (by linarith)
      have : 0 < R s := lt_of_lt_of_le h2 h1
      exact_mod_cast this.ne'
    show Hf v (χ s) / (R s : ℂ) = Hf v (w s) + ∑ s' : Fin ρ, ε s s' * Hf v (w s')
    rw [← Hf_prj_right hv (χ s), hdec s s.2]
    simp only [Hf_eq_inner, inner_smul_left, inner_add_left, sum_inner, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [mul_div_cancel_left₀ _ hR]
    congr 1
    rw [show (∑ s' : Fin ρ, ε s s' * inner ℂ (w s') v) = ∑ i ∈ Finset.range ρ, ε s i * inner ℂ (w i) v from
      Fin.sum_univ_eq_sum_range (fun i => ε s i * inner ℂ (w i) v) ρ]
    refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
    rw [hεz s s.2 i (by simpa using hi), zero_mul]
  · intro s
    show ‖χ s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s
    have hRs := (hRb s s.2).1
    have hμ := (hred s s.2).1
    have hA := (hcmp s).1
    have hn := hχn s
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have h1 : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hX : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by nlinarith
    have e15 : (1.5 : ℝ) = 3 / 2 := by norm_num
    rw [e15]
    constructor
    · nlinarith
    · nlinarith [Real.pi_gt_three]
  · intro s y hy uy hU
    show |2 * inner ℝ (χ s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2
    have huy : uy ∈ Xg X.L I := ⟨y, hy, hU⟩
    have hA := (hcmp s).1
    have hM : 3 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ≤ M1 (E := E) P.m := by
      rw [M1]
      have h1 : (ρ : ℝ) ^ 2 ≤ (P.m : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 2
      have h2 := mul_le_mul_of_nonneg_right h1 hK0.le
      nlinarith
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hM1 : 1 ≤ M1 (E := E) P.m := by nlinarith
    have e1 : |2 * inner ℝ (χ s) uy| ≤ 2 * (‖χ s‖ * ‖uy‖) := by
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    rcases (hred s s.2).2 uy huy with h | h
    · have := mul_le_mul_of_nonneg_right hM1 (sq_nonneg ‖uy‖)
      linarith
    · have hn := hχn s
      have h2 : ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * ‖uy‖ :=
        le_trans hn (mul_le_mul_of_nonneg_left h (by positivity))
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg uy)
      have h4 := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖uy‖)
      nlinarith
  · intro s
    show ‖χ s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph
    have hn := hχn s
    have hμ := (hred s s.2).1
    have hB := hμB s s.2
    have h0 : 0 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by positivity
    have h1 : ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (PT.f E : ℝ))) := by
      calc ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * μ s ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    have hFpos : (0 : ℝ) < (PT.f E : ℝ) := by linarith
    have hd4 : (dstar (E := E) P.m : ℝ) ^ 4 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by
      rw [hdR]
      have h5 : 16 * (PT.f E : ℝ) ^ 4 * (P.m : ℝ) ^ 4 ≤ 16 * (PT.f E : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_left hmf (by positivity : (0 : ℝ) ≤ 16 * (PT.f E : ℝ) ^ 4)
        nlinarith
      have h6 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hf2 2
        nlinarith
      have h7 : 16 * (PT.f E : ℝ) ^ 4 ≤ PT.rd E * PT.rd E ^ 2 := by nlinarith
      have h8a := mul_le_mul_of_nonneg_left h7 hFpos.le
      have h8b : 0 ≤ (PT.f E : ℝ) * PT.rd E ^ 3 := by positivity
      have h8 : 16 * (PT.f E : ℝ) ^ 5 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by nlinarith
      nlinarith
    have hρ4 : (ρ : ℝ) ^ 4 ≤ (P.m : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 4
    have hdF : (dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ) ≤ 8 * PT.rd E ^ 3 := by rw [div_le_iff₀ hFpos]; linarith
    have hC : 0 ≤ 2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph := mul_nonneg (by positivity) hph
    refine h1.trans ?_
    calc _ = (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((ρ : ℝ) ^ 4 * ((dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ))) := by
          field_simp; ring
      _ ≤ (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((P.m : ℝ) ^ 4 * (8 * PT.rd E ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρ4 hdF (by positivity) (by positivity)) hC
      _ = Cchi (E := E) P.m * P.ph := by rw [Cchi, RR]; ring

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
