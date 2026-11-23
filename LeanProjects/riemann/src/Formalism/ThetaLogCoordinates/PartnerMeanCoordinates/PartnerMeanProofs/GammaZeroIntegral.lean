import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMXB

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

theorem gamma_zero_integral {p : ℕ} [Fact p.Prime] (K r : ℕ) (LLw : Letters (K + 1)) (ρ : Fin r) (n a : ℕ) (κ : ℝ)
    (hS : LLw.total ≤ n) (hn : n ≤ a) (h4 : (K + 2) * (r * Nat.log p a) ≤ ⌈κ⌉₊)
    (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hf : f ∈ PolZ p r LLw) (hf' : f' ∈ PolZ p r LLw) :
    ‖(p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p LLw ρ n f) (freeze p LLw ρ n f') /
      ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])))‖ ≤ 1 := by
  classical
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)
  obtain ⟨hfP, hfI⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hfP', hfI'⟩ := Submodule.mem_inf.mp hf'
  obtain ⟨hFP, -, hFI⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP
  obtain ⟨-, -, hFI'⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'
  set F := freeze p LLw ρ n f with hF
  set F' := freeze p LLw ρ n f' with hF'
  have hc := gammaIntegralityLemmas.intPol_coeff F (hFI hfI)
  have hc' := gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')
  set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')
  have hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p]) := by
    rw [hDen]; push_cast; ring
  rw [hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]
  refine gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_
  intro m hm
  have hmd : MultiDeg (LLw.snoc n) m := by
    rw [Pol, mem_restrictSupport_iff] at hFP
    exact hFP (Finset.mem_coe.mpr hm)
  set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum
  have hNum0 : Num ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hwf : gammaIntegralityLemmas.wf (p := p) m = (Num : ℚ_[p]) := by
    rw [hNum, gammaIntegralityLemmas.wf]; push_cast; rfl
  rw [hwf]
  have hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i := fun i => hmd i
  have hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ a := by
    intro i
    rw [hδ]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [FrozenVariableComponents.snoc_deg_last]; exact hn
    · rw [FrozenVariableComponents.snoc_deg_castSucc]
      exact (gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)
  have h1 := gammaIntegralityLemmas.vW_ge (p := p) m (T := a) (B := Nat.log p (a)) le_rfl hT
  rw [Fin.sum_univ_castSucc] at h1
  simp only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1
  have h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial +
      ∑ i, padicValNat p (LLw.deg i).factorial := by
    rw [hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne',
      gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤
      padicValNat p n.factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial hS
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne')
      (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']
    omega
  have h5 := gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m)
    Num Den hNum0 hDen0 1 norm_one (by
      have : (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ) := by
        have : padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊ := by
          rw [h2]
          have h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤
              padicValNat p Num + (K + 2) * (r * Nat.log p (a)) := h1
          omega
        exact_mod_cast this
      omega)
  rw [one_mul] at h5
  exact h5

theorem tieOpsX_main : TieOpsX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ _hp2 hr hρ hadm hE hSn hdeg hL hκ hHP hHW nb f U V dg fw hf hUV hfw i
  classical
  have hK : T.pos i + 1 + 1 ≤ N := hK_of_adm LL T hadm i
  have hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i := by
    rw [S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i
  have hni : n i ≤ Xb := by
    have := hdeg ⟨T.pos i + 1, by omega⟩
    rwa [setTies_deg_eta LL T hadm i n (by omega)] at this
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ, coef =
      (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN =
      ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN := ⟨_, rfl⟩
  have hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' =
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    rw [gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]
    ring
  let B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i))
      (FfL p (LL.setTies T n) T i ρ (n i)))
  have hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    simp [B, fockB_apply, FfL_apply]
  have hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
      (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      LinearIndependent ℚ_[p] f' ∧
      MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg i w a else 0 := by
    intro w
    obtain ⟨hU1, hV1, hU2, hV2, hfac⟩ := hUV i w
    refine smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_
    rw [← hfac]
    ext x y
    simp only [Matrix.of_apply]
    rw [hB, hgam]
  choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔
      MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ :=
    ⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩
  have hnb0 : ∀ w, w ∉ Ω → nb i w = 0 := by
    intro w hw
    by_contra h0
    have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥ := by
      by_contra h; exact hw ((hΩ w).mpr h)
    have hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈
        MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
      rw [← (hf i w).2]; exact Submodule.subset_span ⟨_, rfl⟩
    have h1 := mmwZ_mmw _ _ _ _ _ hmem
    rw [hbot, Submodule.mem_bot] at h1
    exact (hf i w).1.ne_zero _ h1
  have hκ' : (T.pos i + 2) * (r * Nat.log p Xb) ≤ ⌈κ⌉₊ := by
    have hl0 : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : ((T.pos i : ℝ) + 2) ≤ (N : ℝ) + 2 := by
      have : ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
      push_cast at this; linarith
    have h2 : (r : ℝ) * (Nat.log p Xb : ℝ) ≤ (r : ℝ) ^ 2 * lgv :=
      mul_le_mul (by nlinarith) (by linarith) hl0 (by positivity)
    have h3 : (((T.pos i + 2) * (r * Nat.log p Xb) : ℕ) : ℝ) ≤ κ := by
      push_cast
      calc ((T.pos i : ℝ) + 2) * ((r : ℝ) * (Nat.log p Xb : ℝ)) ≤ ((N : ℝ) + 2) * ((r : ℝ) ^ 2 * lgv) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = ((N + 2) * r ^ 2 : ℝ) * lgv := by ring
        _ ≤ κ := hκ
    exact_mod_cast h3.trans (Nat.le_ceil κ)
  have hspZ : ∀ μ v, v ∈ TO.Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr →
      (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) := by
    intro μ v hv hw hvi
    obtain ⟨g, hg, rfl⟩ := hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi
    by_cases hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω
    · have hg' := hf'sp _ hg
      refine Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈
        Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩
      · rw [← FfL_apply, map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [← FfL_apply, map_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [← FfL_apply, LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx
    · have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥ := by
        by_contra h; exact hwΩ ((hΩ _).mpr h)
      have h1 := mmwZ_mmw _ _ _ _ _ hg
      rw [hbot, Submodule.mem_bot] at h1
      rw [h1, ← FfL_apply, map_zero]; exact Submodule.zero_mem _
  have hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 →
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' y.1.1 y.2)) = if x = y then dg i x.1.1 x.2 else 0 := by
    rintro ⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla
    have hww : w = w' := sub_left_injective hla
    subst hww
    have := hf'diag w b b'
    rw [hB] at this
    simp only
    rw [this]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [if_neg hbb, if_neg]
      intro h
      apply hbb
      simpa using h
  have hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1 := by
    intro x y
    rw [fock_Ffull LL T hadm i ρ n]
    have hg := gamma_zero_integral (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) Xb κ hS hni hκ'
      (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))
    rw [← hNN] at hg
    have e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) =
        (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ *
          (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) / NN)) := by
      rw [hcst]; ring
    rw [e, norm_mul]
    exact mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg
  obtain ⟨Tm, πm, h1, h2, h3, h4, h5⟩ := tie_core (LL.setTies T n) T hadm i ρ e1 hK hHP hHW E (by linarith)
    (ι := Σ w : Ω, Fin (nb i w.1))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2))
    (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1)
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)))
    (Ffull_indep LL T hadm i ρ n hS Ω (nb i) f' (fun w a => mmwZ_mmw _ _ _ _ _ (hf'1 w a)) hf'li)
    hspZ
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => Ffull_int LL T hadm i ρ n hS _ (mmwZ_polZ _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => dg i x.1.1 x.2) cst hdiag hG0
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (hfw i x.1.1).1 hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (hfw i x.1.1).1)
    (fun x => Ffull_ne LL T hadm i ρ n x.1.1 _ (hfw i x.1.1).1 ((hfw i x.1.1).2 ((hΩ _).mp x.1.2)) hS)
  refine ⟨Tm, πm, e1 * (T.pos i + 1 + 1) + 2 * e1,
    (by nlinarith [hK, Nat.zero_le e1]), h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩
  have hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)),
      Module.finrank ℚ_[p] (TO.YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
        (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) =
      ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card *
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_filter, TO.YYsp_eq]
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) =
      ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    rw [Finset.mem_coe]
    by_contra hwΩ
    refine hw ?_
    have hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w :=
      (Finset.card_le_univ _).trans (by simp)
    have hle0 := Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)
    simp only [hle0, Nat.cast_zero, zero_mul]
  rw [hfs]
  rw [hsumN] at h5
  exact_mod_cast h5

theorem partnerMX_of_parts (hT : TieOpsX) (hY : YPartnerC) : PartnerMX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ h2p hr hρ hadm hE hS hdeg hL hκ he1 hHP hHW nb f U V dg fw h1 h2 h3
  have hops := hT p N r LL T Xb E κ lgv e1 n ρ h2p hr hρ hadm hE hS hdeg hL hκ hHP hHW nb f U V dg fw h1 h2 h3
  choose Tm πm Kf hK hTY hTint hadj hcomm hrank using hops
  have hadm' : T.Admissible (LL.setTies T n) := hadm
  set LL' := LL.setTies T n with hLL'
  set Ysp : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Y p (r := r) LL' T.J T.thr with hYsp
  set W : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Ysp ⊓ (Finset.univ : Finset (Fin T.t)).inf (fun i => LinearMap.ker (πm i - LinearMap.id)) with hW
  have hYpol : Ysp ≤ Pol p r LL' := inf_le_left
  have hWY : W ≤ Ysp := inf_le_left
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hsat : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 →
      x ∈ YZ p (r := r) LL' T.J T.thr → c • x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' →
      x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' := by
    intro c x hc hx hcx
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hx).2⟩
    have hxY : x ∈ Ysp := (Submodule.mem_inf.mp hx).1
    have hcW : c • x ∈ W := (Submodule.mem_inf.mp hcx).1
    show x ∈ W
    refine Submodule.mem_inf.mpr ⟨hxY, ?_⟩
    rw [Submodule.mem_finsetInf]
    intro i _
    have hci := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp hcW).2) i (Finset.mem_univ i)
    rw [LinearMap.mem_ker] at hci ⊢
    rw [← algebraMap_smul ℚ_[p] c x, map_smul, smul_eq_zero] at hci
    rcases hci with h | h
    · exact absurd (PadicInt.ext (h.trans PadicInt.coe_zero.symm)) hc
    · exact h
  have hL1Y : W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' ≤ YZ p (r := r) LL' T.J T.thr :=
    inf_le_inf_right (PolZ p r LL') (show W.restrictScalars ℤ_[p] ≤ Ysp.restrictScalars ℤ_[p] from fun x hx => hWY hx)
  refine ⟨W.restrictScalars ℤ_[p] ⊓ PolZ p r LL', hL1Y, hsat, ?_, ?_⟩
  ·
    intro u hu hprim
    have huY : u ∈ YZ p (r := r) LL' T.J T.thr := hL1Y hu
    have hprimY : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL' T.J T.thr →
        u = c • x → IsUnit c := by
      intro c x hx hux
      by_cases hc : c = 0
      · exfalso
        have hu0 : u = 0 := by rw [hux, hc, zero_smul]
        have := hprim 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero])
        exact not_isUnit_zero this
      · exact hprim c x (hsat c x hc hx (hux ▸ hu)) hux
    obtain ⟨z'', hz'', hnorm⟩ := hY p N r LL' T.J T.thr ρ e1 hr hHP u huY hprimY
    obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = e1 * (N + 1) := ⟨_, rfl⟩
    rw [← hK₀] at hnorm
    set e := ⌊E⌋₊ with he
    let Ts : Fin T.t → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
      fun i => ((p : ℚ_[p]) ^ (Kf i)) • Tm i
    have hTsZ : ∀ i, ∀ y ∈ YZ p (r := r) LL' T.J T.thr, Ts i y ∈ YZ p (r := r) LL' T.J T.thr := by
      intro i y hy
      have hyY : y ∈ Ysp := (Submodule.mem_inf.mp hy).1
      have h1 : Ts i y ∈ Ysp := Ysp.smul_mem _ (hTY i y hyY)
      exact Submodule.mem_inf.mpr ⟨h1, Submodule.mem_inf.mpr ⟨hYpol h1, hTint i y hy⟩⟩
    have hTsY : ∀ i, ∀ y ∈ (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])), Ts i y ∈ Ysp :=
      fun i y hy => Ysp.smul_mem _ (hTY i y hy)
    set u' := lcomp Ts (List.finRange T.t) z'' with hu'
    have hu'Z : u' ∈ YZ p (r := r) LL' T.J T.thr :=
      lcomp_keep Ts (YZ p (r := r) LL' T.J T.thr : Set _) (List.finRange T.t) (fun j _ => hTsZ j) z'' hz''
    refine ⟨u', hu'Z, ?_⟩
    have hfix : ∀ i ∈ List.finRange T.t, πm i u = u := by
      intro i _
      have huW : u ∈ W := (Submodule.mem_inf.mp hu).1
      have := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp huW).2) i (Finset.mem_univ i)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    have hpeel := peel (fockN p LL') (T.phi p LL') Ts πm (fun i => (p : ℚ_[p]) ^ (Kf i + e))
      (fun i => (Y p (r := r) LL' T.J (T.thrUpTo i) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))
      (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (fun i => fun x hx => y_le_thrUpTo LL' T i hx) hTsY
      (fun i j hij => phi_keeps LL' T hadm' i j hij)
      (fun i j hij => hcomm i j hij)
      (fun i u hu u' hu' => by
        show fockN p LL' (T.phi p LL' i u) (((p : ℚ_[p]) ^ (Kf i)) • Tm i u') = _
        rw [fockN_smul_right', hadj i u hu u' hu', pow_add]; ring)
      (List.finRange T.t) (List.pairwise_lt_finRange T.t) u (hWY (Submodule.mem_inf.mp hu).1) hfix z''
      (Submodule.mem_inf.mp hz'').1
    have hphis : T.phis p (r := r) LL' = lcomp (T.phi p (r := r) LL') (List.finRange T.t) := rfl
    rw [hphis, hpeel]
    have hS' : (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ (T.t : ℝ) * (E + κ) := by
      have hb : ∀ i, ((Kf i + e : ℕ) : ℝ) ≤ E + κ := by
        intro i; push_cast
        have h1 : (Kf i : ℝ) ≤ ((e1 * (N + 2) : ℕ) : ℝ) := by exact_mod_cast hK i
        have h2 : (e : ℝ) ≤ E := Nat.floor_le (by linarith)
        linarith
      calc (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ ∑ _i : Fin T.t, (E + κ) := Finset.sum_le_sum fun i _ => hb i
        _ = (T.t : ℝ) * (E + κ) := by simp; ring
    have hK0' : (K₀ : ℝ) ≤ κ := by
      have h1 : (K₀ : ℝ) ≤ ((e1 * (N + 2) : ℕ) : ℝ) := by
        rw [hK₀]; exact_mod_cast Nat.mul_le_mul_left e1 (by omega)
      linarith
    have hD : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℤ) ≤ ⌊(T.t : ℝ) * (E + κ) + κ⌋ := by
      apply Int.le_floor.mpr
      have : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℝ) = (∑ i, ((Kf i + e : ℕ) : ℝ)) + K₀ := by push_cast; rfl
      rw [Int.cast_natCast, this]
      linarith
    have hprod : ((List.finRange T.t).map (fun i => (p : ℚ_[p]) ^ (Kf i + e))).prod =
        (p : ℚ_[p]) ^ (∑ i, (Kf i + e)) := by
      rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
    rw [hprod, norm_mul, norm_pow, Padic.norm_p]
    calc (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + κ) + κ⌋)
        ≤ (p : ℝ) ^ (-((((∑ i, (Kf i + e)) + K₀ : ℕ)) : ℤ)) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * (p : ℝ) ^ (-(K₀ : ℤ)) := by
        rw [Nat.cast_add, neg_add, zpow_add₀ (ne_of_gt hp0), zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * ‖fockN p LL' u z''‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
  ·
    haveI := pol_finiteDimensional (p := p) (r := r) LL'
    haveI : FiniteDimensional ℚ_[p] Ysp := Submodule.finiteDimensional_of_le hYpol
    have q1 : Module.finrank ℤ_[p] (YZ p (r := r) LL' T.J T.thr) = Module.finrank ℚ_[p] Ysp :=
      finrank_lattice LL' Ysp hYpol
    have q2 : Module.finrank ℤ_[p] (W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' : Submodule ℤ_[p] _) =
        Module.finrank ℚ_[p] W := finrank_lattice LL' W (hWY.trans hYpol)
    rw [q1, q2]
    have hc := codim_inf_le Ysp (fun i => LinearMap.ker (πm i - LinearMap.id)) univ
    refine (Nat.cast_le.mpr hc).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hrank i

theorem pointMX_of_partner (hBad : BadCrit) (hP : PartnerMX) : PointMX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  obtain ⟨L₁, hL₁, hsat, hprim, hrank⟩ :=
    hP p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  have hfin : Module.Finite ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) := by
    haveI : IsNoetherian ℤ_[p] (PolZ p r (LL.setTies T n)) :=
      isNoetherian_of_fg_of_noetherian _ (polZ_fg (LL.setTies T n))
    haveI : IsNoetherian ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) :=
      isNoetherian_of_le (fun x hx => by unfold YZ at hx; exact hx.2)
    infer_instance
  have hb : bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ ≤
      Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ :=
    hBad p (MvPolynomial (Fin N × Fin r) ℚ_[p])
      (fockBil (LL.setTies T n) (T.phis p (LL.setTies T n))) (YZ p (r := r) (LL.setTies T n) T.J T.thr) L₁
      ⌊(T.t : ℝ) * (E + κ) + κ⌋ hfin hL₁ hsat hprim
  exact le_trans (Nat.cast_le.mpr hb) hrank

end Formalism.InvariantFactorPaths.MC
