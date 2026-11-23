import ReciprocityTheory.Chebotarev.CycStatement
import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.NoWind
import ReciprocityTheory.Chebotarev.CycOrth
import ReciprocityTheory.Chebotarev.CycTail
import ReciprocityTheory.Chebotarev.ChebyshevLambdaSubPsiBounded
import ReciprocityTheory.Chebotarev.SummableGfun
import ReciprocityTheory.Chebotarev.PowerSeriesDiagonalLinear

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem cyc_re_psum_upper (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → (Psum E χ s).re ≤ C := by
  by_cases hχ : χ = 1
  · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Lser E χ s‖ < ‖L1‖ + 1 :=
    ((continuous_norm.tendsto L1).comp hL).eventually (gt_mem_nhds (by linarith))
  refine ⟨Real.log (‖L1‖ + 1) + C3, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs1 : 1 < s) _
  have he : Complex.exp (abelian₂ E χ s) = Lser E χ s := h2 E l χ s hs1
  have hre : Real.exp (abelian₂ E χ s).re < ‖L1‖ + 1 := by rw [← Complex.norm_exp, he]; exact hs
  have hlam : (abelian₂ E χ s).re < Real.log (‖L1‖ + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]; exact hre
  have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hs1)
  rw [Complex.sub_re] at hd
  linarith [(abs_le.mp hd).1]

theorem cyc_re_psum_lower (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), -C ≤ (Psum E χ s).re := by
  choose C hC using fun χ' => cyc_re_psum_upper (E := E) h2 h3a hK hirr χ'
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  refine ⟨|C1| + ∑ χ' : DirichletCharacter ℂ l, |C χ'|, ?_⟩
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ', χ' ≠ 1 → (Psum E χ' s).re ≤ C χ' := eventually_all.2 hC
  filter_upwards [hall, hC1, self_mem_nhdsWithin] with s hs hs1 (hgt : 1 < s)
  have hS := h1.2.2 E s hgt
  have ho := psum_orth (E := E) l (1 : (ZMod l)ˣ) s hS
  simp only [inv_one, Units.val_one, map_one, one_mul] at ho
  have hore : ∑ χ' : DirichletCharacter ℂ l, (Psum E χ' s).re = (Nat.totient l : ℝ) * Pcl E l 1 s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this]; simp
  have htot : (Nat.totient l : ℝ) = ((l - 1 : ℕ) : ℝ) := by rw [Nat.totient_prime Fact.out]
  have hP := pcl_nonneg (E := E) l 1 s
  have h1le : (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| := by
    have := re_psum_one_le (E := E) l s hS
    rw [htot]; linarith [le_abs_self C1]
  have hbd : ∀ χ', (Psum E χ' s).re ≤
      |C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0) := by
    intro χ'
    split_ifs with h
    · subst h; linarith [abs_nonneg (C 1)]
    · linarith [hs χ' h, le_abs_self (C χ')]
  have hsplit := Finset.add_sum_erase Finset.univ (fun χ' => (Psum E χ' s).re) (Finset.mem_univ χ)
  have herase : ∑ χ' ∈ Finset.univ.erase χ, (Psum E χ' s).re ≤
      ∑ χ' : DirichletCharacter ℂ l, (|C χ'| + (if χ' = 1 then (Nat.totient l : ℝ) * Pcl E l 1 s + |C1| else 0)) := by
    refine (Finset.sum_le_sum fun χ' _ => hbd χ').trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro χ' _ _
    have := mul_nonneg (Nat.cast_nonneg (Nat.totient l) : (0 : ℝ) ≤ _) hP
    split_ifs
    · linarith [abs_nonneg (C χ'), abs_nonneg C1]
    · simp
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l)] at herase
  simp only [Finset.mem_univ, if_true] at herase
  linarith

end

section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem cyc_psum_bdd (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Psum E χ s‖ ≤ B := by
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C, hC⟩ := cyc_re_psum_lower (E := E) h1 h2 h3a hK hS1 hirr χ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hlow : ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.exp (-(C + C3)) ≤ ‖Lser E χ s‖ := by
    filter_upwards [hC, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
    rw [← h2 E l χ s hgt, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hgt)
    rw [Complex.sub_re] at hd
    linarith [(abs_le.mp hd).1]
  have hL0 : L1 ≠ 0 := by
    have := ge_of_tendsto ((continuous_norm.tendsto L1).comp hL) hlow
    intro h0
    rw [h0, norm_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))
  have hexp : Tendsto (fun s => Complex.exp (abelian₂ E χ s)) (𝓝[>] 1) (𝓝 L1) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact (h2 E l χ s hs).symm
  obtain ⟨B, hB⟩ := bdd_of_exp_tendsto _ (h3c E l χ) L1 hL0 hexp
  refine ⟨B + C3, ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
  have := hC3 s hgt
  calc ‖Psum E χ s‖ = ‖abelian₂ E χ s - (abelian₂ E χ s - Psum E χ s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖abelian₂ E χ s‖ + ‖abelian₂ E χ s - Psum E χ s‖ := norm_sub_le _ _
    _ ≤ B + C3 := by linarith

theorem tendsto_log_one_div_sub_one :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
  have h0 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_sub_right 1).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      simpa using hs
  exact (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0)).congr
    (fun s => by simp only [Function.comp_apply, one_div])

theorem cyc_pcl_large (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (a : (ZMod l)ˣ) (X : ℝ) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), X ≤ Pcl E l (a : ZMod l) s := by
  have hB0 : ∀ χ : DirichletCharacter ℂ l, ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → ‖Psum E χ s‖ ≤ B := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
    · obtain ⟨B, hB⟩ := cyc_psum_bdd (E := E) h1 h2 h3a h3c hK hS1 hirr χ hχ
      exact ⟨B, hB.mono fun _ h _ => h⟩
  choose B hB using hB0
  obtain ⟨C1, hC1⟩ := hS1 E l hirr
  obtain ⟨HighestWeightIntegral, hC3b⟩ := h3b E
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ, χ ≠ 1 → ‖Psum E χ s‖ ≤ B χ := eventually_all.2 hB
  set k : ℝ := ((l - 1 : ℕ) : ℝ) with hk
  set S : ℝ := ∑ χ : DirichletCharacter ℂ l, |B χ| with hSdef
  have hkpos : 0 < k := by
    have := (Fact.out : l.Prime).two_le
    rw [hk]; exact_mod_cast (by omega : 0 < l - 1)
  have hbig := tendsto_log_one_div_sub_one.eventually (eventually_ge_atTop (k * (k * X + S) + HighestWeightIntegral + C1))
  filter_upwards [hall, hC1, hbig, Ioc_mem_nhdsGT one_lt_two] with s hs hs1 hlog hsI
  have hgt : 1 < s := hsI.1
  have hS := h1.2.2 E s hgt
  have htot : (Nat.totient l : ℝ) = k := by rw [hk, Nat.totient_prime Fact.out]
  have ho := psum_orth (E := E) l a s hS
  have hore : ∑ χ : DirichletCharacter ℂ l, (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re
      = k * Pcl E l (a : ZMod l) s := by
    have := congrArg Complex.re ho
    rw [Complex.re_sum] at this
    rw [this, ← htot]; simp
  have hterm : ∀ χ : DirichletCharacter ℂ l,
      (if χ = 1 then (Psum E (1 : DirichletCharacter ℂ l) s).re else 0) - |B χ|
        ≤ (χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s).re := by
    intro χ
    split_ifs with h
    · subst h
      rw [MulChar.one_apply_coe, one_mul]
      linarith [abs_nonneg (B 1)]
    · have h3 : ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s‖ ≤ B χ := by
        rw [norm_mul]
        calc ‖χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l)‖ * ‖Psum E χ s‖ ≤ 1 * ‖Psum E χ s‖ :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          _ ≤ B χ := by rw [one_mul]; exact hs χ h
      have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h3)).1
      linarith [le_abs_self (B χ)]
  have hsum := Finset.sum_le_sum fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ l))) => hterm χ
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ l), hore] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hp1 := pcl_one_le_re_psum_one (E := E) l s hS
  have hpe : Real.log (1 / (s - 1)) - HighestWeightIntegral ≤ PE E s := by
    have := hC3b s hsI
    linarith [(abs_le.mp this).1]

  have hk1 : k * (k * X + S) ≤ k * Pcl E l 1 s := by linarith
  have hk2 : k * X + S ≤ Pcl E l 1 s := le_of_mul_le_mul_left hk1 hkpos
  have hk3 : k * X ≤ k * Pcl E l (a : ZMod l) s := by linarith
  exact le_of_mul_le_mul_left hk3 hkpos

theorem cyc_of (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1) :
    CycStatement := by
  intro E _ _ l _ hirr a T
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hbad : ∀ q : Prm E, (Nrm q).Prime → Nrm q ∉ T → ((Nrm q : ℕ) : ZMod l) ≠ a :=
    fun q hp hT => hno q.asIdeal q.isPrime hp hT
  let g : Prm E → ℝ := fun q => (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) +
    Set.indicator {q | Nrm q ∈ T} (fun _ => (1 : ℝ)) q
  have hg : Summable g :=
    summable_nonprime_norm.add (summable_of_hasFiniteSupport ((finite_norm_mem T).subset Set.support_indicator_subset))
  have hle : ∀ s : ℝ, 1 < s → Pcl E l (a : ZMod l) s ≤ ∑' q, g q := by
    intro s hs
    have hS := h1.2.2 E s hs
    have hterm : ∀ q : Prm E, (if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) ≤ g q := by
      intro q
      have h2q := two_le_nrm q
      have hN1 : (1 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nrm q)
      have hpow1 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hpow2 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have hind0 : 0 ≤ Set.indicator {q : Prm E | Nrm q ∈ T} (fun _ => (1 : ℝ)) q :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) q
      have hinv0 : 0 ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by positivity
      simp only [g]
      by_cases hc : ((Nrm q : ℕ) : ZMod l) = a
      · rw [if_pos hc]
        by_cases hp : (Nrm q).Prime
        · have hT : Nrm q ∈ T := by
            by_contra hT; exact hbad q hp hT hc
          rw [if_pos hp, Set.indicator_of_mem (show q ∈ {q : Prm E | Nrm q ∈ T} from hT)]
          linarith
        · rw [if_neg hp]; linarith
      · rw [if_neg hc]
        split_ifs <;> linarith
    have hP : Summable (fun q : Prm E =>
        if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
      refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
      · split_ifs
        · positivity
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · positivity
    exact Summable.tsum_le_tsum hterm hP hg
  obtain ⟨s, hs, hs1⟩ := ((cyc_pcl_large (E := E) h1 h2 h3a h3b h3c hK hS1 hirr a (∑' q, g q + 1)).and
    self_mem_nhdsWithin).exists
  linarith [hle s hs1]

end

theorem cyc_holds : CycStatement :=
  cyc_of affine_proper_base_change proper_base_change casimirPower_surjective_symmetric chebyshev_log_bounded smoothMap_seminorm_bound k_holds power_series_diagonal_linear

end ReciprocityTheory.Cheb
