import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserIdeleMultiplicativeOnIdealsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralResidueSystemFiniteAdelesModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitCongruenceSubgroupRelIndexNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

variable {E : Type} [Field E] [NumberField E] {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {χ : HChar E}

theorem indicator_box_mul {H : Subgroup (Af E)ˣ} (hH : H ≤ congr r) (hχ : ∀ u ∈ H, finPart χ u = 1) (s : ℂ) (g : (Af E)ˣ)
    (u : (Af E)ˣ) (hu : u ∈ H) : (box r).indicator (zterm χ s) (g * u) = (box r).indicator (zterm χ s) g := by
  classical
  simp only [Set.indicator_apply, mul_mem_box (hH hu), zterm_mul, zterm_unit χ s fun w => (hH hu w).1, hχ u hu]
  simp

theorem one_sub_ne_zero {x : ℂ} (hx : ‖x‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (v : HeightOneSpectrum (𝓞 E)) :
    1 - x * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h2 : ‖x * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ = 1 := by
    rw [← sub_eq_zero.1 h, norm_one]
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)] at h2
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s).re < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by simp only [Complex.neg_re]; linarith)
  have h4 := mul_le_of_le_one_left
    (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (Ideal.absNorm v.asIdeal)) (-s).re) hx
  linarith

open Classical in

theorem box_euler (hu : IsUnitary χ) (hr : ∀ w, r w ≤ 1) (hχ : ∀ u ∈ congr r, finPart χ u = 1) {s : ℂ} (hs : 1 < s.re) :
    ∃ Z, QSum (congr r) ((box r).indicator (zterm χ s)) Z ∧
      HasProd (fun w => if r w = 1 then (1 - (val χ w : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ else 1) Z := by
  obtain ⟨t, t1, tmul, tv, tmod, tco, tinj, tsurj⟩ := GlobalTheory.T.exists_uniformiserIdele_multiplicative_on_ideals E
  let C : Ideal (𝓞 E) → Prop := fun I => I ≠ ⊥ ∧ ∀ w, r w ≠ 1 → ¬ w.asIdeal ∣ I
  let X : Ideal (𝓞 E) → ℂ := fun I => if C I then (finPart χ (t I) : ℂ) else 0
  have hX : ∀ I, ‖X I‖ ≤ 1 := fun I => by
    simp only [X]
    split_ifs
    · exact (hu _).le
    · simp
  have hC : ∀ I J, C (I * J) ↔ C I ∧ C J := fun I J => by
    simp only [C, Ne, Ideal.mul_eq_bot, not_or, fun w : HeightOneSpectrum (𝓞 E) => w.prime.dvd_mul (a := I) (b := J)]
    exact ⟨fun h => ⟨⟨h.1.1, fun w hw => (h.2 w hw).1⟩, h.1.2, fun w hw => (h.2 w hw).2⟩,
      fun h => ⟨⟨h.1.1, h.2.1⟩, fun w hw => ⟨h.1.2 w hw, h.2.2 w hw⟩⟩⟩
  have hE := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X (by simp [X, C])
    (by
      have : C ⊤ := ⟨top_ne_bot, fun w _ h => w.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))⟩
      simp [X, this, t1])
    (fun I J => by
      simp only [X, hC]
      by_cases hI : C I
      · by_cases hJ : C J
        · simp [hI, hJ, tmul I J hI.1 hJ.1]
        · simp [hJ]
      · simp [hI]) hX s hs
  have hS : Summable fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded (GlobalTheory.Mem.summable_norm_absNorm_cpow E hs) fun I => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hX I)
  refine ⟨∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
  · have h1 : HasSum ((fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘ ((↑) : {I | C I} → _)) _ :=
      (hasSum_subtype_iff_of_support_subset (fun I hI => by
        by_contra h
        exact hI (by simp only [X]; rw [if_neg (show ¬ C I from h), zero_mul]))).2 hS.hasSum
    let f : {I | C I} → (Af E)ˣ ⧸ congr r := fun I => QuotientGroup.mk (t I)
    have hf : Function.Injective f := fun I J h => by
      refine Subtype.ext (tinj _ _ I.2.1 J.2.1 fun w => ?_)
      have h2 := QuotientGroup.eq.1 h
      have e : t J = t I * ((t I)⁻¹ * t J) := by simp
      rw [e]
      show _ = Valued.v ((t I : Af E) w * (((t I)⁻¹ * t J : (Af E)ˣ) : Af E) w)
      rw [map_mul, (h2 w).1, mul_one]
    unfold QSum
    rw [← hf.hasSum_iff]
    · refine h1.congr_fun fun I => ?_
      have hb : t I ∈ box r := fun w => by
        by_cases hw : r w = 1
        · rw [hw]; exact Valuation.map_sub_le _ (tco I I.2.1 w).1 (by simp)
        · rw [(tco I I.2.1 w).2.2 (I.2.2 w hw)]; simp
      show (box r).indicator (zterm χ s) (QuotientGroup.mk (t I) : _ ⧸ congr r).out = X I * _
      rw [out_mk (indicator_box_mul le_rfl hχ s), Set.indicator_of_mem hb, zterm, tmod I I.2.1]
      simp only [X]
      rw [if_pos (show C I from I.2), Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ (by
        rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]
    · intro q hq
      refine Set.indicator_of_notMem (fun hb => hq ?_) _
      have hz : ∀ w, Valued.v ((q.out : Af E) w) ≤ 1 := fun w => by
        have := Valuation.map_add_le Valued.v ((hb w).trans (hr w)) (le_of_eq (map_one _))
        rwa [sub_add_cancel] at this
      obtain ⟨I, hI, hv⟩ := tsurj _ hz
      have hCI : C I := ⟨hI, fun w hw hd => by
        have h3 := Valuation.map_one_add_of_lt Valued.v ((hb w).trans_lt (lt_of_le_of_ne (hr w) hw))
        rw [add_sub_cancel, ← hv] at h3
        exact ((tco I hI w).2.1 hd).ne h3⟩
      refine ⟨⟨I, hCI⟩, ?_⟩
      rw [← q.out_eq]
      refine QuotientGroup.eq.2 fun w => ?_
      have e : (t I : Af E) w * (((t I)⁻¹ * q.out : (Af E)ˣ) : Af E) w = (q.out : Af E) w := by
        show ((t I * ((t I)⁻¹ * q.out) : (Af E)ˣ) : Af E) w = _
        rw [mul_inv_cancel_left]
      have e1 : Valued.v ((((t I)⁻¹ * q.out : (Af E)ˣ) : Af E) w) = 1 := by
        have := congrArg Valued.v e
        rw [map_mul, hv] at this
        exact mul_left_cancel₀ (ObjModel.coord_ne _ w) (this.trans (mul_one _).symm)
      refine ⟨e1, ?_⟩
      by_cases hw : r w = 1
      · rw [hw]; exact Valuation.map_sub_le _ e1.le (by simp)
      · rw [(tco I hI w).2.2 (hCI.2 w hw), one_mul] at e
        exact e ▸ hb w
  · rw [hE]
    have hl : Summable fun P : HeightOneSpectrum (𝓞 E) =>
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) :=
      (Summable.clog_one_sub (hS.comp_injective fun _ _ h => HeightOneSpectrum.ext h)).neg
    refine hl.hasSum.cexp.congr_fun fun w => ?_
    rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (one_sub_ne_zero (hX _) hs w)]
    by_cases hw : r w = 1
    · have : C w.asIdeal := ⟨w.ne_bot, fun w' hw' h => hw' (by
        rw [HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top (Ideal.le_of_dvd h)).symm, hw])⟩
      simp only [X]
      rw [if_pos hw, if_pos this, tv, finPart_unifAt]
    · simp only [X]
      rw [if_neg hw, if_neg fun h => h.2 w hw dvd_rfl]
      simp

theorem box_entire (hu : IsUnitary χ) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) (hr : ∀ w, r w ≤ 1) (hfin : {w | r w ≠ 1}.Finite)
    {U : Subgroup (Af E)ˣ} (hU : U ≤ congr r) (hn : U.relIndex (congr r) ≠ 0) (hχ : ∀ u ∈ U, finPart χ u = 1) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → QSum U ((box r).indicator (zterm χ s)) (Z s) := by
  classical
  by_cases h : ∀ u ∈ congr r, finPart χ u = 1
  · refine ⟨fun s => U.relIndex (congr r) * (Λ s * ∏ w ∈ hfin.toFinset, (eulerFactor χ s w)⁻¹), ?_, fun s hs => ?_⟩
    · refine Differentiable.const_mul (hΛ.1.mul (Differentiable.fun_finset_prod fun w _ => ?_)) _
      unfold eulerFactor
      by_cases hw : χ.UnrAt w
      · simp only [if_pos hw, inv_inv]
        refine Differentiable.const_sub (Differentiable.const_mul (Differentiable.const_cpow differentiable_neg
          (Or.inl ?_)) _) _
        exact_mod_cast (ObjModel.absNorm_pos w).ne'
      · simp [hw]
    · rw [← qsum_index hU hn (indicator_box_mul le_rfl h s)]
      obtain ⟨Z, hZ, hP⟩ := box_euler hu hr h hs
      have h1 : HasProd (fun w => if w ∈ hfin.toFinset then eulerFactor χ s w else 1)
          (∏ w ∈ hfin.toFinset, eulerFactor χ s w) := by
        have := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := hfin.toFinset)
          (f := fun w => if w ∈ hfin.toFinset then eulerFactor χ s w else 1) fun w hw => if_neg hw
        rwa [Finset.prod_congr rfl fun w hw => if_pos hw] at this
      have h2 : Λ s = Z * ∏ w ∈ hfin.toFinset, eulerFactor χ s w := by
        refine (hΛ.2 s hs).unique ((hP.mul h1).congr_fun fun w => ?_)
        by_cases hw : r w = 1
        · have : χ.UnrAt w := fun x hx => h (single w x) fun w' => by
            by_cases e : w' = w
            · subst e
              rw [single_self, hw]
              exact ⟨hx, Valuation.map_sub_le _ (le_of_eq hx) (by simp)⟩
            · rw [suppAt_single w x w' e]; simp
          simp [hw, eulerFactor, this]
        · simp [hw]
      have h3 : ∏ w ∈ hfin.toFinset, eulerFactor χ s w ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => by
        unfold eulerFactor
        split_ifs
        · exact inv_ne_zero (one_sub_ne_zero (le_of_eq (hu _)) hs w)
        · exact one_ne_zero
      rwa [Finset.prod_inv_distrib, h2, mul_inv_cancel_right₀ h3]
  · refine ⟨fun _ => 0, differentiable_const _, fun s hs => ?_⟩
    push Not at h
    obtain ⟨u, hu', hne⟩ := h
    have h1u : IsUnitary (1 : HChar E) := fun _ => norm_one
    obtain ⟨Z, hZ, -⟩ := box_euler h1u hr (fun _ _ => rfl) hs
    rw [qsum_index hU hn (indicator_box_mul le_rfl (fun _ _ => rfl) s)] at hZ
    have h2 : Summable fun q : (Af E)ˣ ⧸ U => (box r).indicator (zterm χ s) q.out := by
      refine Summable.of_norm_bounded hZ.summable.norm fun q => le_of_eq ?_
      simp only [Set.indicator_apply]
      split_ifs
      · rw [norm_zterm hu, norm_zterm h1u]
      · rfl
    have h3 : QSum U ((box r).indicator (zterm χ s)) _ := h2.hasSum
    have h4 := h3.eq_zero (indicator_box_mul hU hχ s) (t := u) (c := finPart χ u) (fun e => hne (Units.ext e)) fun g => by
      rw [mul_comm u g]
      simp only [Set.indicator_apply, mul_mem_box hu', zterm_mul, zterm_unit χ s fun w => (hu' w).1]
      split_ifs
      · exact mul_comm _ _
      · simp
    rwa [h4] at h3

theorem exists_box {N : ℕ} (hN : 0 < N) {a : Af E} (ha : ∀ w, Valued.v (a w) ≤ 1) :
    ∃ (t : (Af E)ˣ) (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)), (∀ w, r w ≤ 1) ∧ (∀ w, radN E N w ≤ r w) ∧
      {w | r w ≠ 1}.Finite ∧ ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w - a w) ≤ radN E N w) ↔ t⁻¹ * z ∈ box r := by
  classical
  have hN1 : ∀ w, radN E N w ≤ 1 := fun w => GlobalTheory.AdLat.valued_natCast_le_one w N
  have hN0 : ∀ w, radN E N w ≠ 0 := fun w => GlobalTheory.AdLat.valued_natCast_ne_zero w hN
  have hNf : {w | radN E N w ≠ 1}.Finite := GlobalTheory.Mem.TupHecke.finite_nat hN
  let T : Af E := ⟨fun w => if radN E N w < Valued.v (a w) then a w else (N : w.adicCompletion E),
    Filter.Eventually.of_forall fun w => by
      refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      beta_reduce
      split_ifs
      exacts [ha w, hN1 w]⟩
  have hT : ∀ w, T w = if radN E N w < Valued.v (a w) then a w else (N : w.adicCompletion E) := fun _ => rfl
  have hT0 : ∀ w, Valued.v (T w) ≠ 0 := fun w => by
    rw [hT]
    split_ifs with h
    exacts [(zero_le.trans_lt h).ne', hN0 w]
  have hTu : IsUnit T := FiniteAdeleRing.isUnit_iff.2 ⟨fun w h => hT0 w (by rw [h, map_zero]), by
    rw [Filter.eventually_cofinite]
    refine hNf.subset fun w hw h => hw ?_
    rw [hT, if_neg (by rw [h]; exact not_lt.2 (ha w))]
    exact h⟩
  obtain ⟨t, ht⟩ := hTu
  refine ⟨t, fun w => radN E N w / Valued.v (T w), fun w => ?_, fun w => ?_, hNf.subset fun w hw h => hw ?_,
    fun z => forall_congr' fun w => ?_⟩
  · rw [div_le_one₀ (zero_lt_iff.2 (hT0 w)), hT]
    split_ifs with h
    exacts [h.le, le_rfl]
  · rw [le_div_iff₀ (zero_lt_iff.2 (hT0 w))]
    refine mul_le_of_le_one_right' ?_
    rw [hT]
    split_ifs
    exacts [ha w, hN1 w]
  · beta_reduce
    rw [hT, if_neg (by rw [h]; exact not_lt.2 (ha w))]
    exact div_self (hN0 w)
  · have e : T w * ((t⁻¹ * z : (Af E)ˣ) : Af E) w = (z : Af E) w := by
      rw [← ht]
      show ((t * (t⁻¹ * z) : (Af E)ˣ) : Af E) w = _
      rw [mul_inv_cancel_left]
    rw [le_div_iff₀ (zero_lt_iff.2 (hT0 w)), ← map_mul, sub_mul, one_mul, mul_comm, e, hT]
    split_ifs with h
    · rfl
    · have h1 : Valued.v (a w - (N : w.adicCompletion E)) ≤ radN E N w := Valuation.map_sub_le _ (not_lt.1 h) le_rfl
      constructor
      · intro h2
        simpa using Valuation.map_add_le _ h2 h1
      · intro h2
        simpa using Valuation.map_sub_le _ h2 h1

open Classical in

theorem class_entire (hu : IsUnitary χ) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {N : ℕ} (hN : 0 < N)
    (hχ : ∀ u ∈ congr (radN E N), finPart χ u = 1) {a : Af E} (ha : ∀ w, Valued.v (a w) ≤ 1) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → QSum (congr (radN E N))
      (fun z => if ∀ w, Valued.v ((z : Af E) w - a w) ≤ radN E N w then zterm χ s z else 0) (Z s) := by
  obtain ⟨t, r, hr, hr', hfin, ht⟩ := exists_box hN ha
  obtain ⟨Z, hZ, h⟩ := box_entire hu hΛ hr hfin (congr_mono hr')
    (mt (Subgroup.relIndex_eq_zero_of_le_right (congr_mono hr)) (GlobalTheory.T.integralUnitCongruenceSubgroup_relIndex_ne_zero E N hN)) hχ
  refine ⟨fun s => zterm χ s t * Z s, (differentiable_zterm χ t).mul hZ, fun s hs => ?_⟩
  refine (((h s hs).translate (indicator_box_mul (congr_mono hr') hχ s) t⁻¹).mul_left (zterm χ s t)).congr_fun fun q => ?_
  simp only [Set.indicator_apply, ht]
  split_ifs
  · rw [← zterm_mul, mul_inv_cancel_left]
  · simp

theorem indicator_hatO_mul {c : Ideal (OF E)} (hχ : ∀ u ∈ hatOUnits c, finPart χ u = 1) (s : ℂ) (g : (Af E)ˣ)
    (u : (Af E)ˣ) (hu : u ∈ hatOUnits c) :
    {z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm χ s) (g * u) =
      {z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm χ s) g := by
  classical
  have : ((g * u : (Af E)ˣ) : Af E) ∈ hatO c ↔ (g : Af E) ∈ hatO c :=
    ⟨fun h => by simpa using mul_mem h hu.2, fun h => mul_mem h hu.1⟩
  simp only [Set.indicator_apply, Set.mem_setOf_eq, this, zterm_mul,
    zterm_unit χ s fun w => (hatOUnits_le_congr c hu w).1, hχ u hu]
  simp

theorem order_entire (hu : IsUnitary χ) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    (hχ : ∀ u ∈ hatOUnits c, finPart χ u = 1) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re →
      QSum (hatOUnits c) ({z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm χ s)) (Z s) := by
  classical
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hNc := Ideal.absNorm_mem c
  generalize Ideal.absNorm c = N at hN hNc
  have hle := congr_le_hatOUnits hN hNc
  have hn : (congr (radN E N)).relIndex (hatOUnits c) ≠ 0 :=
    mt (Subgroup.relIndex_eq_zero_of_le_right (hatOUnits_le_congr c)) (GlobalTheory.T.integralUnitCongruenceSubgroup_relIndex_ne_zero E N hN)
  have hn' : (((congr (radN E N)).relIndex (hatOUnits c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  obtain ⟨R, hR, hR'⟩ := GlobalTheory.T.exists_integral_residue_system_finiteAdeles_mod E N hN
  choose! Z hZ h using fun (a : Af E) (ha : ∀ w, Valued.v (a w) ≤ 1) =>
    class_entire hu hΛ hN (fun u hu => hχ u (hle hu)) ha
  refine ⟨fun s => (((congr (radN E N)).relIndex (hatOUnits c) : ℕ) : ℂ)⁻¹ * ∑ a ∈ R.filter (· ∈ hatO c), Z a s,
    Differentiable.const_mul (Differentiable.fun_sum fun a ha => hZ a (hR a (Finset.mem_filter.1 ha).1)) _, fun s hs => ?_⟩
  rw [qsum_index hle hn (indicator_hatO_mul hχ s), mul_inv_cancel_left₀ hn']
  refine (hasSum_sum fun a ha => h a (hR a (Finset.mem_filter.1 ha).1) s hs).congr_fun fun q => ?_
  by_cases hq : ((q.out : (Af E)ˣ) : Af E) ∈ hatO c
  · obtain ⟨a, ⟨ha, ha'⟩, hun⟩ := hR' _ (ObjModel.hatO_integral hq)
    have hao : a ∈ hatO c := mem_hatO_of_sub hN hNc hq fun w => by rw [Valuation.map_sub_swap]; exact ha' w
    rw [Set.indicator_of_mem (s := {z : (Af E)ˣ | (z : Af E) ∈ hatO c}) hq, Finset.sum_eq_single_of_mem a (Finset.mem_filter.2 ⟨ha, hao⟩)
      fun b hb hne => if_neg fun h => hne (hun b ⟨(Finset.mem_filter.1 hb).1, h⟩), if_pos ha']
  · rw [Set.indicator_of_notMem (s := {z : (Af E)ˣ | (z : Af E) ∈ hatO c}) hq, Finset.sum_eq_zero fun b hb => if_neg fun h =>
      hq (mem_hatO_of_sub hN hNc (Finset.mem_filter.1 hb).2 h)]

theorem exists_hchar {c : Ideal (OF E)} (hc : c ≠ ⊥) [Finite (PicO c)] (θ : PicO c →* ℂˣ) :
    ∃ η : HChar E, IsUnitary η ∧ (∀ k, η.inf k = 1) ∧ ∀ z, finPart η z = θ (QuotientGroup.mk z) := by
  have hn : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hk : ∀ u, GlobalTheory.Mem.TupHecke.Cong (Ideal.absNorm c) u → θ.comp (QuotientGroup.mk' _) u = 1 := fun u hu => by
    show θ (QuotientGroup.mk u) = 1
    rw [(QuotientGroup.eq_one_iff u).2 (Subgroup.mem_sup_right (congr_le_hatOUnits hn (Ideal.absNorm_mem c) hu)), map_one]
  refine ⟨⟨(θ.comp (QuotientGroup.mk' _)).comp (GlobalTheory.Mem.TupHecke.finP E), GlobalTheory.Mem.TupHecke.continuous_finP hn _ hk,
    fun k => ?_⟩, fun x => ?_, fun k => ?_, fun z => rfl⟩
  · show θ (QuotientGroup.mk (Units.map (algebraMap E (Af E)).toMonoidHom k)) = 1
    rw [(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (show _ ∈ princ from ⟨k, rfl⟩)), map_one]
  · refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (PicO c)) ?_ Nat.card_pos.ne'
    show ((θ _ : ℂˣ) : ℂ) ^ _ = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · show θ (QuotientGroup.mk' _ (GlobalTheory.Mem.TupHecke.finP E (infDiag k))) = 1
    rw [infDiag_eq]
    show θ (QuotientGroup.mk' _ 1) = 1
    rw [map_one, map_one]

open Classical in

theorem sum_char {G : Type} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] (g : G) :
    ∑ θ : G →* ℂˣ, (θ g : ℂ) = if g = 1 then (Fintype.card (G →* ℂˣ) : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · obtain ⟨θ, hθ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ h
    refine sum_hom_units_eq_zero ((Units.coeHom ℂ).comp (MonoidHom.eval g)) fun e => hθ (Units.ext ?_)
    exact DFunLike.congr_fun e θ

theorem zterm_princ [IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (h : IsCMType φ) {s : ℕ} {κ : I → ℕ}
    (hi : HasInf χ φ fun i => (κ i : ℤ) + s) (σ : ℂ) (a : Eˣ) :
    zterm χ (s + σ) (Units.map (algebraMap E (Af E)).toMonoidHom a) = term φ (2 * s) κ σ a := by
  have h2 := term_mul_inf hi a
  have h3 : ((finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom a) : ℂˣ) : ℂ) * ((χ.inf a : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  have h4 : ∏ i, (φ i a * starRingEnd ℂ (φ i a)) ^ s = ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ s : ℝ) : ℂ) := by
    rw [← ObjModel.prod_normSq h, Finset.prod_pow]
    simp [Complex.mul_conj']
  have h5 : term φ (2 * s) κ σ a = term φ (2 * s) κ 0 a * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
    rw [← ObjModel.prod_normSq h, ← ObjModel.prod_cpow _ _ fun i => sq_nonneg _]
    unfold term
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _), ← sq,
      ← Complex.cpow_nat_mul]
    simp
  have h6 : (|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)|) ≠ 0 := by simp [Algebra.norm_eq_zero_iff]
  rw [h4] at h2
  rw [h5, zterm, ObjModel.modF_princ, eq_inv_of_mul_eq_one_left h3, eq_inv_of_mul_eq_one_left h2, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (abs_nonneg _)]; exact Real.pi_ne_zero.symm),
    Complex.cpow_add _ _ (by exact_mod_cast h6), Complex.cpow_natCast, Complex.cpow_neg, Complex.ofReal_pow]
  simp only [mul_inv, mul_assoc]

theorem exists_isLatSum : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 c : Ideal (OF E)) (χ : HChar E), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ → IsUnitary χ → HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  classical
  intro hL E _ _ _ I _ φ hφ s κ 𝔣 c χ _ hs h𝔣 hd hc hu hi hχ y
  have := PicFin.finite_picO E c hc
  have := Fintype.ofFinite (PicO c →* ℂˣ)
  obtain ⟨i₀, -⟩ := hφ (Classical.arbitrary _)
  have hcard : (Fintype.card (PicO c →* ℂˣ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  choose η hηu hηi hηf using fun θ : PicO c →* ℂˣ => exists_hchar hc θ
  have hex : ∀ θ, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re →
      QSum (hatOUnits c) ({z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm (χ * η θ) s)) (Z s) := fun θ => by
    have h1 : IsUnitary (χ * η θ) := fun x => by
      show ‖((χ.1 x * (η θ).1 x : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, norm_mul, hu x, hηu θ x, one_mul]
    obtain ⟨Λ, hΛ⟩ := hL E I φ _ (χ * η θ) hφ h1 (fun k => by
      rw [Formalism.L2.Host.HChar.inf_mul, hηi, mul_one]; exact hi k) ⟨i₀, by omega⟩
    refine order_entire h1 hΛ hc fun u hu => ?_
    rw [finPart_mul, hχ u hu, hηf, (QuotientGroup.eq_one_iff u).2 (Subgroup.mem_sup_right hu), map_one, one_mul]
  choose Z hZ hZs using hex
  refine ⟨fun σ => zterm χ (s + σ) y * ((Fintype.card (PicO c →* ℂˣ) : ℂ)⁻¹ *
    ∑ θ : PicO c →* ℂˣ, (θ (QuotientGroup.mk y) : ℂ) * Z θ (s + σ)), ?_, fun σ hσ => ?_⟩
  · have h0 : Differentiable ℂ fun σ : ℂ => (s : ℂ) + σ := by fun_prop
    exact ((differentiable_zterm χ y).comp h0).mul (Differentiable.const_mul
      (Differentiable.fun_sum fun θ _ => ((hZ θ).comp h0).const_mul _) _)
  have hσ' : 1 < ((s : ℂ) + σ).re := by simpa using hσ
  let F : (Af E)ˣ → ℂ := fun z => if (QuotientGroup.mk (y * z) : PicO c) = 1 then
    {z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm χ (s + σ)) z else 0
  have hF : ∀ g, ∀ u ∈ hatOUnits c, F (g * u) = F g := fun g u hu => by
    simp only [F]
    rw [indicator_hatO_mul hχ _ g u hu, ← mul_assoc, QuotientGroup.mk_mul _ (y * g) u,
      (QuotientGroup.eq_one_iff u).2 (Subgroup.mem_sup_right hu), mul_one]
  have h1 : HasSum (fun q : (Af E)ˣ ⧸ hatOUnits c => F q.out) ((Fintype.card (PicO c →* ℂˣ) : ℂ)⁻¹ *
      ∑ θ : PicO c →* ℂˣ, (θ (QuotientGroup.mk y) : ℂ) * Z θ (s + σ)) := by
    refine ((hasSum_sum fun θ _ => (hZs θ _ hσ').mul_left (θ (QuotientGroup.mk y) : ℂ)).mul_left _).congr_fun fun q => ?_
    have e : ∀ θ : PicO c →* ℂˣ, (θ (QuotientGroup.mk y) : ℂ) *
        {z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm (χ * η θ) (s + σ)) q.out =
        (θ (QuotientGroup.mk (y * q.out)) : ℂ) *
          {z : (Af E)ˣ | (z : Af E) ∈ hatO c}.indicator (zterm χ (s + σ)) q.out := fun θ => by
      simp only [Set.indicator_apply]
      split_ifs
      · rw [zterm, zterm, finPart_mul, hηf, QuotientGroup.mk_mul, map_mul, Units.val_mul, Units.val_mul]
        ring
      · simp
    simp only [e, F]
    rw [← Finset.sum_mul, sum_char]
    split_ifs
    · rw [inv_mul_cancel_left₀ hcard]
    · simp
  let P : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom
  let A : modUnits (lattice c y) → Eˣ := fun q => Units.mk0 q.1.out (out_mem_lattice q).2
  let f : modUnits (lattice c y) → (Af E)ˣ ⧸ hatOUnits c := fun q => QuotientGroup.mk (P (A q) * y⁻¹)
  have hO : ∀ a : Eˣ, ((P a : (Af E)ˣ) : Af E) ∈ hatO c → (a : E) ∈ orderC c := fun a ha => by
    rw [← SetLike.mem_coe, ← GlobalTheory.T.idelicRingClassLattice_one_eq_order E c hc, mem_lattice, inv_one, Units.val_one, mul_one]
    exact ha
  have hf : Function.Injective f := fun q q' h => by
    have h2 := QuotientGroup.eq.1 h
    rw [show (P (A q) * y⁻¹)⁻¹ * (P (A q') * y⁻¹) = P (A q' * (A q)⁻¹) by
      rw [map_mul, map_inv]; simp [mul_comm, mul_left_comm, mul_assoc]] at h2
    obtain ⟨u, hu⟩ := GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hd _ (A q' * (A q)⁻¹).ne_zero (hO _ h2.1) (by
      rw [← Units.val_inv_eq_inv_val]
      exact hO _ (by rw [map_inv]; exact h2.2))
    refine Subtype.ext ?_
    rw [← q.1.out_eq, ← q'.1.out_eq]
    refine Quotient.sound ⟨u, ?_⟩
    rw [← hu]
    show ((A q' : Eˣ) : E) = _ * ((A q : Eˣ) : E)
    rw [← Units.val_mul, inv_mul_cancel_right]
  rw [← hf.hasSum_iff] at h1
  · refine (h1.mul_left (zterm χ (s + σ) y)).congr_fun fun q => ?_
    show _ = _ * F (QuotientGroup.mk (P (A q) * y⁻¹) : _ ⧸ hatOUnits c).out
    rw [out_mk hF]
    simp only [F]
    rw [if_pos, Set.indicator_of_mem (s := {z : (Af E)ˣ | (z : Af E) ∈ hatO c}) (out_mem_lattice q).1, ← zterm_mul,
      mul_comm (P (A q)) y⁻¹, mul_inv_cancel_left]
    · exact (zterm_princ hφ hi σ (A q)).symm
    · rw [mul_comm, inv_mul_cancel_right]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left ⟨_, rfl⟩)
  · intro q hq
    by_contra hne
    have h2 : (QuotientGroup.mk (y * q.out) : PicO c) = 1 := by
      by_contra h; exact hne (if_neg h)
    have h3 : ((q.out : (Af E)ˣ) : Af E) ∈ hatO c := by
      by_contra h
      exact hne ((if_pos h2).trans (Set.indicator_of_notMem (s := {z : (Af E)ˣ | (z : Af E) ∈ hatO c}) h _))
    obtain ⟨_, ⟨a, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 ((QuotientGroup.eq_one_iff _).1 h2)
    have h4 : P a * y⁻¹ = q.out * u⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_right_comm, hau, mul_inv_cancel_comm]
    have h5 : (a : E) ∈ lattice c y := by
      show ((P a * y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
      rw [h4]
      exact mul_mem h3 hu.2
    let q' : modUnits (lattice c y) := ⟨Quotient.mk _ (a : E), a, h5, a.ne_zero, rfl⟩
    obtain ⟨v, hv⟩ : (unitRel (E := E)).r a q'.1.out := Quotient.exact (Quotient.out_eq _).symm
    have h6 : A q' = Units.map (algebraMap (OF E) E).toMonoidHom v * a := Units.ext hv
    have h7 : P (Units.map (algebraMap (OF E) E).toMonoidHom v) ∈ hatOUnits c :=
      ⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c (v⁻¹ : (OF E)ˣ))⟩
    refine hq ⟨q', ?_⟩
    rw [← q.out_eq]
    show QuotientGroup.mk (P (A q') * y⁻¹) = _
    rw [h6, map_mul, mul_assoc, h4, QuotientGroup.mk_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 h7,
      (QuotientGroup.eq_one_iff _).2 (inv_mem hu), one_mul, mul_one]

end GlobalTheory.CMVal.LatEnt
