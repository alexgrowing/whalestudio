import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormOnValuationRing

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem norm_le_of_int {l : ℕ} [Fact l.Prime] {T : Type} [CommRing T] [Algebra ℤ_[l] T]
    [Algebra.IsIntegral ℤ_[l] T] (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T) : ‖φ x‖ ≤ 1 :=
  (int_iff_norm _).1 ((Algebra.IsIntegral.isIntegral x).map φ)

private theorem mem_max_iff {l : ℕ} [Fact l.Prime] {T : Type} [CommRing T] [IsLocalRing T] [Algebra ℤ_[l] T]
    [Algebra.IsIntegral ℤ_[l] T] (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T) : x ∈ maximalIdeal T ↔ ‖φ x‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.NormOnValuationRing.mem_max_iff φ x

private theorem exists_dvr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {σ : Type} [Finite σ] (b : σ → PadicAlgCl l)
    (hb : ∀ i, ‖b i‖ ≤ 1) :
    ∃ (A : Subalgebra O (PadicAlgCl l)), IsDiscreteValuationRing A ∧ Module.Finite O A ∧ ∀ i, b i ∈ A := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  let S : Set (PadicAlgCl l) := Set.range b ∪ algebraMap O _ '' s
  haveI : Finite S := ((Set.finite_range b).union (s.finite_toSet.image _)).to_subtype
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] S
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  let B := (integralClosure ℤ_[l] K).map f
  have hB : ∀ x ∈ S, IsIntegral ℤ_[l] x → x ∈ B := fun x hx hi =>
    ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hO : ∀ a : O, algebraMap O (PadicAlgCl l) a ∈ B := by
    intro a
    have ha : a ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      exact hB _ (Or.inr ⟨x, hx, rfl⟩)
        ((Algebra.IsIntegral.isIntegral x).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l)))
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]; exact B.mul_mem (B.algebraMap_mem c) hx
  let A : Subalgebra O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := hO }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  refine ⟨A, d1, ?_, fun i => hB _ (Or.inl ⟨i, rfl⟩) ((int_iff_norm _).2 (hb i))⟩
  haveI : Module.Finite ℤ_[l] A := d2
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O A

private theorem exists_co {O A : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing A] [IsLocalRing A] [Algebra O A] [Module.Finite O A] :
    ∃ (B : Subalgebra O A) (_ : IsCO O B), IsLocalHom B.val ∧ ∀ x ∈ maximalIdeal A, x ∈ B := by
  let B : Subalgebra O A :=
    { carrier := {x | ∃ a : O, x - algebraMap O A a ∈ maximalIdeal A}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        have : x * y - algebraMap O A (a * b) = x * (y - algebraMap O A b) + algebraMap O A b * (x - algebraMap O A a) := by
          rw [map_mul]; ring
        rw [this]
        exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ ha)
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have : x + y - algebraMap O A (a + b) = (x - algebraMap O A a) + (y - algebraMap O A b) := by
          rw [map_add]; ring
        rw [this]
        exact add_mem ha hb
      algebraMap_mem' := fun a => ⟨a, by simp⟩ }
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.tower_top (R := O)
  haveI hl : IsLocalHom (algebraMap B A) := Algebra.IsIntegral.isLocalHom B A
  haveI : IsLocalRing B := RingHom.domain_isLocalRing (algebraMap B A)
  haveI : Module.Finite O B := Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
  refine ⟨B, co_finite O O B fun x => ?_, ⟨fun a ha => hl.map_nonunit a ha⟩, fun x hx => ⟨0, by simpa using hx⟩⟩
  obtain ⟨a, ha⟩ := x.2
  exact ⟨a, fun hu => ha (hu.map (algebraMap B A))⟩

private theorem exists_norm_btwn {K : Type} [NontriviallyNormedField K] [IsAlgClosed K] {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) : ∃ t : K, x < ‖t‖ ∧ ‖t‖ < y := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hc0 : 0 < ‖c‖ := one_pos.trans hc
  have hL : 0 < Real.log ‖c‖ := Real.log_pos hc
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (div_lt_div_of_pos_right (Real.log_lt_log hx hxy) hL)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ q.num) q.den_pos
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_nz] at ht
    exact zpow_ne_zero _ (norm_pos_iff.1 hc0) ht.symm
  have h3 : (q.den : ℝ) * Real.log ‖t‖ = q.num * Real.log ‖c‖ := by
    rw [← Real.log_pow, ← Real.log_zpow, ← norm_pow, ← norm_zpow, ht]
  have h4 : Real.log ‖t‖ = q * Real.log ‖c‖ := by
    have hd : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
    rw [Rat.cast_def, div_mul_eq_mul_div, eq_div_iff hd, mul_comm, h3]
  have htp := norm_pos_iff.2 ht0
  refine ⟨t, ?_, ?_⟩
  · rw [← Real.log_lt_log_iff hx htp, h4]
    exact (div_lt_iff₀ hL).1 h1
  · rw [← Real.log_lt_log_iff htp (hx.trans hxy), h4]
    exact (lt_div_iff₀ hL).1 h2

private theorem exists_scale {K σ : Type} [NontriviallyNormedField K] [IsAlgClosed K] [Fintype σ] (w : σ → ℤ) (a : σ → K)
    (h0 : ∀ i, w i = 0 → ‖a i‖ < 1)
    (h1 : ∀ i h, 0 < w i → w h < 0 → ‖a i ^ (w h).natAbs * a h ^ (w i).natAbs‖ < 1) :
    ∃ t : Kˣ, ∀ i, ‖((t ^ w i : Kˣ) : K) * a i‖ < 1 := by
  classical
  have hc : ∀ i, ∃ c : K, w i ≠ 0 → c ^ (w i).natAbs = a i := fun i => by
    by_cases h : w i = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (a i) (Int.natAbs_pos.2 h)
      exact ⟨c, fun _ => hc⟩
  choose c hc using hc
  have h2 : ∀ i h, 0 < w i → w h < 0 → ‖c i‖ * ‖c h‖ < 1 := fun i h hi hh => by
    have := h1 i h hi hh
    rw [← hc i hi.ne', ← hc h hh.ne, ← pow_mul, ← pow_mul, mul_comm (w h).natAbs, ← mul_pow, norm_pow, norm_mul] at this
    exact lt_of_pow_lt_pow_left₀ _ zero_le_one (by rwa [one_pow])
  obtain ⟨L, hL0, hL1, hL2⟩ : ∃ L : ℝ, 0 ≤ L ∧ (∀ h, w h < 0 → ‖c h‖ ≤ L) ∧ ∀ i, 0 < w i → ‖c i‖ * L < 1 := by
    by_cases hne : (Finset.univ.filter fun h => w h < 0).Nonempty
    · obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image _ (fun h => ‖c h‖) hne
      exact ⟨‖c h‖, norm_nonneg _, fun h' hh' => hmax h' (by simpa using hh'),
        fun i hi => h2 i h hi (by simpa using hh)⟩
    · exact ⟨0, le_rfl, fun h hh => absurd ⟨h, by simpa using hh⟩ hne, fun i _ => by simp⟩
  have hev : ∀ᶠ y in nhds L, ∀ i, 0 < w i → ‖c i‖ * y < 1 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : 0 < w i
    · have : ContinuousAt (fun y : ℝ => ‖c i‖ * y) L := by fun_prop
      exact (this.eventually_lt continuousAt_const (hL2 i hi)).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h => absurd h hi
  obtain ⟨y, hy, hy2⟩ := hev.exists_gt
  obtain ⟨t, ht1, ht2⟩ := exists_norm_btwn (K := K) (x := (L + y) / 2) (y := y) (by linarith) (by linarith)
  have ht0 : 0 < ‖t‖ := by linarith
  refine ⟨Units.mk0 t (norm_pos_iff.1 ht0), fun i => ?_⟩
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rcases lt_trichotomy (w i) 0 with h | h | h
  · have e : w i = -((w i).natAbs : ℤ) := by omega
    rw [← hc i h.ne, e, _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow, ← mul_pow, norm_pow]
    refine pow_lt_one₀ (norm_nonneg _) ?_ (by omega)
    rw [norm_mul, norm_inv, inv_mul_lt_iff₀ ht0]
    have := hL1 i h
    linarith
  · rw [h, zpow_zero, one_mul]
    exact h0 i h
  · have e : w i = ((w i).natAbs : ℤ) := by omega
    rw [← hc i h.ne', e, zpow_natCast, Int.natAbs_natCast, ← mul_pow, norm_pow]
    refine pow_lt_one₀ (norm_nonneg _) ?_ (by omega)
    rw [norm_mul, mul_comm]
    exact (mul_le_mul_of_nonneg_left ht2.le (norm_nonneg _)).trans_lt (hy2 i h)

private theorem mono_mem {O σ : Type} [CommRing O] (w : σ → ℤ) (b : σ →₀ ℕ) :
    (MvPowerSeries.monomial b 1 : MvPowerSeries σ O) ∈ wtPart O w (Finsupp.weight w b) := fun n hn => by
  classical
  rw [MvPowerSeries.coeff_monomial, if_neg]
  rintro rfl
  exact hn rfl

private theorem ev_eq {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] (W : WPres O ℤ R) (P : Subalgebra O (MvPowerSeries W.σ O))
    (hP : ∀ {j f}, f ∈ wtPart O W.wt j → f ∈ P) (ψ : P →ₐ[O] K) (Φ : MvPowerSeries W.σ O →ₐ[O] K) (t : Kˣ)
    (hΦ : ∀ f, ‖Φ f‖ ≤ 1) (hψ : ∀ f (hf : f ∈ wtPart O W.wt 0), ‖ψ ⟨f, hP hf⟩‖ ≤ 1)
    (hX : ∀ i, Φ (MvPowerSeries.X i) = ((t ^ W.wt i : Kˣ) : K) * ψ ⟨_, hP (X_mem_wtPart O W.wt i)⟩)
    (hlt : ∀ i, ‖Φ (MvPowerSeries.X i)‖ < 1) (j : ℤ) (f : MvPowerSeries W.σ O) (hf : f ∈ wtPart O W.wt j) :
    Φ f = ((t ^ j : Kˣ) : K) * ψ ⟨f, hP hf⟩ := by
  classical
  have hmono : ∀ n : W.σ →₀ ℕ, Φ (MvPowerSeries.monomial n 1) =
      ((t ^ Finsupp.weight W.wt n : Kˣ) : K) * ψ ⟨_, hP (mono_mem W.wt n)⟩ := by
    intro n
    induction n using Finsupp.induction_linear with
    | zero =>
      have : (⟨_, hP (mono_mem W.wt 0)⟩ : P) = 1 := rfl
      rw [this]
      simp
    | add a b ha hb =>
      have e : (MvPowerSeries.monomial (a + b) 1 : MvPowerSeries W.σ O) =
          MvPowerSeries.monomial a 1 * MvPowerSeries.monomial b 1 := by
        rw [MvPowerSeries.monomial_mul_monomial, one_mul]
      have : (⟨_, hP (mono_mem W.wt (a + b))⟩ : P) = ⟨_, hP (mono_mem W.wt a)⟩ * ⟨_, hP (mono_mem W.wt b)⟩ :=
        Subtype.ext e
      rw [this, e, map_mul, map_mul, ha, hb, map_add, _root_.zpow_add, Units.val_mul]
      ring
    | single i k =>
      have : (⟨_, hP (mono_mem W.wt (Finsupp.single i k))⟩ : P) = ⟨_, hP (X_mem_wtPart O W.wt i)⟩ ^ k :=
        Subtype.ext (MvPowerSeries.X_pow_eq i k).symm
      rw [this, ← MvPowerSeries.X_pow_eq, map_pow, map_pow, hX, Finsupp.weight_single, mul_pow, nsmul_eq_mul,
        mul_comm (k : ℤ), _root_.zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  have hmlt : ∀ n : W.σ →₀ ℕ, n ≠ 0 → ‖Φ (MvPowerSeries.monomial n 1)‖ < 1 := by
    intro n hn
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hn
    have e : (MvPowerSeries.monomial n 1 : MvPowerSeries W.σ O) =
        MvPowerSeries.X i * MvPowerSeries.monomial (n - Finsupp.single i 1) 1 := by
      rw [MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul, add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hi
    rw [e, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hlt i) (hΦ _)
  have h0 : ∀ f (hf : f ∈ wtPart O W.wt 0), Φ f = ψ ⟨f, hP hf⟩ := by
    obtain ⟨μ, hμ, hd⟩ := part_span O R ℤ W {n | n ≠ 0 ∧ Finsupp.weight W.wt n = 0} 0 fun _ h => h.2
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ m ∈ μ, ‖Φ (MvPowerSeries.monomial m 1)‖ ≤ ρ := by
      rcases μ.eq_empty_or_nonempty with rfl | hne
      · exact ⟨0, le_rfl, one_pos, by simp⟩
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image μ (fun m => ‖Φ (MvPowerSeries.monomial m 1)‖) hne
        exact ⟨_, norm_nonneg _, hmlt m (hμ hm).1, hmax⟩
    have key : ∀ N : ℕ, ∀ f (hf : f ∈ wtPart O W.wt 0), ‖Φ f - ψ ⟨f, hP hf⟩‖ ≤ ρ ^ N := by
      intro N
      induction N with
      | zero =>
        intro f hf
        rw [pow_zero, sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hΦ f) (by rw [norm_neg]; exact hψ f hf))
      | succ N ih =>
        intro f hf
        obtain ⟨b, hb, he⟩ := hd (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (fun n hn => by
          rw [map_sub, MvPowerSeries.coeff_C]
          by_cases h0 : n = 0
          · subst h0; simp
          · rw [if_neg h0, sub_zero]
            exact hf n fun h => hn ⟨h0, h⟩)
        have he' : f = algebraMap O _ (MvPowerSeries.constantCoeff f) + ∑ m ∈ μ, b m * MvPowerSeries.monomial m 1 :=
          sub_eq_iff_eq_add'.1 he
        have he2 : (⟨f, hP hf⟩ : P) = algebraMap O _ (MvPowerSeries.constantCoeff f) +
            ∑ m ∈ μ, (⟨_, hP (hb m)⟩ : P) * ⟨_, hP (mono_mem W.wt m)⟩ := by
          apply Subtype.ext
          rw [Subalgebra.coe_add, AddSubmonoidClass.coe_finset_sum]
          exact he'
        have he3 : Φ f - ψ ⟨f, hP hf⟩ =
            ∑ m ∈ μ, (Φ (b m) - ψ ⟨_, hP (hb m)⟩) * Φ (MvPowerSeries.monomial m 1) := by
          rw [he2, congrArg Φ he', map_add, map_add, AlgHom.commutes, AlgHom.commutes, add_sub_add_left_eq_sub,
            map_sum, map_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [map_mul, map_mul, sub_mul, hmono m, congrArg (t ^ ·) (hμ hm).2]
          simp
        rw [he3]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m hm => ?_
        rw [norm_mul, pow_succ]
        exact mul_le_mul (ih _ (hb m)) (hρ m hm) (norm_nonneg _) (by positivity)
    intro f hf
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1) fun N => key N f hf
  obtain ⟨μ, hμ, hd⟩ := part_span O R ℤ W {n | Finsupp.weight W.wt n = j} j fun _ h => h
  obtain ⟨b, hb, he⟩ := hd f hf
  have he2 : (⟨f, hP hf⟩ : P) = ∑ m ∈ μ, (⟨_, hP (hb m)⟩ : P) * ⟨_, hP (mono_mem W.wt m)⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact he
  rw [he2, congrArg Φ he, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : Finsupp.weight W.wt m = j := hμ hm
  rw [map_mul, map_mul, h0 _ (hb m), hmono m, congrArg (t ^ ·) hm']
  ring

private theorem norm_facts {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {T : Type} [CommRing T] [IsLocalRing T]
    [Algebra O T] [Module.Finite O T] (φ : T →ₐ[O] PadicAlgCl l) (x : T) :
    ‖φ x‖ ≤ 1 ∧ (x ∈ maximalIdeal T ↔ ‖φ x‖ < 1) := by
  letI : Algebra ℤ_[l] T := ((algebraMap O T).comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite ℤ_[l] T := Module.Finite.trans O T
  exact ⟨norm_le_of_int (φ.restrictScalars ℤ_[l]) x, mem_max_iff (φ.restrictScalars ℤ_[l]) x⟩

private theorem zero_facts {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {Γ R : Type} [Group Γ]
    [CommRing R] [IsLocalRing R] [Algebra O R] (u : Γ →* GG 3 R) (hfin : Module.Finite O (wpart O u 0))
    (ξ : Sring O u →ₐ[O] PadicAlgCl l) (x : R) (hx : x ∈ wpart O u 0) :
    ‖ξ ⟨x, mem_Sring u hx⟩‖ ≤ 1 ∧ (x ∈ maximalIdeal R → ‖ξ ⟨x, mem_Sring u hx⟩‖ < 1) := by
  let T : Subalgebra O R := (wpart O u 0).toSubalgebra SetLike.GradedOne.one_mem fun x y hx hy => by
    simpa using SetLike.GradedMul.mul_mem hx hy
  haveI : Module.Finite O T := hfin
  haveI : IsLocalHom (T.val : T →+* R) := ⟨fun a ha => by
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hb' : (a : R) * b = 1 := hb
    have hbT : b ∈ wpart O u 0 := fun R' _ _ _ f f' t h => by
      have h1 := a.2 R' f f' t h
      rw [zpow_zero, Units.val_one, one_mul] at h1 ⊢
      calc f' b = f' b * f ((a : R) * b) := by rw [hb', map_one, mul_one]
        _ = f' ((a : R) * b) * f b := by rw [map_mul, map_mul, h1]; ring
        _ = f b := by rw [hb', map_one, one_mul]
    exact IsUnit.of_mul_eq_one (⟨b, hbT⟩ : T) (Subtype.ext hb')⟩
  haveI : IsLocalRing T := RingHom.domain_isLocalRing (T.val : T →+* R)
  have := norm_facts (ξ.comp (Subalgebra.inclusion (S := T) fun y hy => mem_Sring u hy)) ⟨x, hx⟩
  exact ⟨this.1, fun hm => this.2.1 fun hu => hm (hu.map T.val)⟩

private theorem exists_loc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {Γ R : Type} [Group Γ]
    [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R) (hfin : Module.Finite O (wpart O u 0))
    (ξ : Sring O u →ₐ[O] PadicAlgCl l) (W : WPres O ℤ R) (hW : ∀ j, W.part j = wpart O u j)
    (hzw : ∀ i, W.z i ∈ wpart O u (W.wt i)) {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] [Module.Finite O A]
    (v : A →ₐ[O] PadicAlgCl l) (hv : Function.Injective v) (t : (PadicAlgCl l)ˣ) (b : W.σ → A)
    (hb : ∀ i, v (b i) = ((t ^ W.wt i : (PadicAlgCl l)ˣ) : PadicAlgCl l) * ξ ⟨W.z i, mem_Sring u (hzw i)⟩)
    (ht : ∀ i, ‖v (b i)‖ < 1) :
    ∃ Ξ : R →ₐ[O] A, IsLocalHom Ξ ∧ ∀ j x (hx : x ∈ wpart O u j),
      v (Ξ x) = ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) * ξ ⟨x, mem_Sring u hx⟩ := by
  obtain ⟨B, hB, hBl, hBm⟩ := exists_co (O := O) (A := A)
  have hm : ∀ i, b i ∈ maximalIdeal A := fun i => (norm_facts v _).2.2 (ht i)
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := co_ev O O B W.σ (Algebra.ofId O B) (fun i => ⟨_, hBm _ (hm i)⟩)
    fun i hi => hm i (hi.map B.val)
  have hP : ∀ {j f}, f ∈ wtPart O W.wt j → f ∈ (Sring O u).comap W.π := fun {j f} hf =>
    mem_Sring u (j := j) (hW j ▸ ⟨f, hf, rfl⟩)
  have hX : ∀ i, (v.comp (B.val.comp Φ)) (MvPowerSeries.X i) = v (b i) := fun i => by
    simp only [AlgHom.comp_apply, hΦ]
    rfl
  have key : ∀ j f (hf : f ∈ wtPart O W.wt j), v (Φ f : A) =
      ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) * ξ ⟨W.π f, hP hf⟩ :=
    ev_eq W ((Sring O u).comap W.π) hP
      (ξ.comp ((W.π.comp ((Sring O u).comap W.π).val).codRestrict (Sring O u) fun x => x.2))
      (v.comp (B.val.comp Φ)) t (fun f => (norm_facts v _).1)
      (fun f hf => (zero_facts u hfin ξ _ (hW 0 ▸ ⟨f, hf, rfl⟩)).1) (fun i => (hX i).trans (hb i))
      (fun i => by rw [hX]; exact ht i)
  have hker : ∀ f ∈ RingHom.ker W.π, Φ f = 0 := by
    obtain ⟨n, f, c, hf, hJ⟩ := ker_gen O ℤ W.σ W.wt _ W.homog
    have : Ideal.span (Set.range f) ≤ RingHom.ker Φ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : W.π (f i) = 0 := by
        rw [← RingHom.mem_ker, hJ]
        exact Ideal.subset_span ⟨i, rfl⟩
      have h2 := key _ _ (hf i)
      rw [show (⟨W.π (f i), hP (hf i)⟩ : Sring O u) = 0 from Subtype.ext h1, map_zero, mul_zero] at h2
      exact Subtype.ext (hv (h2.trans (map_zero v).symm))
    intro g hg
    rw [hJ] at hg
    exact this hg
  let Ξ : R →ₐ[O] B := (Ideal.Quotient.liftₐ (RingHom.ker W.π) Φ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hΞ : ∀ f, Ξ (W.π f) = Φ f := fun f => by
    have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π f) = Ideal.Quotient.mk _ f := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Φ hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π f)) = _
    rw [this]
    rfl
  refine ⟨B.val.comp Ξ, ⟨fun x hx => ?_⟩, fun j x hx => ?_⟩
  · by_contra hn
    have h1 : Ξ x ∈ maximalIdeal B := by
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hn
    exact h1 (hBl.map_nonunit _ hx)
  · obtain ⟨f, hf, rfl⟩ : x ∈ W.part j := hW j ▸ hx
    exact (congrArg (fun y : B => v y) (hΞ f)).trans (key j f hf)

theorem UpperTheory.V.UnitaryThreeInertia.isCharZeroPt_of_isPtHom :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → ∀ (ξ : Sring O u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG 3 (PadicAlgCl l)), IsPtHom u ξ r → F.IsCharZeroPt g₁ r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr
  obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
  have hzw : ∀ i, W.z i ∈ wpart O u (W.wt i) := fun i => hW.part _ ▸ W.z_mem i
  have hzm : ∀ i, W.z i ∈ maximalIdeal R := fun i => by
    obtain ⟨g, a, b, -, -, e⟩ := hW.var i
    rw [e]
    exact hu.pt.red g a b
  obtain ⟨t, ht⟩ := exists_scale W.wt (fun i => ξ ⟨W.z i, mem_Sring u (hzw i)⟩)
    (fun i hi => (zero_facts u hfin ξ _ (hi ▸ hzw i)).2 (hzm i))
    (fun i h hi hh => by
      have h1 : W.z i ^ (W.wt h).natAbs * W.z h ^ (W.wt i).natAbs ∈ wpart O u 0 := by
        have h2 := SetLike.mul_mem_graded (SetLike.pow_mem_graded (W.wt h).natAbs (hzw i))
          (SetLike.pow_mem_graded (W.wt i).natAbs (hzw h))
        have h3 : (W.wt h).natAbs • W.wt i + (W.wt i).natAbs • W.wt h = 0 := by
          rw [nsmul_eq_mul, nsmul_eq_mul, Int.natCast_natAbs, Int.natCast_natAbs, abs_of_neg hh, abs_of_pos hi]
          ring
        rwa [h3] at h2
      rw [← map_pow, ← map_pow, ← map_mul]
      exact (zero_facts u hfin ξ _ h1).2
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hzm h) _ (Int.natAbs_pos.2 hi.ne'))))
  obtain ⟨A, hA, hAf, hbA⟩ := exists_dvr (O := O) _ fun i => (ht i).le
  haveI : IsLocalRing A := hA.toIsLocalRing
  obtain ⟨Ξ, hΞ, key⟩ := exists_loc u hfin ξ W hW.part hzw A.val Subtype.val_injective t (fun i => ⟨_, hbA i⟩)
    (fun _ => rfl) ht
  refine ⟨A, hA, hAf, t, push Ξ u, isPt_push F _ g₁ u hu.pt, MonoidHom.ext fun g => ?_⟩
  refine SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) ?_
  · refine Eq.trans ?_ ((conjBy_tor r t).1 g a b).symm
    rw [(hr g).2]
    exact key _ _ (entry_mem u g a b)
  · rw [(conjBy_tor r t).2.1, (hr g).1]
    rfl
