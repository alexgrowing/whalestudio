import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe

open MvPowerSeries

namespace GlobalTheory.LocalUnit

section Gauss

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {σ : Type} [Finite σ]

omit [Finite σ] in
theorem coeff_rescale_const (t : O) (H : MvPowerSeries σ O) (m : σ →₀ ℕ) :
    coeff m (rescale (fun _ => t) H) = t ^ m.degree * coeff m H := by
  rw [coeff_rescale, Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem exists_max_coeff (hv : v.Integers O) {t : O} (ht : v (algebraMap O C t) < 1) (H : MvPowerSeries σ O)
    (h0 : constantCoeff H ≠ 0) :
    ∃ m₀, ∀ m, v (algebraMap O C (coeff m (rescale (fun _ => t) H))) ≤
      v (algebraMap O C (coeff m₀ (rescale (fun _ => t) H))) := by
  have hpos : 0 < v (algebraMap O C (constantCoeff H)) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun h => h0 (hv.hom_inj (h.trans (map_zero _).symm))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hpos ht
  obtain ⟨m₀, -, hm₀⟩ := Set.exists_max_image _
    (fun m => v (algebraMap O C (coeff m (rescale (fun _ => t) H)))) (Finsupp.finite_of_degree_le (σ := σ) n)
    ⟨0, by simp⟩
  refine ⟨m₀, fun m => ?_⟩
  by_cases hm : m.degree ≤ n
  · exact hm₀ m hm
  · refine le_trans ?_ (hm₀ 0 (by simp))
    simp only [coeff_rescale_const, map_zero, pow_zero, one_mul, map_mul, map_pow,
      coeff_zero_eq_constantCoeff_apply]
    refine le_trans (mul_le_of_le_one_right' (hv.map_le_one _)) (le_trans ?_ hn.le)
    exact pow_le_pow_right_of_le_one' ht.le (by omega)

omit [Finite σ] in

theorem exists_eq_C_mul {x : O} {H : MvPowerSeries σ O} (h : ∀ m, x ∣ coeff m H) :
    ∃ H' : MvPowerSeries σ O, H = MvPowerSeries.C x * H' := by
  choose y hy using h
  refine ⟨y, ?_⟩
  ext m
  exact (hy m).trans (coeff_C_mul m (y : MvPowerSeries σ O) x).symm

omit [Finite σ] in

theorem exists_primitive [IsLocalRing O] (hv : v.Integers O) {H : MvPowerSeries σ O} {m₀ : σ →₀ ℕ}
    (h : ∀ m, v (algebraMap O C (coeff m H)) ≤ v (algebraMap O C (coeff m₀ H))) (h0 : coeff m₀ H ≠ 0) :
    ∃ H' : MvPowerSeries σ O, H = MvPowerSeries.C (coeff m₀ H) * H' ∧
      MvPowerSeries.map (IsLocalRing.residue O) H' ≠ 0 := by
  haveI := hv.hom_inj.isDomain
  obtain ⟨H', hH'⟩ := exists_eq_C_mul (x := coeff m₀ H) (H := H) fun m => hv.dvd_of_le (h m)
  refine ⟨H', hH', fun h1 => ?_⟩
  have h2 := congrArg (coeff m₀) hH'
  rw [coeff_C_mul] at h2
  have h3 : coeff m₀ H' = 1 := mul_left_cancel₀ h0 (by rw [mul_one]; exact h2.symm)
  have h4 := congrArg (coeff m₀) h1
  rw [coeff_map, h3, map_one, map_zero] at h4
  exact one_ne_zero h4

theorem constantCoeff_dvd [IsAlgClosed C] [IsLocalRing O] (hv : v.Integers O) {F G : MvPowerSeries σ O} {c : O}
    (hc : c ≠ 0) (h : F * G = MvPowerSeries.C c) (m : σ →₀ ℕ) : constantCoeff F ∣ coeff m F := by
  classical
  haveI := hv.hom_inj.isDomain
  have hab : constantCoeff F * constantCoeff G = c := by
    rw [← map_mul, h, constantCoeff_C]
  have ha : constantCoeff F ≠ 0 := fun h0 => hc (by rw [← hab, h0, zero_mul])
  have hb : constantCoeff G ≠ 0 := fun h0 => hc (by rw [← hab, h0, mul_zero])
  have hpos : ∀ x : O, x ≠ 0 → 0 < v (algebraMap O C x) := fun x hx => by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun h => hx (hv.hom_inj (h.trans (map_zero _).symm))
  by_contra hn
  rw [hv.dvd_iff_le, not_le] at hn
  obtain ⟨s, hs⟩ := hv.dvd_of_le hn.le
  have hs0 : s ≠ 0 := fun h0 => ha (by rw [hs, h0, mul_zero])
  have hm0 : coeff m F ≠ 0 := fun h0 => ha (by rw [hs, h0, zero_mul])
  have hs1 : v (algebraMap O C s) < 1 := by
    rw [hs, map_mul, map_mul] at hn
    exact (mul_lt_iff_lt_one_right (hpos _ hm0)).1 hn
  obtain ⟨t', ht'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C s) (n := m.degree + 1) (by omega)
  have ht1 : v t' < 1 := by
    rw [← ht', map_pow] at hs1
    exact (pow_lt_one_iff_of_nonneg zero_le (by omega)).1 hs1
  obtain ⟨t, rfl⟩ := hv.exists_of_le_one ht1.le
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hs0
    apply hv.hom_inj
    rw [← ht']
    simp
  obtain ⟨i, hi⟩ := exists_max_coeff hv ht1 F ha
  obtain ⟨j, hj⟩ := exists_max_coeff hv ht1 G hb
  have hi' : v (algebraMap O C (constantCoeff F)) <
      v (algebraMap O C (coeff i (rescale (fun _ => t) F))) := by
    refine lt_of_lt_of_le ?_ (hi m)
    rw [coeff_rescale_const, hs, map_mul, map_mul, map_mul, map_mul, ← ht', map_pow, map_pow, map_pow, pow_succ,
      mul_comm]
    refine mul_lt_mul_of_pos_right ?_ (hpos _ hm0)
    exact mul_lt_of_lt_one_right (pow_pos (hpos _ ht0) _) ht1
  have hj' : v (algebraMap O C (constantCoeff G)) ≤
      v (algebraMap O C (coeff j (rescale (fun _ => t) G))) := by
    have := hj 0
    rwa [coeff_rescale_const, map_zero, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply] at this
  have hx : coeff i (rescale (fun _ => t) F) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hi'
    exact not_lt_zero hi'
  have hy : coeff j (rescale (fun _ => t) G) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hj'
    exact (hpos _ hb).not_ge hj'
  obtain ⟨F', hF', hF⟩ := exists_primitive hv hi hx
  obtain ⟨G', hG', hG⟩ := exists_primitive hv hj hy
  have hFG := mul_ne_zero hF hG
  rw [← map_mul] at hFG
  obtain ⟨k, hk⟩ : ∃ k, IsUnit (coeff k (F' * G')) := by
    by_contra hk
    apply hFG
    ext k
    rw [coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff]
    exact fun hu => hk ⟨k, hu⟩
  generalize coeff i (rescale (fun _ => t) F) = x at *
  generalize coeff j (rescale (fun _ => t) G) = y at *
  have e1 : coeff k (rescale (fun _ => t) (F * G)) = x * y * coeff k (F' * G') := by
    rw [map_mul, hF', hG', mul_mul_mul_comm, ← map_mul, coeff_C_mul]
  rw [h, coeff_rescale_const, coeff_C] at e1
  split_ifs at e1 with hk0
  · rw [hk0, map_zero, pow_zero, one_mul, ← hk0, ← hab] at e1
    have e2 := congrArg (fun z => v (algebraMap O C z)) e1
    simp only [map_mul] at e2
    rw [hv.isUnit_iff_valuation_eq_one.1 hk, mul_one] at e2
    exact (mul_lt_mul hi' hj' (hpos _ hb) zero_le).ne e2
  · rw [mul_zero] at e1
    exact mul_ne_zero (mul_ne_zero hx hy) hk.ne_zero e1.symm

theorem exists_eq_C_mul_unit [IsAlgClosed C] [IsLocalRing O] (hv : v.Integers O) {F G : MvPowerSeries σ O} {c : O}
    (hc : c ≠ 0) (h : F * G = MvPowerSeries.C c) :
    ∃ U : MvPowerSeries σ O, IsUnit U ∧ F = MvPowerSeries.C (constantCoeff F) * U := by
  haveI := hv.hom_inj.isDomain
  obtain ⟨U, hU⟩ := exists_eq_C_mul (constantCoeff_dvd hv hc h)
  refine ⟨U, ?_, hU⟩
  have ha : constantCoeff F ≠ 0 := fun h0 => hc (by
    rw [← constantCoeff_C (σ := σ) c, ← h, map_mul, h0, zero_mul])
  have h1 := congrArg constantCoeff hU
  rw [map_mul, constantCoeff_C] at h1
  rw [isUnit_iff_constantCoeff, mul_left_cancel₀ ha (h1.symm.trans (mul_one _).symm)]
  exact isUnit_one

end Gauss

section Complete

variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B]

theorem fg_ker [Module.Finite O B] (ψ : B →ₐ[O] O) : (RingHom.ker ψ).FG := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := O) (M := B)
  have : RingHom.ker ψ = Ideal.span (Set.range fun i => b i - algebraMap O B (ψ (b i))) := by
    apply le_antisymm
    · have key : ∀ x ∈ Submodule.span O (Set.range b), x - algebraMap O B (ψ x) ∈
          Ideal.span (Set.range fun i => b i - algebraMap O B (ψ (b i))) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Ideal.subset_span ⟨i, rfl⟩
        | zero => simp
        | add x y _ _ hx hy =>
          have := add_mem hx hy
          rwa [sub_add_sub_comm, ← map_add, ← map_add] at this
        | smul r x _ hx =>
          have := Ideal.mul_mem_left _ (algebraMap O B r) hx
          rwa [mul_sub, ← map_mul, ← Algebra.smul_def, ← smul_eq_mul, ← map_smul] at this
      intro x hx
      have := key x (hb ▸ Submodule.mem_top)
      rwa [RingHom.mem_ker.1 hx, map_zero, sub_zero] at this
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
  rw [this]
  exact Submodule.fg_span (Set.finite_range _)

theorem maximalIdeal_le_radical [IsLocalRing O] [IsLocalRing B] [Module.Finite O B] (I : Ideal O)
    (hI : IsLocalRing.maximalIdeal O ≤ I.radical) :
    IsLocalRing.maximalIdeal B ≤ (I.map (algebraMap O B)).radical := by
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro Q ⟨hQ, hQp⟩
  have h1 : IsLocalRing.maximalIdeal O ≤ Q.comap (algebraMap O B) :=
    hI.trans ((Ideal.IsPrime.radical_le_iff inferInstance).2 (Ideal.map_le_iff_le_comap.1 hQ))
  have h2 : (Q.comap (algebraMap O B)).IsMaximal := by
    rw [← (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) h1]
    infer_instance
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q h2)).ge

theorem exists_complete [IsLocalRing O] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B] (I : Ideal O)
    [hO : IsAdicComplete I O] (hI : IsLocalRing.maximalIdeal O ≤ I.radical) (ψ : B →ₐ[O] O) :
    ∃ J : Ideal B, IsAdicComplete J B ∧ RingHom.ker ψ ≤ J := by
  have h1 := GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O I hO B
  have h2 : RingHom.ker ψ ≤ (I.map (algebraMap O B)).radical :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)).trans (maximalIdeal_le_radical I hI)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h2 (fg_ker ψ)
  refine ⟨RingHom.ker ψ ⊔ I.map (algebraMap O B), ?_, le_sup_left⟩
  have h3 : (RingHom.ker ψ ⊔ I.map (algebraMap O B)) ^ (n + 1) ≤ I.map (algebraMap O B) :=
    Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le hn (pow_one _).le)
  exact GlobalTheory.isAdicComplete_of_pow_le_of_pow_le B _ _ 1 (n + 1) ((pow_one _).le.trans le_sup_right) h3 h1

end Complete

theorem localUnits : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → GlobalTheory.WeilIntegral.LocalUnits O := by
  intro p _ C _ _ _ v O _ _ _ _ hv R _ _ _ B _ _ _ _ _ θ ψ f g c hc hfg
  haveI := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hI : IsLocalRing.maximalIdeal O ≤ (Ideal.span {(p : O)}).radical := by
    intro x hx
    have h1 : v (algebraMap O C x) < 1 :=
      lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
    have hp : (0 : NNReal) < v (algebraMap O C (p : O)) := by
      rw [map_natCast, pos_iff_ne_zero, Valuation.ne_zero_iff]
      exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    obtain ⟨M, hM⟩ := NNReal.exists_pow_lt_of_lt_one hp h1
    refine ⟨M, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
    rw [map_pow, map_pow]
    exact hM.le
  obtain ⟨J, hJ, hψ⟩ := exists_complete _ hI ψ
  obtain ⟨s, hs, ι, τ, _, _, ⟨Q⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth O
    ((IsLocalRing.maximalIdeal B).comap θ)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension O (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨π, hπ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension O (Localization.Away s)
  have hs' : IsUnit (θ s) := by
    by_contra h
    exact hs h
  let θ' : Localization.Away s →ₐ[O] B := IsLocalization.Away.liftAlgHom s hs'
  have hθ : ∀ r, θ' (algebraMap R _ r) = θ r := fun r => by simp [θ']
  obtain ⟨φ, hφ₁, hφ₂⟩ := GlobalTheory.FormalChart.exists_expansion π hπ (ψ.comp θ')
  obtain ⟨w, -, hw⟩ := GlobalTheory.FormalChart.exists_factor π hπ (ψ.comp θ') φ hφ₁ hφ₂ J θ' fun b =>
    hψ (by simp [RingHom.mem_ker])
  have h1 : φ (algebraMap R _ f) * φ (algebraMap R _ g) = MvPowerSeries.C c := by
    rw [← map_mul, ← map_mul, hfg, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  obtain ⟨U, hU, hF⟩ := exists_eq_C_mul_unit hv hc h1
  obtain ⟨u, hu⟩ := hU.map w
  refine ⟨u, ?_⟩
  have h2 := congrArg w hF
  rw [hφ₁, map_mul, ← hu, AlgHom.comp_apply, hθ, ← AlgHom.comp_apply, hw, hθ] at h2
  rw [← w.commutes]
  exact h2

end GlobalTheory.LocalUnit
