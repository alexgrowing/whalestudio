import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.HeckeTheorem
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar partialLFunction coe_localChar continuous_localChar)
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.HeckePartial

theorem localChar_inv' (c : HeckeCharacter ℚ) (v : Pl) : localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rfl

theorem isReal_all (w : InfinitePlace ℚ) : w.IsReal := IsTotallyReal.isReal w

theorem tau_zero (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) (w : InfinitePlace ℚ) :
    c.infiniteTau w = 0 := by
  have hw : w.IsReal := isReal_all w
  by_contra hτ
  have hx : 0 < Real.exp (Real.pi / c.infiniteTau w) := Real.exp_pos _
  have h1 := c.realComponent_eq_one_of_isOfFinOrder hc hw (x := Units.mk0 _ hx.ne') hx
  have h2 := c.infiniteComponent_eq w (realUnitsHom hw (Units.mk0 _ hx.ne'))
  have hι : extensionEmbedding w ((realUnitsHom hw (Units.mk0 _ hx.ne') : (w.Completion)ˣ) : w.Completion) =
      ((Real.exp (Real.pi / c.infiniteTau w) : ℝ) : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw, extensionEmbeddingOfIsReal_realUnitsHom]
    rfl
  have hn : ‖((realUnitsHom hw (Units.mk0 _ hx.ne') : (w.Completion)ˣ) : w.Completion)‖ =
      Real.exp (Real.pi / c.infiniteTau w) := by
    have := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
      ((realUnitsHom hw (Units.mk0 _ hx.ne') : (w.Completion)ˣ) : w.Completion)
    rw [extensionEmbeddingOfIsReal_realUnitsHom] at this
    rw [← this]
    simp [abs_of_pos hx]
  have h3 : ((c.infiniteComponent w (realUnitsHom hw (Units.mk0 _ hx.ne')) : Circle) : ℂ) = 1 := by
    have : c.infiniteComponent w (realUnitsHom hw (Units.mk0 _ hx.ne')) = 1 := h1
    rw [this]; simp
  rw [h3, hι, hn, InfinitePlace.mult, if_pos hw, pow_one] at h2
  have h0 : ((Real.exp (Real.pi / c.infiniteTau w) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  rw [div_self h0, one_zpow, one_mul, Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log hx.le, Real.log_exp] at h2
  have h4 : ((Real.pi / c.infiniteTau w : ℝ) : ℂ) * (((c.infiniteTau w : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    have : ((c.infiniteTau w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ
    push_cast
    field_simp
  rw [h4, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem weight_eq (c : HeckeCharacter ℚ) (δ : Bool)
    (hs : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) (w : InfinitePlace ℚ) :
    c.infiniteWeight w = if δ then 1 else 0 := by
  have hw : w.IsReal := isReal_all w
  have h2 := c.infiniteComponent_eq w (-1)
  obtain ⟨h0, h1⟩ := c.infiniteWeight_of_isReal hw
  rw [hs w] at h2
  have e1 : extensionEmbedding w (((-1 : (w.Completion)ˣ)) : w.Completion) = -1 := by
    simp
  have e2 : ‖(((-1 : (w.Completion)ˣ)) : w.Completion)‖ = 1 := by
    simp
  rw [e1, e2] at h2
  have hm : c.infiniteWeight w = 0 ∨ c.infiniteWeight w = 1 := by omega
  rcases hm with hm | hm <;> cases δ <;> simp [hm] at h2 ⊢
  · norm_num at h2
  · norm_num at h2

theorem gammaFactor_eq (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) (δ : Bool)
    (hs : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) (s : ℂ) :
    c.gammaFactor s = Complex.Gammaℝ (s + if δ then 1 else 0) := by
  rw [HeckeCharacter.gammaFactor, Fintype.prod_subsingleton _ Rat.infinitePlace,
    HeckeCharacter.infiniteGamma, if_pos (isReal_all _), tau_zero c hc, weight_eq c δ hs]
  cases δ <;> simp

theorem weight_prod (c : HeckeCharacter ℚ) (δ : Bool)
    (hs : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) :
    (∏ w, (-Complex.I) ^ (c.infiniteWeight w).natAbs) = if δ then -Complex.I else 1 := by
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, weight_eq c δ hs]
  cases δ <;> simp

theorem discrNorm_eq (c : HeckeCharacter ℚ) : c.discrNormConductor = (Ideal.absNorm c.conductor : ℝ) := by
  rw [HeckeCharacter.discrNormConductor, Rat.numberField_discr]
  simp

theorem exp_zero_of_unit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {μ : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) : quasiCharExponent μ = 0 := by
  unfold quasiCharExponent
  rw [hμ.2]
  simp

theorem lf_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {μ : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) {s : ℂ} (hs : 0 < s.re) :
    localLFactor μ s ≠ 0 :=
  localLFactor_ne_zero hμ.1 (by rw [exp_zero_of_unit hμ]; simpa using hs)

theorem differentiable_lf_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (μ : Fˣ →* ℂˣ) :
    Differentiable ℂ fun s => (localLFactor μ s)⁻¹ := by
  by_cases h : IsUnramifiedChar μ
  · have hq : (residueCard F : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.2 (by have := one_lt_residueCard (K := F); omega)
    have : (fun s => (localLFactor μ s)⁻¹) =
        fun s : ℂ => 1 - ((μ (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s) := by
      funext s
      rw [localLFactor_of_isUnramified h, inv_inv]
    rw [this]
    exact (differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_id.neg.const_cpow (Or.inl hq)))
  · have : (fun s => (localLFactor μ s)⁻¹) = fun _ : ℂ => (1 : ℂ) := by
      funext s
      rw [localLFactor_of_not_isUnramified h, inv_one]
    rw [this]
    exact differentiable_const _

theorem partial_conductor (c : HeckeCharacter ℚ) {s : ℂ} (hs : 1 < s.re) :
    partialLFunction c c.conductorPrimes s = c.LFunction s := by
  refine (GroundTheory.Automorphic.GodementSection.hasSum_partialLFunction c _ hs).unique ?_
  convert c.hasSum_LFunction hs using 2 with I
  split_ifs with h
  · rfl
  · push Not at h
    obtain ⟨v, hv, hd⟩ := h
    rw [c.coeff_of_not, zero_mul]
    rintro ⟨-, hco⟩
    have hd' := c.mem_conductorPrimes.1 hv
    have h1 : v.asIdeal ∣ 1 := by
      rw [Ideal.isCoprime_iff_sup_eq] at hco
      have := Ideal.dvd_iff_le.1 hd
      have h2 := Ideal.dvd_iff_le.1 hd'
      rw [Ideal.one_eq_top, ← hco, Ideal.dvd_iff_le]
      exact sup_le this h2
    exact v.isPrime.ne_top (by
      rw [Ideal.one_eq_top, Ideal.dvd_iff_le, top_le_iff] at h1
      exact h1)

theorem euler (hE : E2) (c : HeckeCharacter ℚ) (S : Finset Pl)
    (hS : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) {s : ℂ} (hs : 1 < s.re) :
    c.LFunction s = Lp c S s * ∏ v ∈ S, localLFactor (localChar c v) s := by
  classical
  set L : Pl → ℂ := fun v => localLFactor (localChar c v) s with hL
  have hS₀ : ∀ v ∉ c.conductorPrimes, IsUnramifiedChar (localChar c v) := fun v hv =>
    (c.isUnramifiedChar_localChar_iff v).2 fun h => hv (c.mem_conductorPrimes.2 h)
  have h0 := ((hE c.conductorPrimes s hs).1 c hS₀).2
  have h1 := ((hE S s hs).1 c hS).2
  rw [partial_conductor c hs] at h0
  have hLp : Lp c S s = partialLFunction c S s := h1.tprod_eq
  have h0' : HasProd L (c.LFunction s) := by
    have e : (({v | v ∉ c.conductorPrimes} : Set Pl).mulIndicator L) = L := by
      funext v
      by_cases hv : v ∈ c.conductorPrimes
      · have hr : ¬ IsUnramifiedChar (localChar c v) := by
          rw [c.isUnramifiedChar_localChar_iff v, not_not]
          exact c.mem_conductorPrimes.1 hv
        rw [Set.mulIndicator_of_notMem (by simpa using hv)]
        exact (localLFactor_of_not_isUnramified hr s).symm
      · exact Set.mulIndicator_of_mem (by simpa using hv) _
    rw [← e]
    exact hasProd_subtype_iff_mulIndicator.1 h0
  have h1' : HasProd (({v | v ∉ S} : Set Pl).mulIndicator L) (Lp c S s) := by
    rw [hLp]
    exact hasProd_subtype_iff_mulIndicator.1 h1
  have h2 : HasProd ((S : Set Pl).mulIndicator L) (∏ v ∈ S, L v) := by
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Pl)
      (f := (S : Set Pl).mulIndicator L) (s := S)
      (fun v hv => Set.mulIndicator_of_notMem (by simpa using hv) _)
    rwa [Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (by simpa using hv) _] at h
  have h3 := h1'.mul h2
  have e : (fun v => ({v | v ∉ S} : Set Pl).mulIndicator L v * (S : Set Pl).mulIndicator L v) = L := by
    funext v
    by_cases hv : v ∈ S
    · rw [Set.mulIndicator_of_notMem (by simpa using hv), Set.mulIndicator_of_mem (by simpa using hv), one_mul]
    · rw [Set.mulIndicator_of_mem (by simpa using hv), Set.mulIndicator_of_notMem (by simpa using hv), mul_one]
  rw [e] at h3
  exact h0'.unique h3

theorem eps_shift (c : HeckeCharacter ℚ) (v : Pl) (hψ : IsStd (localAdelicChar ℚ v)) (s : ℂ) :
    localEpsilon (localChar c v) (localAdelicChar ℚ v) s =
      localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2) *
        (((Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal c.conductor : ℕ) : ℝ) : ℂ) ^ (1 / 2 - s) := by
  have hcond : addCharConductor (localAdelicChar ℚ v) = 0 := hψ.2.2
  by_cases h : IsUnramifiedChar (localChar c v)
  · have hf : multiplicity v.asIdeal c.conductor = 0 :=
      multiplicity_eq_zero.2 ((c.isUnramifiedChar_localChar_iff v).1 h)
    rw [localEpsilon_of_isUnramified h, localEpsilon_of_isUnramified h, hcond, hf]
    simp
  · rw [localEpsilon_of_not_isUnramified_eq h, localEpsilon_of_not_isUnramified_eq h, hcond,
      c.quasiCharConductor_localChar v, residueCard_adicCompletion]
    set f := multiplicity v.asIdeal c.conductor
    set q := Ideal.absNorm v.asIdeal
    have hq : (q : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have e : (((q ^ f : ℕ) : ℝ) : ℂ) ^ (1 / 2 - s) = (q : ℂ) ^ ((f : ℂ) * (1 / 2 - s)) := by
      rw [Complex.natCast_cpow_natCast_mul]
      push_cast
      rfl
    rw [e]
    have e2 : (q : ℂ) ^ (((0 - (f : ℤ) : ℤ) : ℂ) * s) =
        (q : ℂ) ^ (((0 - (f : ℤ) : ℤ) : ℂ) * (1 / 2)) * (q : ℂ) ^ ((f : ℂ) * (1 / 2 - s)) := by
      rw [← Complex.cpow_add _ _ hq]
      congr 1
      push_cast
      ring
    rw [e2]
    ring

theorem eps_half_unr (c : HeckeCharacter ℚ) (v : Pl) (hψ : IsStd (localAdelicChar ℚ v))
    (h : IsUnramifiedChar (localChar c v)) :
    localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2) = 1 := by
  rw [localEpsilon_of_isUnramified h, hψ.2.2]
  simp

theorem rootNumber_eq (c : HeckeCharacter ℚ) :
    c.rootNumber = (∏ w, (-Complex.I) ^ (c.infiniteWeight w).natAbs) *
      ∏ᶠ v, localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2) := by
  rw [HeckeCharacter.rootNumber, HeckeCharacter.fourierConst,
    ← c.finiteFourier_mul_eq_finprod_localEpsilon c.toFractionalIdeal_conductorDifferentIdele]
  ring

theorem prod_eps (c : HeckeCharacter ℚ) (S : Finset Pl) (hψ : ∀ v, IsStd (localAdelicChar ℚ v))
    (hS : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) (s : ℂ) :
    ∏ v ∈ S, localEpsilon (localChar c v) (localAdelicChar ℚ v) s =
      (∏ᶠ v, localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2)) *
        (c.discrNormConductor : ℂ) ^ (1 / 2 - s) := by
  classical
  have h1 : (∏ᶠ v, localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2)) =
      ∏ v ∈ S, localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      by_contra h
      exact hv (eps_half_unr c v (hψ v) (hS v h))
  have hsub : c.conductorPrimes ⊆ S := fun v hv => by
    by_contra h
    exact (c.isUnramifiedChar_localChar_iff v).1 (hS v h) (c.mem_conductorPrimes.1 hv)
  have h2 : (Ideal.absNorm c.conductor : ℝ) =
      ∏ v ∈ S, ((Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal c.conductor : ℕ) : ℝ) := by
    rw [c.absNorm_conductor, Nat.cast_prod]
    refine Finset.prod_subset hsub fun v _ hv => ?_
    have : multiplicity v.asIdeal c.conductor = 0 :=
      multiplicity_eq_zero.2 fun hd => hv (c.mem_conductorPrimes.2 hd)
    simp [this]
  rw [h1, discrNorm_eq, h2, GroundTheory.Automorphic.GodementSection.ofReal_prod_cpow _ _ (fun _ => by positivity),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eps_shift c v (hψ v) s

theorem not_cpow_of_ne (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) (h1 : c ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup ℚ,
      (c.toIdele x : ℂ) = ((ideleModule ℚ x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  rintro ⟨τ, hτ⟩
  have h0 : τ = 0 := by
    rw [← HeckeCharacter.infiniteTau_of_forall hτ Rat.infinitePlace]
    exact tau_zero c hc _
  subst h0
  apply h1
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine Circle.ext ?_
  have h := hτ y
  simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero] at h
  exact h

theorem one_cpow (x : IdeleGroup ℚ) :
    ((1 : HeckeCharacter ℚ).toIdele x : ℂ) = ((ideleModule ℚ x : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) * Complex.I) := by
  simp [HeckeCharacter.toIdele_apply]

theorem isPreconnected_U : IsPreconnected (({0, 1} : Set ℂ)ᶜ) := by
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_ ?_).isConnected.isPreconnected
  · rw [Complex.rank_real_complex]
    norm_num
  · exact (Set.toFinite _).countable

theorem cont_one :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (1 : HeckeCharacter ℚ).LFunction s) ∧
      (∀ s, Strip s → G s * ((1 : HeckeCharacter ℚ).discrNormConductor : ℂ) ^ (s / 2) * (1 : HeckeCharacter ℚ).gammaFactor s =
        (s - 1) * (1 : HeckeCharacter ℚ).completedLFunction s) ∧ G 1 ≠ 0 := by
  set χ : HeckeCharacter ℚ := 1 with hχ
  obtain ⟨g, hgd, hgL, r, hr, hlim⟩ := χ.exists_LFunction_continuation_of_forall (τ := 0) one_cpow
  have e1 : (1 : ℂ) - ((0 : ℝ) : ℂ) * Complex.I = 1 := by simp
  rw [e1] at hgd hlim
  set h : ℂ → ℂ := fun s => (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ with hh
  have hhd : Differentiable ℂ h := χ.differentiable_cpow_mul_gammaFactor_inv
  have hUo : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hsubU : (({0, 1} : Set ℂ)ᶜ) ⊆ {1}ᶜ := fun s hs h1 => hs (Or.inr h1)
  have hΛ : DifferentiableOn ℂ χ.completedLFunction (({0, 1} : Set ℂ)ᶜ) := fun s hs =>
    (HeckeCharacter.differentiableAt_completedLFunction_of_forall (τ := 0) one_cpow
      (by simpa using fun h0 => hs (Or.inl h0)) (by simpa using fun h0 => hs (Or.inr h0))).differentiableWithinAt
  have hid : Set.EqOn g (fun s => h s * χ.completedLFunction s) (({0, 1} : Set ℂ)ᶜ) := by
    have a1 : AnalyticOnNhd ℂ g (({0, 1} : Set ℂ)ᶜ) := (hgd.mono hsubU).analyticOnNhd hUo
    have a2 : AnalyticOnNhd ℂ (fun s => h s * χ.completedLFunction s) (({0, 1} : Set ℂ)ᶜ) :=
      (hhd.differentiableOn.mul hΛ).analyticOnNhd hUo
    refine a1.eqOn_of_preconnected_of_eventuallyEq a2 isPreconnected_U (z₀ := 2) (by norm_num) ?_
    have hop : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hop.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
    rw [hgL s hs]
    exact χ.LFunction_eq_mul_completedLFunction hs
  set G : ℂ → ℂ := Function.update (fun s => (s - 1) * g s) 1 r with hG
  have hGne : ∀ s, s ≠ 1 → G s = (s - 1) * g s := fun s hs => Function.update_of_ne hs _ _
  refine ⟨G, ?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · rw [← differentiableOn_univ]
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem).1 ⟨?_, ?_⟩
    · refine DifferentiableOn.congr (f := fun s => (s - 1) * g s) ?_ fun z hz => hGne z hz.2
      exact ((differentiable_id.sub_const 1).differentiableOn).mul
        (hgd.mono fun z hz => hz.2)
    · rw [hG, continuousAt_update_same]
      simpa using hlim
  · have h1 : s ≠ 1 := fun h0 => by simp [h0] at hs
    rw [hGne s h1, hgL s hs]
  · have h1 : s ≠ 1 := fun h0 => by
      have := hs.2
      simp [h0] at this
    have h0 : s ≠ 0 := fun h0 => by
      have := hs.1
      simp [h0] at this
    have hU : s ∈ (({0, 1} : Set ℂ)ᶜ) := by
      simp [h0, h1]
    have hA : (χ.discrNormConductor : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'
    have hg0 := χ.gammaFactor_ne_zero hs.1
    rw [hGne s h1, hid hU]
    simp only [hh]
    rw [Complex.cpow_neg]
    have hX' : (χ.discrNormConductor : ℂ) ^ (s / 2) ≠ 0 := χ.discrNormConductor_cpow_ne_zero _
    field_simp
  · rw [hG, Function.update_self]
    exact hr

theorem cont_ne (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) (h1 : c ≠ 1) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s : ℂ, 1 < s.re → G s = (s - 1) * c.LFunction s) ∧
      (∀ s, Strip s → G s * (c.discrNormConductor : ℂ) ^ (s / 2) * c.gammaFactor s = (s - 1) * c.completedLFunction s) ∧
      G 1 = 0 ∧ deriv G 1 ≠ 0 := by
  have hn := not_cpow_of_ne c hc h1
  set g : ℂ → ℂ := fun s => (c.discrNormConductor : ℂ) ^ (-(s / 2)) * (c.gammaFactor s)⁻¹ * c.completedLFunction s with hg
  have hgd : Differentiable ℂ g := c.differentiable_cpow_mul_gammaFactor_inv.mul (c.differentiable_completedLFunction hn)
  have hgL : ∀ s : ℂ, 1 < s.re → g s = c.LFunction s := fun s hs => (c.LFunction_eq_mul_completedLFunction hs).symm
  have hd : HasDerivAt (fun s => (s - 1) * g s) (1 * g 1 + (1 - 1) * deriv g 1) 1 :=
    ((hasDerivAt_id' (1 : ℂ)).sub_const 1).fun_mul (hgd 1).hasDerivAt
  refine ⟨fun s => (s - 1) * g s, (differentiable_id.sub_const 1).mul hgd, fun s hs => by simp only [hgL s hs], fun s hs => ?_, by simp, ?_⟩
  · have hg0 := c.gammaFactor_ne_zero hs.1
    have hX' : (c.discrNormConductor : ℂ) ^ (s / 2) ≠ 0 := c.discrNormConductor_cpow_ne_zero _
    simp only [hg]
    rw [Complex.cpow_neg]
    field_simp
  · rw [hd.deriv, sub_self, zero_mul, add_zero, one_mul]
    exact c.continuation_ne_zero_of_one_le_re hn hgd hgL (by simp)

theorem cont (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s : ℂ, 1 < s.re → G s = (s - 1) * c.LFunction s) ∧
      (∀ s, Strip s → G s * (c.discrNormConductor : ℂ) ^ (s / 2) * c.gammaFactor s = (s - 1) * c.completedLFunction s) ∧
      (c = 1 → G 1 ≠ 0) ∧ (c ≠ 1 → G 1 = 0 ∧ deriv G 1 ≠ 0) := by
  by_cases h1 : c = 1
  · subst h1
    obtain ⟨G, a, b, d, e⟩ := cont_one
    exact ⟨G, a, b, d, fun _ => e, fun h => absurd rfl h⟩
  · obtain ⟨G, a, b, d, e⟩ := cont_ne c hc h1
    exact ⟨G, a, b, d, fun h => absurd h h1, fun _ => e⟩

theorem half (hE : E2) (hU : ∀ (c : HeckeCharacter ℚ) (v : Pl), IsUnit1 (localChar c v)) (c : HeckeCharacter ℚ) (S : Finset Pl)
    (hS : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) {s : ℂ} (hs : 1 < s.re) :
    c.LFunction s * ∏ v ∈ S, (localLFactor (localChar c v) s)⁻¹ = Lp c S s := by
  rw [euler hE c S hS hs, mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (lf_ne_zero (hU c v) (by linarith)), mul_one]

theorem fe_core (hψ : ∀ v, IsStd (localAdelicChar ℚ v)) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Pl)
    (hc : IsOfFinOrder c) (hsgn : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (hsgn' : ∀ w : InfinitePlace ℚ, (c⁻¹.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (hS : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) {G G' : ℂ → ℂ}
    (hG : ∀ s, Strip s → G s * (c.discrNormConductor : ℂ) ^ (s / 2) * c.gammaFactor s = (s - 1) * c.completedLFunction s)
    (hG' : ∀ s, Strip s → G' s * (c⁻¹.discrNormConductor : ℂ) ^ (s / 2) * c⁻¹.gammaFactor s =
      (s - 1) * c⁻¹.completedLFunction s) {s : ℂ} (hs : Strip s) :
    -s * G s * Complex.Gammaℝ (s + if δ then 1 else 0) = (s - 1) * ((if δ then -Complex.I else 1) *
      Complex.Gammaℝ (1 - s + if δ then 1 else 0)) *
      (∏ v ∈ S, localEpsilon (localChar c v) (localAdelicChar ℚ v) s) * G' (1 - s) := by
  have hs' : Strip (1 - s) := ⟨by simpa using hs.2, by simpa using hs.1⟩
  have h1 := hG s hs
  have h2 := hG' (1 - s) hs'
  have hfe : c.completedLFunction s = c.rootNumber * c⁻¹.completedLFunction (1 - s) := by
    refine c.completedLFunction_eq_rootNumber_mul fun τ hτ => ?_
    have h0 : τ = 0 := by
      rw [← HeckeCharacter.infiniteTau_of_forall hτ Rat.infinitePlace]
      exact tau_zero c hc _
    subst h0
    constructor
    · intro h
      have := hs.1
      simp [h] at this
    · intro h
      have := hs.2
      simp [h] at this
  rw [HeckeCharacter.discrNormConductor_inv, gammaFactor_eq c⁻¹ hc.inv δ hsgn'] at h2
  rw [gammaFactor_eq c hc δ hsgn] at h1
  rw [rootNumber_eq, weight_prod c δ hsgn] at hfe
  rw [prod_eps c S hψ hS s]
  set A : ℂ := (c.discrNormConductor : ℂ) with hA
  have hA0 : A ≠ 0 := Complex.ofReal_ne_zero.2 c.discrNormConductor_pos.ne'
  have hX : A ^ (s / 2) ≠ 0 := c.discrNormConductor_cpow_ne_zero _
  have hY : A ^ ((1 - s) / 2) = A ^ (s / 2) * A ^ (1 / 2 - s) := by
    rw [← Complex.cpow_add _ _ hA0]
    congr 1
    ring
  rw [hY] at h2
  rw [hfe] at h1
  refine mul_left_cancel₀ hX ?_
  set Pf := ∏ᶠ v, localEpsilon (localChar c v) (localAdelicChar ℚ v) (1 / 2)
  set D : ℂ := if δ then -Complex.I else 1
  set γ := Complex.Gammaℝ (s + if δ then 1 else 0)
  set γ' := Complex.Gammaℝ (1 - s + if δ then 1 else 0)
  linear_combination (-s) * h1 - (s - 1) * D * Pf * h2

theorem partial_functional_equation : B0 → E2 → H1 := by
  intro hB hE c δ S hc hsgn hS
  have hψ : ∀ v, IsStd (localAdelicChar ℚ v) := fun v => (hB.1 v).1
  have hU : ∀ (c : HeckeCharacter ℚ) (v : Pl), IsUnit1 (localChar c v) := fun c v => (hB.1 v).2.2.2.2.2.2 c
  have hsgn' : ∀ w : InfinitePlace ℚ, (c⁻¹.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1 := fun w => by
    have e : (((c⁻¹).infiniteComponent w (-1) : Circle) : ℂ) =
        (((c.infiniteComponent w (-1))⁻¹ : Circle) : ℂ) := rfl
    rw [e, Circle.coe_inv, hsgn w]
    split_ifs <;> simp
  have hS' : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v) := fun v hv => by
    rw [localChar_inv']
    exact isUnramifiedChar_inv_iff.2 (hS v hv)
  obtain ⟨G, hGd, hGL, hGS, hG1, hG2⟩ := cont c hc
  obtain ⟨G', hGd', hGL', hGS', -, -⟩ := cont c⁻¹ hc.inv
  have hEd : ∀ c : HeckeCharacter ℚ, Differentiable ℂ fun s => ∏ v ∈ S, (localLFactor (localChar c v) s)⁻¹ := fun c =>
    Differentiable.fun_finset_prod fun v _ => differentiable_lf_inv _
  have hE1 : ∏ v ∈ S, (localLFactor (localChar c v) 1)⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero (lf_ne_zero (hU c v) (by norm_num))
  refine ⟨fun s => G s * ∏ v ∈ S, (localLFactor (localChar c v) s)⁻¹,
    fun s => G' s * ∏ v ∈ S, (localLFactor (localChar c⁻¹ v) s)⁻¹, hGd.mul (hEd c), hGd'.mul (hEd c⁻¹), fun s hs => ⟨?_, ?_, ?_⟩,
    fun s hs => ?_, fun h => ?_, fun h => ?_⟩
  · simp only
    rw [hGL s hs, mul_assoc, half hE hU c S hS hs]
  · simp only
    rw [hGL' s hs, mul_assoc, half hE hU c⁻¹ S hS' hs]
  · simp only
    rw [hGL' s hs, mul_assoc, half hE hU c⁻¹ S hS' hs]
    have h1 : s - 1 ≠ 0 := fun h0 => by
      have : s = 1 := sub_eq_zero.1 h0
      simp [this] at hs
    refine mul_ne_zero h1 ?_
    rw [← half hE hU c⁻¹ S hS' hs]
    exact mul_ne_zero (c⁻¹.LFunction_ne_zero hs)
      (Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero (lf_ne_zero (hU c⁻¹ v) (by linarith)))
  · have hs' : Strip (1 - s) := ⟨by simpa using hs.2, by simpa using hs.1⟩
    have hcore := fe_core hψ c δ S hc hsgn hsgn' hS hGS hGS' hs
    simp only
    have hg : ∀ v ∈ S, gam (localAdelicChar ℚ v) (localChar c v) s =
        localEpsilon (localChar c v) (localAdelicChar ℚ v) s * localLFactor (localChar c⁻¹ v) (1 - s) *
          (localLFactor (localChar c v) s)⁻¹ := fun v _ => by
      rw [gam, div_eq_mul_inv, localChar_inv']
    rw [Finset.prod_congr rfl hg, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hQ : (∏ v ∈ S, localLFactor (localChar c⁻¹ v) (1 - s)) *
        ∏ v ∈ S, (localLFactor (localChar c⁻¹ v) (1 - s))⁻¹ = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (lf_ne_zero (hU c⁻¹ v) hs'.1)
    set P := ∏ v ∈ S, localEpsilon (localChar c v) (localAdelicChar ℚ v) s
    set Q := ∏ v ∈ S, localLFactor (localChar c⁻¹ v) (1 - s)
    set Q' := ∏ v ∈ S, (localLFactor (localChar c⁻¹ v) (1 - s))⁻¹
    set E := ∏ v ∈ S, (localLFactor (localChar c v) s)⁻¹
    set D : ℂ := (if δ then -Complex.I else 1) * Complex.Gammaℝ (1 - s + if δ then 1 else 0)
    linear_combination E * hcore - (s - 1) * D * P * E * G' (1 - s) * hQ
  · simp only
    exact mul_ne_zero (hG1 h) hE1
  · obtain ⟨h0, hd⟩ := hG2 h
    simp only
    refine ⟨by rw [h0, zero_mul], ?_⟩
    have e : deriv (fun s => G s * ∏ v ∈ S, (localLFactor (localChar c v) s)⁻¹) 1 =
        deriv G 1 * ∏ v ∈ S, (localLFactor (localChar c v) 1)⁻¹ := by
      have := ((hGd 1).hasDerivAt.fun_mul ((hEd c) 1).hasDerivAt).deriv
      rw [this, h0, zero_mul, add_zero]
    rw [e]
    exact mul_ne_zero hd hE1

end GlobalTheory.CompanionTheory.HeckePartial

end
