import Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic
import Formalism.PadicSubsetSums.StableGradedCounts.ZReuse
import Formalism.PadicSubsetSums.StableGradedCounts.ZCircleCharExtends
import Formalism.PadicSubsetSums.StableGradedCounts.FactorOverLocalSubalgebra
import Formalism.PadicSubsetSums.StableGradedCounts.CharpolyFactorAnnihilator
import Formalism.PadicSubsetSums.StableGradedCounts.ZGoodCuspidal
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt

open Polynomial Filter Topology

namespace Formalism.IrreducibleCountingLemmas.Z

theorem open_subgroup_continuous : OpenSubgroupContinuous := by
  intro A _ _ _ U χ hU hχ
  apply continuous_of_continuousAt_one
  have h1 : ContinuousAt (fun u : U => χ (u : A)) 1 := hχ.continuousAt
  have hemb : Topology.IsOpenEmbedding (Subtype.val : U → A) := hU.isOpenEmbedding_subtypeVal
  have := (hemb.continuousAt_iff (g := χ) (x := (1 : U))).1 h1
  simpa using this

theorem circle_character_extends_open : CircleCharExtendsOpen := by
  intro A _ _ _ U χ hU hχ
  obtain ⟨χ', h⟩ := circle_character_extends A U χ
  refine ⟨χ', open_subgroup_continuous A U χ' hU ?_, h⟩
  have : (fun u : U => χ' (u : A)) = χ := funext h
  rw [this]; exact hχ

theorem root_coefficient_formula : RootCoefficient := by
  intro m i; ring

theorem hull_bound_signed : HullBoundSigned := by
  intro r m x hr hx i
  have hrm : ((r : ℝ) - 1) / 2 = m := by rw [hr]; push_cast; ring
  rw [hrm]
  have hconv : Convex ℝ {y : Fin m → ℝ | |y i| ≤ (m : ℝ)} := by
    have h := (convex_Icc (-(m : ℝ)) (m : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
    have hset : {y : Fin m → ℝ | |y i| ≤ (m : ℝ)} =
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) ⁻¹' Set.Icc (-(m : ℝ)) (m : ℝ) := by
      ext y
      constructor
      · intro hy; exact abs_le.1 hy
      · intro hy; exact abs_le.2 hy
    rw [hset]; exact h
  refine convexHull_min ?_ hconv hx
  rintro _ ⟨⟨σ, ε⟩, rfl⟩
  have h1 : ((σ i : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (σ i).2.le
  have h0 : (0 : ℝ) ≤ ((σ i : ℕ) : ℝ) := Nat.cast_nonneg _
  show |(((ε i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((σ i : ℕ) : ℝ))| ≤ (m : ℝ)
  rw [abs_mul]
  have he : |(((ε i : ℤˣ) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
  rw [he, one_mul, abs_le]
  constructor <;> linarith

theorem inert_parameter_bound : InertParameterBound := by
  intro r m q x α hr hq hα hx β hβ
  have hb := hull_bound_signed r m x hr hx
  have hr0 : (0 : ℝ) ≤ ((r : ℝ) - 1) / 2 := by
    have : ((r : ℝ) - 1) / 2 = m := by rw [hr]; push_cast; ring
    rw [this]; exact Nat.cast_nonneg _
  simp only [Multiset.mem_add, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    Multiset.mem_singleton] at hβ
  rcases hβ with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · rw [hα]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (abs_le.1 (hb i)).2
  · rw [norm_inv, hα, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (by have := (abs_le.1 (hb i)).1; linarith)
  · rw [norm_one]
    exact Real.one_le_rpow hq.le hr0

theorem root_sum_unitary : RootSumUnitary := by
  intro m i
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  simp only [Finset.sum_apply]
  have h1 : ∀ a b : Fin m, (if a < b then
        (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) - Pi.single b 1) +
          (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) + Pi.single b 1) else (0 : Fin m → ℤ)) i =
      (if a = i then (if i < b then (4 : ℤ) else 0) else 0) := by
    intro a b
    by_cases hab : a < b
    · rw [if_pos hab]
      by_cases hai : a = i
      · rw [if_pos hai, ← hai, if_pos hab]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
        ring
      · rw [if_neg hai]
        have h0 : (Pi.single a 1 : Fin m → ℤ) i = 0 := Pi.single_eq_of_ne (Ne.symm hai) _
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, h0, smul_eq_mul]
        ring
    · rw [if_neg hab]
      by_cases hai : a = i
      · rw [if_pos hai, ← hai, if_neg hab]; rfl
      · rw [if_neg hai]; rfl
  have h3 : ∀ a : Fin m, ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ) +
        (1 : ℤ) • ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ))) i = if a = i then 4 else 0 := by
    intro a
    by_cases hai : a = i
    · rw [if_pos hai, ← hai]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      norm_num
    · rw [if_neg hai]
      have h0 : (Pi.single a 1 : Fin m → ℤ) i = 0 := Pi.single_eq_of_ne (Ne.symm hai) _
      simp only [Pi.add_apply, Pi.smul_apply, h0, smul_eq_mul]
      norm_num
  have h4 : ∀ a : Fin m, (∑ b : Fin m, if a = i then (if i < b then (4 : ℤ) else 0) else 0) =
      if a = i then ∑ b : Fin m, (if i < b then (4 : ℤ) else 0) else 0 := by
    intro a
    by_cases hai : a = i
    · simp only [if_pos hai]
    · simp only [if_neg hai, Finset.sum_const_zero]
  simp only [h1, h3, h4, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter, Finset.sum_const]
  have h5 : (Finset.univ.filter fun b : Fin m => i < b).card = m - 1 - i := by
    have : (Finset.univ.filter fun b : Fin m => i < b) = Finset.Ioi i := by ext; simp
    rw [this, Fin.card_Ioi]
  rw [h5]
  have := i.2
  simp only [nsmul_eq_mul]
  have h6 : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - i := by omega
  rw [h6]; ring

theorem cusp_value_count : CuspValueCount := by
  intro n p t lam c hpt hn hrun c₀
  have hcard : (Finset.univ.filter fun j : Fin n => lam j = c).card = t := by
    have : (Finset.univ.filter fun j : Fin n => lam j = c).map Fin.valEmbedding =
        Finset.Ico p (p+t) := by
      ext a
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact (hrun j).1 hj
      · intro h; exact ⟨⟨a, by omega⟩, (hrun _).2 h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]; omega
  by_cases h : c₀ = c
  · subst h; exact hcard.le
  · have hd : Disjoint (Finset.univ.filter fun j : Fin n => lam j = c₀)
        (Finset.univ.filter fun j : Fin n => lam j = c) := by
      rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h (h1.symm.trans h2)
    have := Finset.card_le_univ ((Finset.univ.filter fun j : Fin n => lam j = c₀) ∪
        (Finset.univ.filter fun j : Fin n => lam j = c))
    rw [Finset.card_union_of_disjoint hd, hcard, Fintype.card_fin] at this
    omega

theorem card_value_ne_run_le (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ) (hpt : p + t ≤ n)
    (hrun : ∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) (c₀ : ℤ) (h : c₀ ≠ c) :
    (Finset.univ.filter fun j => lam j = c₀).card ≤ n - t := by
  have hcard : (Finset.univ.filter fun j : Fin n => lam j = c).card = t := by
    have : (Finset.univ.filter fun j : Fin n => lam j = c).map Fin.valEmbedding =
        Finset.Ico p (p+t) := by
      ext a
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact (hrun j).1 hj
      · intro h; exact ⟨⟨a, by omega⟩, (hrun _).2 h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]; omega
  have hd : Disjoint (Finset.univ.filter fun j : Fin n => lam j = c₀)
      (Finset.univ.filter fun j : Fin n => lam j = c) := by
    rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h (h1.symm.trans h2)
  have := Finset.card_le_univ ((Finset.univ.filter fun j : Fin n => lam j = c₀) ∪
      (Finset.univ.filter fun j : Fin n => lam j = c))
  rw [Finset.card_union_of_disjoint hd, hcard, Fintype.card_fin] at this
  omega

theorem card_lt_add_card_gt_add_card_eq (n : ℕ) (lam : Fin n → ℤ) (c₀ : ℤ) :
    (Finset.univ.filter fun j => c₀ < lam j).card + (Finset.univ.filter fun j => lam j < c₀).card +
      (Finset.univ.filter fun j => lam j = c₀).card = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have : ∀ j : Fin n, ((if c₀ < lam j then 1 else 0) + (if lam j < c₀ then 1 else 0) +
      (if lam j = c₀ then 1 else 0) : ℕ) = 1 := by
    intro j; split_ifs <;> omega
  simp [this]

theorem cusp_value_count_dual : CuspValueCountDual := by
  intro n p t lam c hpt hn hrun c₀
  have h := cusp_value_count n p t lam c hpt hn hrun (-c₀)
  refine le_trans (le_of_eq ?_) h
  refine Finset.card_bij (fun j _ => Fin.rev j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  · intro a _ b _ hab; exact Fin.rev_injective hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨Fin.rev b, ?_, Fin.rev_rev b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.rev_rev]
    omega

theorem cusp_count_symmetric : CuspCountSym := by
  intro n p t lam c hpt hn hrun c₀ i hi h
  have := cusp_value_count n p t lam c hpt hn hrun c₀
  have := card_lt_add_card_gt_add_card_eq n lam c₀
  omega

theorem cusp_count_dual : CuspCountDual := by
  intro n p t lam c hpt hn hrun c₀ i hi ⟨h1, h2⟩
  exact cusp_count_symmetric n p t lam c hpt hn hrun c₀ i hi (by omega)

theorem cusp_centre_holds : CuspCentre := by
  intro n p t lam c hpt hn hrun c₀ h
  by_contra hc
  have := card_value_ne_run_le n p t lam c hpt hrun c₀ hc
  have := card_lt_add_card_gt_add_card_eq n lam c₀
  omega

theorem zero_count_range : ZCountRange := by
  intro K M N _ _ _ _ _ _ _ I Zg _ _ Ms Nx e θ hI hT hN hb
  classical
  have hmap : ∀ x, (Ms (e x)).map θ = Nx x := by
    intro x
    apply SetLike.coe_injective
    rw [Submodule.map_coe]
    exact (hb x).image_eq
  have hrange : LinearMap.range θ = ⨆ x, Nx x := by
    rw [LinearMap.range_eq_map, ← hT, Submodule.map_iSup,
      ← e.iSup_comp (g := fun s => (Ms s).map θ)]
    simp_rw [hmap]
  have hfr : ∀ x, Module.finrank K (Nx x) = Module.finrank K (Ms (e x)) := by
    intro x
    let φ : Ms (e x) →ₗ[K] Nx x := θ.restrict (fun m hm => (hb x).mapsTo hm)
    have hφ : Function.Bijective φ :=
      ⟨fun a b h => Subtype.ext ((hb x).injOn a.2 b.2 (congrArg Subtype.val h)), fun y => by
        obtain ⟨m, hm, h⟩ := (hb x).surjOn y.2
        exact ⟨⟨m, hm⟩, Subtype.ext h⟩⟩
    exact (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
  have hsumM : ∑ x, Module.finrank K (Nx x) = Module.finrank K M := by
    simp_rw [hfr]
    rw [Equiv.sum_comp e (fun s => Module.finrank K (Ms s))]
    have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hI hT
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Ms) hint).finrank_eq,
      Module.finrank_directSum]
  have hsumR : Module.finrank K (LinearMap.range θ) = ∑ x, Module.finrank K (Nx x) := by
    have hinjΨ : Function.Injective (DirectSum.coeLinearMap Nx) := hN.dfinsupp_lsum_injective
    rw [hrange, ← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinjΨ,
      Module.finrank_directSum]
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot]
    have h := LinearMap.finrank_range_add_finrank_ker θ
    rw [hsumR, hsumM] at h
    exact Submodule.finrank_eq_zero.1 (by omega)
  exact ⟨hinj, hrange, hsumR, hsumR.trans hsumM⟩

theorem norm_inert_cpow_eq (q : ℝ) (s : ℂ) (hq : 2 ≤ q) :
    ‖((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ = q ^ (-2 * s.re) := by
  have hq0 : 0 < q := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rw [← Real.rpow_natCast q 2, ← Real.rpow_mul hq0.le]
  congr 1
  simp

theorem rpow_neg_two_mul_le_half (q σ : ℝ) (hq : 2 ≤ q) (hσ : 1 / 2 < σ) : q ^ (-2 * σ) ≤ 1 / 2 := by
  have hq0 : 0 < q := by linarith
  calc q ^ (-2 * σ) ≤ q ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = q⁻¹ := Real.rpow_neg_one q
    _ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) hq

theorem half_le_norm_inert_denominator (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1) (hs : 1 / 2 < s.re) :
    1 / 2 ≤ ‖1 - ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ := by
  have h1 : ‖ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul, hch, one_mul, norm_inert_cpow_eq q s hq]; exact rpow_neg_two_mul_le_half q _ hq hs
  have h2 := norm_sub_norm_le (1 : ℂ) (ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s))
  rw [norm_one] at h2
  linarith

theorem inertFactor_sub_one_le (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1)
    (hs : 1 / 2 < s.re) : ‖inertFactor q ch s - 1‖ ≤ 4 * q ^ (-2 * s.re) := by
  have hd := half_le_norm_inert_denominator q ch s hq hch hs
  set u := ((q ^ 2 : ℝ) : ℂ) ^ (-s) with hu
  have hd0 : (1 - ch * u) ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; linarith
  have e : inertFactor q ch s - 1 = (ch - 1) * u / (1 - ch * u) := by
    unfold inertFactor
    rw [← hu, div_sub_one hd0]
    congr 1
    ring
  rw [e, norm_div, norm_mul, hu, norm_inert_cpow_eq q s hq, ← hu]
  have h2 : ‖ch - 1‖ ≤ 2 := by
    have := norm_sub_le ch 1
    rw [hch, norm_one] at this; linarith
  have hp : 0 ≤ q ^ (-2 * s.re) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ (by linarith)]
  calc ‖ch - 1‖ * q ^ (-2 * s.re) ≤ 2 * q ^ (-2 * s.re) := mul_le_mul_of_nonneg_right h2 hp
    _ = 4 * q ^ (-2 * s.re) * (1 / 2) := by ring
    _ ≤ 4 * q ^ (-2 * s.re) * ‖1 - ch * u‖ := mul_le_mul_of_nonneg_left hd (by positivity)

theorem inertFactor_ne_zero (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1)
    (hs : 1 / 2 < s.re) : inertFactor q ch s ≠ 0 := by
  have hd := half_le_norm_inert_denominator q ch s hq hch hs
  have hn := half_le_norm_inert_denominator q 1 s hq norm_one hs
  rw [one_mul] at hn
  unfold inertFactor
  apply div_ne_zero
  · intro h; rw [h, norm_zero] at hn; linarith
  · intro h; rw [h, norm_zero] at hd; linarith

theorem inert_euler_quotient : InertEulerQuotient := by
  intro ι q ch s hq hch hs hsum
  have hS : Summable (fun v => ‖inertFactor (q v) (ch v) s - 1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun v => inertFactor_sub_one_le (q v) (ch v) s (hq v) (hch v) hs) (hsum.mul_left 4)
  have e : (fun v => inertFactor (q v) (ch v) s) =
      fun v => 1 + (inertFactor (q v) (ch v) s - 1) := by
    funext v; ring
  refine ⟨hS, ?_, ?_⟩
  · rw [e]; exact multipliable_one_add_of_summable hS
  · rw [e]
    refine tprod_one_add_ne_zero_of_summable (fun v => ?_) hS
    rw [add_sub_cancel]
    exact inertFactor_ne_zero (q v) (ch v) s (hq v) (hch v) hs

theorem pole_transfer_holds : PoleTransfer := by
  intro L Z R hR hR1 hL hZ
  have h1 : Tendsto (fun s => ‖R s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) (𝓝 ‖R 1‖) :=
    (hR.norm).tendsto.mono_left nhdsWithin_le_nhds
  have h2 := hZ.atTop_mul_pos (norm_pos_iff.2 hR1) h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hL s hs, norm_mul]

theorem run_jumps_holds : RunJumps := by
  intro n p t a c ha ht hpt hrun
  have hp : p < n := by omega
  have hc : a ⟨p, hp⟩ = c := (hrun ⟨p, hp⟩).2 ⟨le_refl _, by simp; omega⟩
  have hlow : ∀ j : Fin n, (j : ℕ) < p → c + 1 ≤ a j := by
    intro j hj
    have h1 : a ⟨p, hp⟩ ≤ a j := ha (by rw [Fin.le_def]; simp; omega)
    have h2 : a j ≠ c := fun h => by have := (hrun j).1 h; omega
    omega
  have hhigh : ∀ j : Fin n, p + t ≤ (j : ℕ) → a j ≤ c - 1 := by
    intro j hj
    have h1 : a j ≤ a ⟨p, hp⟩ := ha (by rw [Fin.le_def]; simp; omega)
    have h2 : a j ≠ c := fun h => by have := (hrun j).1 h; omega
    omega
  have hmid : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) < p + t → a j = c := fun j h1 h2 =>
    (hrun j).2 ⟨h1, h2⟩
  refine ⟨fun j => ?_, fun k hk => ?_, fun j => ?_⟩
  · rcases lt_or_ge (j : ℕ) p with h | h
    · have := hlow j h
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro ⟨h1, h2⟩; omega
    · rcases lt_or_ge (j : ℕ) (p + t) with h' | h'
      · have := hmid j h h'
        constructor
        · intro _; exact ⟨h, h'⟩
        · intro _; constructor <;> omega
      · have := hhigh j h'
        constructor
        · rintro ⟨h1, h2⟩; omega
        · rintro ⟨h1, h2⟩; omega
  · refine ⟨⟨p + k, by omega⟩, ?_⟩
    have := hmid ⟨p + k, by omega⟩ (by simp) (by simp; omega)
    rw [this]; push_cast; ring
  · rcases lt_or_ge (j : ℕ) p with h | h
    · have := hlow j h
      constructor <;> omega
    · rcases lt_or_ge (j : ℕ) (p + t) with h' | h'
      · have := hmid j h h'
        constructor <;> omega
      · have := hhigh j h'
        constructor <;> omega

theorem block_is_run : BlockIsRun := by
  intro n p t a c w ha hpt hn hrun hblock
  have ht : 1 ≤ t := by omega
  have hs : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → (i : ℤ) - a i < (j : ℤ) - a j := by
    intro i j hij
    have h1 : a j ≤ a i := ha (by rw [Fin.le_def]; omega)
    omega
  obtain ⟨j0, hj0⟩ := hblock 0 (by omega)
  have hind : ∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℕ) = (j0 : ℕ) + k ∧ (j : ℤ) - a j = w + k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨j0, by simp, hj0⟩
    | succ k ih =>
      intro hk
      obtain ⟨j, hj, hjw⟩ := ih (by omega)
      obtain ⟨j', hj'⟩ := hblock (k + 1) hk
      push_cast at hj'
      have h1 : (j : ℕ) < (j' : ℕ) := by
        by_contra hcon
        rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with h | h
        · have := hs j' j h; omega
        · have : j' = j := Fin.ext (by omega)
          rw [this] at hj'; omega
      have h2 : (j' : ℕ) = (j : ℕ) + 1 := by
        by_contra hcon
        have hlt : (j : ℕ) + 1 < (j' : ℕ) := by omega
        have hb : (j : ℕ) + 1 < n := by have := j'.2; omega
        have e1 := hs j ⟨(j : ℕ) + 1, hb⟩ (by simp)
        have e2 := hs ⟨(j : ℕ) + 1, hb⟩ j' (by simpa using hlt)
        omega
      refine ⟨j', by omega, ?_⟩
      push_cast; omega
  have hval : ∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℕ) = (j0 : ℕ) + k ∧ a j = (j0 : ℤ) - w := by
    intro k hk
    obtain ⟨j, hj, hjw⟩ := hind k hk
    refine ⟨j, hj, ?_⟩
    have : (j : ℤ) = (j0 : ℤ) + k := by exact_mod_cast hj
    omega
  obtain ⟨jl, hjl, hal⟩ := hval (t - 1) (by omega)
  have hjln := jl.2
  have ha0 : a j0 = (j0 : ℤ) - w := by
    obtain ⟨j, hj, h⟩ := hval 0 (by omega)
    have : j = j0 := Fin.ext (by omega)
    rw [← this]; rw [this] at h ⊢; exact h
  have hc : (j0 : ℤ) - w = c := by
    rcases Nat.lt_or_ge p (j0 : ℕ) with h | h
    · have := (hrun j0).2 ⟨by omega, by omega⟩
      omega
    · obtain ⟨j, hj, hv⟩ := hval (p - j0) (by omega)
      have := (hrun j).2 ⟨by omega, by omega⟩
      omega
  have r0 := (hrun j0).1 (by omega)
  have rl := (hrun jl).1 (by omega)
  have hj0p : (j0 : ℕ) = p := by omega
  have hw : w = (p : ℤ) - c := by
    have : (j0 : ℤ) = (p : ℤ) := by exact_mod_cast hj0p
    omega
  refine ⟨hw, ?_⟩
  rw [hw]
  exact (run_jumps_holds n p t a c ha ht hpt hrun).1

theorem inertFactor_differentiableAt (q : ℝ) (ch s : ℂ) (hq : 2 ≤ q) (hch : ‖ch‖ = 1)
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (fun z => inertFactor q ch z) s := by
  have hc : ((q ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < q ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hu : DifferentiableAt ℂ (fun z : ℂ => ((q ^ 2 : ℝ) : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hc)
  unfold inertFactor
  refine ((differentiableAt_const _).sub hu).div
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul hu)) ?_
  intro h
  have := half_le_norm_inert_denominator q ch s hq hch hs
  rw [h, norm_zero] at this
  linarith

theorem inert_euler_holomorphic : InertEulerHolomorphic := by
  intro ι q ch hq hch hsum s hs
  have hs : 1 / 2 < s.re := hs
  obtain ⟨σ₀, h1, h2⟩ : ∃ σ₀ : ℝ, 1 / 2 < σ₀ ∧ σ₀ < s.re := exists_between hs
  let K : Set ℂ := {z | σ₀ < z.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hKd : ∀ v, DifferentiableOn ℂ (fun z => inertFactor (q v) (ch v) z) K := fun v z hz =>
    (inertFactor_differentiableAt (q v) (ch v) z (hq v) (hch v)
      (lt_trans h1 hz)).differentiableWithinAt
  have hprod := ((hsum σ₀ h1).mul_left 4).hasProdLocallyUniformlyOn_one_add
    (f := fun v z => inertFactor (q v) (ch v) z - 1) hK
    (.of_forall fun v z hz => by
      have hz' : σ₀ < z.re := hz
      refine (inertFactor_sub_one_le (q v) (ch v) z (hq v) (hch v) (lt_trans h1 hz')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hq v]) (by linarith))
    (fun v => ((hKd v).sub (differentiableOn_const _)).continuousOn)
  have hd : DifferentiableOn ℂ (fun z => ∏' v, (1 + (inertFactor (q v) (ch v) z - 1))) K :=
    hprod.differentiableOn (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun v _ => hKd v)) hK
  have h3 := hd.differentiableAt (hK.mem_nhds h2)
  simp only [add_sub_cancel] at h3
  exact h3.differentiableWithinAt

theorem semisimple_quotient_simple : SemisimpleQuotientSimple := by
  intro R M Q _ _ _ _ _ _ _ π huniq hπ
  have hco : ∀ C : Submodule R Q, IsCoatom C → IsCoatom (C.comap π) := by
    intro C hC
    refine ⟨?_, ?_⟩
    · intro h
      apply hC.1
      have := congrArg (Submodule.map π) h
      rwa [Submodule.map_comap_eq_of_surjective hπ, Submodule.map_top, LinearMap.range_eq_top.2 hπ]
        at this
    · intro b hb
      have hker : LinearMap.ker π ≤ b := le_trans (LinearMap.ker_le_comap π) hb.le
      have hbb : (b.map π).comap π = b := by
        rw [Submodule.comap_map_eq, sup_eq_left.2 hker]
      have hle : C ≤ b.map π := by
        have := Submodule.map_mono (f := π) hb.le
        rwa [Submodule.map_comap_eq_of_surjective hπ] at this
      have hne : C ≠ b.map π := by
        intro h
        rw [h, hbb] at hb
        exact lt_irrefl _ hb
      have htop := hC.2 _ (lt_of_le_of_ne hle hne)
      rw [← hbb, htop, Submodule.comap_top]
  have hone : ∀ C C' : Submodule R Q, IsCoatom C → IsCoatom C' → C = C' := by
    intro C C' hC hC'
    exact Submodule.comap_injective_of_surjective hπ (huniq _ _ (hco C hC) (hco C' hC'))
  rw [isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  obtain ⟨N', hN'⟩ := exists_isCompl N
  have hN'top : N' ≠ ⊤ := by
    intro h
    apply hbot
    have := hN'.inf_eq_bot
    rwa [h, inf_top_eq] at this
  obtain ⟨C, hC, hNC⟩ := (eq_top_or_exists_le_coatom N).resolve_left htop
  obtain ⟨C', hC', hNC'⟩ := (eq_top_or_exists_le_coatom N').resolve_left hN'top
  have := hone C C' hC hC'
  subst this
  apply hC.1
  rw [eq_top_iff, ← hN'.sup_eq_top]
  exact sup_le hNC hNC'

theorem charpolyRev_map_alt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [h]

theorem third_reduction_holds : ResidueCharpolyEq := by
  intro O _ _ X' _ T hT G n r hr x y g
  have h1 : Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
      Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) := by
    rw [charpolyRev_map_alt, charpolyRev_map_alt]
    ext j
    rw [coeff_map, coeff_map]
    exact same_residue_holds O X' T hT _ (hr g j) x y
  refine ⟨h1, ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      M.charpoly = (Matrix.charpolyRev M).reflect n := by
    intro M
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, reflect_reflect]
  rw [key, key, h1]

theorem eval_algebraMap_eq {O X' : Type} [CommRing O] (T : Subalgebra O (X' → O)) (x : X') (c : O) :
    ev T x (algebraMap O T c) = c := by
  simp [ev]

theorem nonempty_of_local_subalgebra {O X' : Type} [CommRing O] (T : Subalgebra O (X' → O)) [IsLocalRing T] :
    Nonempty X' := by
  by_contra h
  have : IsEmpty X' := not_nonempty_iff.1 h
  exact zero_ne_one (α := T) (Subtype.ext (funext fun x => isEmptyElim x))

theorem monic_of_eval_monic {O X' : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X' → O))
    [IsLocalRing T] (p : T[X]) (h : ∀ x, (p.map (ev T x)).Monic) : p.Monic := by
  obtain ⟨x₀⟩ := nonempty_of_local_subalgebra T
  have hp0 : p ≠ 0 := by
    intro h0
    have := h x₀
    rw [h0, Polynomial.map_zero] at this
    exact this.ne_zero rfl
  have ha0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hval : ∀ x, ev T x p.leadingCoeff = 1 ∨ ev T x p.leadingCoeff = 0 := by
    intro x
    have hle : (p.map (ev T x)).natDegree ≤ p.natDegree := natDegree_map_le
    have hc : ev T x p.leadingCoeff = (p.map (ev T x)).coeff p.natDegree := by
      rw [coeff_map]; rfl
    rcases hle.eq_or_lt with he | hl
    · left
      rw [hc, ← he]; exact h x
    · right
      rw [hc]; exact coeff_eq_zero_of_natDegree_lt hl
  have hidem : p.leadingCoeff * (1 - p.leadingCoeff) = 0 := by
    apply Subtype.ext
    funext x
    have : ev T x (p.leadingCoeff * (1 - p.leadingCoeff)) = 0 := by
      rw [map_mul, map_sub, map_one]
      rcases hval x with h1 | h1 <;> rw [h1] <;> simp
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p.leadingCoeff with hu | hu
  · have := (hu.mul_right_eq_zero).1 hidem
    exact (sub_eq_zero.1 this).symm
  · exact absurd ((hu.mul_left_eq_zero).1 hidem) ha0

theorem fifth_factor_monic : FactorOverLocalSubalgebraMonic := by
  intro O _ _ X' _ T hT t c F s hF h1 h2
  obtain ⟨P, hP1, hP2, hP3⟩ := factorOverLocalSubalgebra O X' T hT t c F s h1 h2
  refine ⟨P, ?_, hP1, hP2, hP3⟩
  rw [hP1] at hF
  exact Monic.of_mul_monic_right ((monic_X_sub_C _).pow t) hF

theorem charpoly_smul_id {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    [FiniteDimensional K B] (c : K) :
    (c • (LinearMap.id : B →ₗ[K] B)).charpoly = (X - C c) ^ Module.finrank K B := by
  rw [LinearMap.charpoly_def, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal,
    Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
    Module.finrank_eq_card_chooseBasisIndex]

theorem charpoly_eq_restrict_mul_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ : Module.End K V) (c : K) (hAB : IsCompl A B)
    (hA0 : ∀ v ∈ A, γ₀ v ∈ A) (hB0 : ∀ v ∈ B, γ₀ v = c • v) :
    γ₀.charpoly = (γ₀.restrict hA0).charpoly * (X - C c) ^ Module.finrank K B := by
  have hconj : (Submodule.prodEquivOfIsCompl A B hAB).conj
      ((γ₀.restrict hA0).prodMap (c • (LinearMap.id : B →ₗ[K] B))) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simp [Submodule.coe_prodEquivOfIsCompl', hB0 b b.2]
  rw [← charpoly_smul_id, ← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj
    (Submodule.prodEquivOfIsCompl A B hAB), hconj]

theorem fifth_assembly_second : FactorAnnihilatorFamily := by
  intro O K _ _ _ _ hinj X' _ T hT V _ _ _ A B γ₀ γ c cγ t F hF hAB hA0 hA hB0 hB hfr hmult
  have := hT
  have hDm : ((X - C c : O[X]) ^ t).Monic := (monic_X_sub_C _).pow t
  have hDK : ((X - C c : O[X]) ^ t).map (algebraMap O K) = (X - C (algebraMap O K c)) ^ t := by
    rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  have hsplit : ∀ x, (γ₀ x).charpoly =
      ((γ₀ x).restrict (hA0 x)).charpoly * (X - C (algebraMap O K c)) ^ t := by
    intro x
    have := charpoly_eq_restrict_mul_scalar (A x) (B x) (γ₀ x) (algebraMap O K c) (hAB x) (hA0 x) (hB0 x)
    rwa [hfr x] at this
  have hFx : ∀ x, F.map (ev T x) = (F.map (ev T x) /ₘ (X - C c) ^ t) * (X - C c) ^ t := by
    intro x
    have hrem : F.map (ev T x) %ₘ (X - C c) ^ t = 0 := by
      apply Polynomial.map_injective _ hinj
      rw [map_modByMonic _ hDm, hDK, hF x, hsplit x, Polynomial.map_zero]
      exact (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C _).pow t)).2 (dvd_mul_left _ _)
    have := modByMonic_add_div (F.map (ev T x)) ((X - C c) ^ t)
    rw [hrem, zero_add] at this
    rw [mul_comm]; exact this.symm
  have hFm : ∀ x, (F.map (ev T x)).Monic := by
    intro x
    apply monic_of_injective hinj
    rw [hF x]; exact LinearMap.charpoly_monic _
  have hsm : ∀ x, (F.map (ev T x) /ₘ (X - C c) ^ t).Monic := by
    intro x
    have := hFm x
    rw [hFx x] at this
    exact Monic.of_mul_monic_right hDm this
  have hunit : ∀ x, IsUnit ((F.map (ev T x) /ₘ (X - C c) ^ t).eval c) := by
    intro x
    apply g5b_multiplicity_holds O t c _ (hsm x)
    rw [← hFx x]; exact hmult x
  obtain ⟨P, hPm, hP1, hP2, hP3⟩ := fifth_factor_monic O X' T hT t c F
    (fun x => F.map (ev T x) /ₘ (X - C c) ^ t) (monic_of_eval_monic T F hFm) hFx hunit
  refine ⟨P, hPm, hP1, hP2, fun x => ?_⟩
  apply charpolyFactorAnnihilator K (V x) (A x) (B x) (γ₀ x) (γ x) (algebraMap O K c) (algebraMap O K cγ) t _
    (hAB x) (hA0 x) (hA x) (hB0 x) (hB x) (hfr x)
  rw [hP3 x, ← hF x, ← hDK, ← Polynomial.map_mul, ← hFx x]

theorem good_cuspidal_multiplicity_one : GoodCuspidalOne := by
  intro k _ P _ r f I _ n d h hr hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨hd, hcard⟩ := goodCuspidal_holds k P r f I n d h hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨v₀⟩ := ‹Nonempty P›
  have hne : Nonempty I := by
    by_contra hemp
    have : IsEmpty I := not_nonempty_iff.1 hemp
    have := hdeg v₀
    rw [hprod v₀, Finset.univ_eq_empty, Finset.prod_empty, natDegree_one] at this
    omega
  have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.1 hcard
  refine ⟨le_antisymm hcard (Fintype.card_pos_iff.2 hne), fun i => ⟨hd i, ?_⟩⟩
  have := hdeg v₀
  rw [hprod v₀, Fintype.prod_subsingleton _ i, hd i, pow_one, hn] at this
  exact this

theorem first_charpoly_in_T : CharpolyOverSubalgebra := by
  intro O _ _ X' _ T n M h
  have hdeg : ∀ x, (M x).charpoly.natDegree = n := fun x => by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hco : ∀ (x : X') (j : ℕ), j ≤ n →
      (M x).charpoly.coeff j = (Matrix.charpolyRev (M x)).coeff (n - j) := by
    intro x j hj
    rw [← Matrix.reverse_charpoly, coeff_reverse, hdeg, revAt_le (Nat.sub_le n j),
      Nat.sub_sub_self hj]
  have hmem : ∀ j : ℕ, (fun x => (M x).charpoly.coeff j) ∈ T := by
    intro j
    by_cases hj : j ≤ n
    · have : (fun x => (M x).charpoly.coeff j) =
          fun x => (Matrix.charpolyRev (M x)).coeff (n - j) := funext fun x => hco x j hj
      rw [this]; exact h _
    · have : (fun x => (M x).charpoly.coeff j) = 0 := funext fun x =>
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [this]; exact T.zero_mem
  let F : T[X] := ∑ j ∈ Finset.range (n + 1), C (⟨_, hmem j⟩ : T) * X ^ j
  have hFc : ∀ j, F.coeff j = if j ≤ n then (⟨_, hmem j⟩ : T) else 0 := by
    intro j
    simp only [F, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp
  refine ⟨F, ?_, fun x => ?_⟩
  · apply monic_of_natDegree_le_of_coeff_eq_one n
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hFc, if_neg (by omega)]
    · rw [hFc, if_pos le_rfl]
      apply Subtype.ext
      funext x
      have := (Matrix.charpoly_monic (M x)).coeff_natDegree
      rw [hdeg] at this
      exact this
  · ext j
    rw [coeff_map, hFc]
    by_cases hj : j ≤ n
    · rw [if_pos hj]; rfl
    · rw [if_neg hj, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)).symm

theorem brauer_nesbitt_char_zero : BrauerNesbittCharZero :=
  fun k _ _ G _ V W _ _ _ _ _ _ ρ τ => brauer_nesbitt k G V W ρ τ

theorem brauer_nesbitt_finite_group : BrauerNesbittFinite :=
  fun k _ _ G _ V W _ _ _ _ _ _ ρ τ => brauer_nesbitt k G V W ρ τ

end Formalism.IrreducibleCountingLemmas.Z
