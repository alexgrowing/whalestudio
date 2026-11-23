import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Filter Topology Pointwise

namespace GlobalTheory.LimCocycle

theorem eventually_smul_mem {LL W : Type} [Field LL] [TopologicalSpace LL] [AddCommGroup W] [Module LL W]
    [TopologicalSpace W] [ContinuousSMul LL W] (c : ℕ → LL) (hc : Tendsto c atTop (𝓝 0))
    {K : Set W} (hK : IsCompact K) {U : Set W} (hU : U ∈ 𝓝 (0 : W)) :
    ∀ᶠ m in atTop, ∀ y ∈ K, c m • y ∈ U := by
  have h : ∀ᶠ a in 𝓝 (0 : LL), ∀ y ∈ K, a • y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have := (continuous_fst.smul continuous_snd : Continuous fun p : LL × W => p.1 • p.2).tendsto ((0 : LL), y)
    exact this.eventually_mem (by simpa using hU)
  exact hc.eventually h

theorem isCompact_of_fg {O LL V : Type} [CommRing O] [Field LL] [Algebra O LL] [TopologicalSpace LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    (hc : IsCompact (Set.range (algebraMap O LL))) (T : Submodule O V) (hT : T.FG) :
    IsCompact (T : Set V) := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hT
  have heq : (T : Set V) = (fun c : Fin n → LL => ∑ i, c i • s i) ''
      (Set.univ.pi fun _ => Set.range (algebraMap O LL)) := by
    ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, ← hs] at hx
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
      refine ⟨fun i => algebraMap O LL (a i), fun i _ => ⟨a i, rfl⟩, ?_⟩
      simp only [algebraMap_smul]
      exact ha
    · rintro ⟨c, hc', rfl⟩
      have : ∀ i, ∃ a : O, algebraMap O LL a = c i := fun i => hc' i (Set.mem_univ i)
      choose a ha using this
      rw [SetLike.mem_coe, ← hs]
      have : (∑ i, c i • s i) = ∑ i, a i • s i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← ha i, algebraMap_smul]
      show ∑ i, c i • s i ∈ _
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [heq]
  exact (isCompact_univ_pi fun _ => hc).image
    (continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const)

end GlobalTheory.LimCocycle

namespace GlobalTheory.LimCocycle

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ hI w hw hstep
  have hcO : IsCompact (Set.range (algebraMap O LL)) := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  haveI := hmod
  haveI := htop
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  haveI : T2Space LL := by
    let e := (Module.finBasis ℚ_[l] LL).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
  haveI : T2Space A.V := by
    let e := (Module.finBasis LL A.V).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)

  have hlpr : l.Prime := Fact.out
  let c : ℕ → LL := fun m => algebraMap O LL (((l : ℕ) : O) ^ m)
  have hc : Tendsto c atTop (𝓝 0) := by
    have hcont : Continuous (algebraMap ℚ_[l] LL) := by
      have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun a => a • (1 : LL) :=
        funext Algebra.algebraMap_eq_smul_one
      rw [h]
      exact continuous_id.smul continuous_const
    have h1 := (hcont.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := l)))
    rw [map_zero] at h1
    refine h1.congr (fun m => ?_)
    simp [c, Function.comp, map_pow, map_natCast]

  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap ℚ_[l] LL),
      map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective, Nat.cast_eq_zero] at h2
    exact hlpr.ne_zero h2
  have hlnu : ¬ IsUnit ((l : ℕ) : O) := by
    intro hu
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have hU : ({1}ᶜ : Set LL) ∈ 𝓝 (0 : LL) := isOpen_compl_singleton.mem_nhds (by simp)
    obtain ⟨m, hm⟩ := (eventually_smul_mem c hc hcO hU).exists
    apply hm (algebraMap O LL (a ^ m)) ⟨_, rfl⟩
    simp only [c, smul_eq_mul, ← map_mul, ← mul_pow, ha, one_pow, map_one, Set.mem_singleton_iff]
  obtain ⟨v, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ

  let Q : ℕ → Submodule O A.V := fun n => ϖ ^ n • LA.T
  have hQT : ∀ n, Q n ≤ LA.T := by
    intro n x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact LA.T.smul_mem _ hy
  have hQmono : ∀ m n, m ≤ n → Q n ≤ Q m := by
    intro m n hmn x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨ϖ ^ (n - m) • y, LA.T.smul_mem _ hy, ?_⟩
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
  have hmem : ∀ n (t : ↥LA.T), t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) ↔ (t : A.V) ∈ Q n := by
    intro n t
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, hb⟩
      exact ⟨b, b.2, by rw [← hb]; rfl⟩
    · rintro ⟨b, hbT, hb⟩
      exact ⟨⟨b, hbT⟩, trivial, Subtype.ext hb⟩
  have hTc : IsCompact (LA.T : Set A.V) := isCompact_of_fg hcO LA.T LA.fg
  have hQc : ∀ n, IsCompact (Q n : Set A.V) := by
    intro n
    have h : (Q n : Set A.V) = (fun x => algebraMap O LL (ϖ ^ n) • x) '' (LA.T : Set A.V) := by
      simp only [Q, Submodule.coe_pointwise_smul, algebraMap_smul]
      rfl
    rw [h]
    exact hTc.image (continuous_const_smul _)
  have hQρ : ∀ n g, ∀ x ∈ Q n, A.ρ g x ∈ Q n := by
    intro n g x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨A.ρ g y, LA.stable g y hy, ?_⟩
    rw [LinearMap.map_smul_of_tower]

  have hshrink : ∀ U ∈ 𝓝 (0 : A.V), ∃ N, ∀ x ∈ Q N, x ∈ U := by
    intro U hU
    obtain ⟨M, hM⟩ := (eventually_smul_mem c hc hTc hU).exists
    refine ⟨v * M, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    have hpow : ϖ ^ (v * M) = ((l : ℕ) : O) ^ M * (↑u⁻¹ : O) ^ M := by
      rw [← mul_pow, hlu, pow_mul, mul_comm (↑u : O), mul_assoc, Units.mul_inv, mul_one]
    have h := hM (((↑u⁻¹ : O) ^ M) • y) (LA.T.smul_mem _ hy)
    rw [hpow, mul_smul]
    simpa only [c, algebraMap_smul] using h
  have hsep : ∀ x : A.V, (∀ n, x ∈ Q n) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨N, hN⟩ := hshrink {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    exact hN x (hx N) rfl

  have hlim : ∀ g, ∃ x : A.V, ∀ n, x - (w n g : A.V) ∈ Q n := by
    intro g
    let C : ℕ → Set A.V := fun n => (fun x => x - (w n g : A.V)) ⁻¹' (Q n : Set A.V)
    have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n x hx => by
        have h1 : x - (w (n + 1) g : A.V) ∈ Q n := hQmono n (n + 1) (Nat.le_succ n) hx
        have h2 : ((w (n + 1) g : A.V) - (w n g : A.V)) ∈ Q n := by
          have := (hmem n _).1 (hstep n g)
          simpa using this
        show x - (w n g : A.V) ∈ Q n
        have := (Q n).add_mem h1 h2
        simpa using this)
      (fun n => ⟨w n g, by simp [C]⟩)
      (by
        have : C 0 = (Homeomorph.subRight (w 0 g : A.V)) ⁻¹' (Q 0 : Set A.V) := rfl
        rw [this]
        exact (Homeomorph.subRight (w 0 g : A.V)).isCompact_preimage.2 (hQc 0))
      (fun n => (hQc n).isClosed.preimage (continuous_sub_right _))
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, fun n => Set.mem_iInter.1 hx n⟩
  choose d hd using hlim
  have hdT : ∀ g, d g ∈ LA.T := by
    intro g
    have := LA.T.add_mem (hQT 0 (hd g 0)) (w 0 g).2
    simpa using this

  have hcocn : ∀ n g h, (w n (g * h) : A.V) - w n g - A.ρ g (w n h) ∈ Q n := by
    intro n g h
    have h1 := (hw n).2 g h
    simp only [actQ, Submodule.mapQ_apply] at h1
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at h1
    have := (hmem n _).1 h1
    simp only [Submodule.coe_sub, Submodule.coe_add] at this
    rw [sub_sub]
    exact this
  have hcoc : ∀ g h, d (g * h) = d g + A.ρ g (d h) := by
    intro g h
    have : d (g * h) - d g - A.ρ g (d h) = 0 := by
      refine hsep _ (fun n => ?_)
      have e : d (g * h) - d g - A.ρ g (d h) = (d (g * h) - w n (g * h)) - (d g - w n g)
          - A.ρ g (d h - w n h) + ((w n (g * h) : A.V) - w n g - A.ρ g (w n h)) := by
        rw [map_sub]; abel
      rw [e]
      exact (Q n).add_mem ((Q n).sub_mem ((Q n).sub_mem (hd _ n) (hd g n)) (hQρ n g _ (hd h n)))
        (hcocn n g h)
    exact sub_eq_zero.1 (by rw [← sub_sub]; exact this)

  have hcont : Continuous d := by
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
    intro U hU
    obtain ⟨N, hN⟩ := hshrink U hU
    have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hw N).1 g₀
    refine Filter.mem_map.2 ?_
    filter_upwards [hlc] with g hg
    show d g - d g₀ ∈ U
    apply hN
    rw [Submodule.Quotient.eq] at hg
    have h3 := (hmem N _).1 hg
    simp only [Submodule.coe_sub] at h3
    have e : d g - d g₀ = (d g - w N g) - (d g₀ - w N g₀) + ((w N g : A.V) - w N g₀) := by abel
    rw [e]
    exact (Q N).add_mem ((Q N).sub_mem (hd g N) (hd g₀ N)) h3
  refine ⟨d, ⟨⟨hcont, hcoc⟩, fun g _ => hdT g⟩, fun n g => ?_⟩
  refine ⟨⟨d g - w n g, hQT n (hd g n)⟩, (hmem n _).2 (hd g n), ?_⟩
  simp

end GlobalTheory.LimCocycle
