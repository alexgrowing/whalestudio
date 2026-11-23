import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormalLocusRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace NormalLocusRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_zpow_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ chartRingZ y c := by
  rw [NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, aeval_mul_zpow_mem y c hg⟩, ⟨_, aeval_mul_zpow_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_of_isHorizontal (y : (Σ k, ι k) → Ω) (hH : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [mConeMap, aeval_C, MvPolynomial.algebraMap_apply]
    simp [hn]
  rw [hH, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : CharZero (chartRingZ y c) :=
  charZero_of_inj_zero fun n hn => by
    have : ((n : chartRingZ y c) : Ω) = 0 := by rw [hn]; rfl
    exact_mod_cast this

theorem finiteType_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Algebra.FiniteType ℤ (chartRingZ y c) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

theorem exists_conductor [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ a ∈ chartRingZ y c, a ≠ 0 ∧ ∀ t ∈ integralClosure (chartRingZ y c) Ω, a * t ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have := charZero_chartRingZ y c
  have := finiteType_chartRingZ y c
  have : Module.Finite A (integralClosure A Ω) :=
    Model.finite_integralClosure_fractionRing_of_charZero A Ω
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (integralClosure A Ω)).FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (S.image ((↑) : integralClosure A Ω → Ω))
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  refine ⟨((b : A) : Ω), (b : A).2, hb0, fun t ht => ?_⟩
  have htop : (⟨t, ht⟩ : integralClosure A Ω) ∈ Submodule.span A (S : Set (integralClosure A Ω)) := by
    rw [hS]; trivial
  suffices key : ∀ x ∈ Submodule.span A (S : Set (integralClosure A Ω)), ((b : A) : Ω) * (x : Ω) ∈ A from
    key _ htop
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := hb (x : Ω) (Finset.mem_image_of_mem _ hx)
    rw [show ((b : A) : Ω) * (x : Ω) = (b : A) • (x : Ω) by rw [Algebra.smul_def]; rfl, ← hr]
    exact r.2
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Subalgebra.coe_add, mul_add]
    exact add_mem hx hz
  | smul r x _ hx =>
    have : ((b : A) : Ω) * ((r • x : integralClosure A Ω) : Ω) = (r : Ω) * (((b : A) : Ω) * (x : Ω)) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      show _ * ((r : Ω) * _) = _
      ring
    rw [this]
    exact mul_mem r.2 hx

omit [Fintype K] in

theorem isMultiHomog_prod {J : Type} (s : Finset J) (H : J → MRing ι) (N : J → K → ℕ)
    (hH : ∀ j ∈ s, IsMultiHomog (H j) (N j)) : IsMultiHomog (∏ j ∈ s, H j) (∑ j ∈ s, N j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact LocalRep.isMultiHomog_mul (hH j (Finset.mem_insert_self j s))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

theorem notMem_mCoordIdeal (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  have h := (RingHom.mem_ker).mp hmem
  erw [ConeTrdeg.mConeMap_of_isMultiHomog y hf] at h
  exact mul_ne_zero (MvPolynomial.C_ne_zero.2 h0)
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

end NormalLocusRep

open NormalLocusRep in

theorem NormalLocusRep.proof : NormalLocusRep.Statement := by
  intro K _ ι _ Ω _ y D hV hbir
  classical
  have := charZero_of_isHorizontal y hV.2.2.1

  have hchart : ∀ c : ∀ k, ι k, ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ integralClosure (chartRingZ y c) Ω,
        (aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ))) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨a, ha, ha0, hcond⟩ := exists_conductor y hbir c hc
      obtain ⟨N, H, hH, he⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hc ha
      have hP : ∀ N' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ N' k) ≠ 0 := fun N' =>
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
      have hHa : aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ)) = a := by
        rw [he, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_eq_one fun k _ => by
          rw [← zpow_natCast, ← zpow_add₀ (hc k), add_neg_cancel, zpow_zero], mul_one]
      refine ⟨N, H, hH, ?_, fun _ t ht => ?_⟩
      · rw [he]
        exact mul_ne_zero ha0 (hP N)
      · rw [hHa]
        exact hcond t ht
    · exact ⟨0, C 1, LocalRep.isMultiHomog_C 1, by simp, fun h => absurd h hc⟩
  choose N H hH hH0 hcond using hchart
  refine ⟨∑ c, N c, ∏ c, H c, isMultiHomog_prod _ H N fun c _ => hH c,
    notMem_mCoordIdeal y (isMultiHomog_prod _ H N fun c _ => hH c)
      (by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun c _ => hH0 c), ?_⟩
  intro a τ s hs z hz hfz

  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  have hHz : eval z (map (Int.castRingHom ℂ) (H c)) ≠ 0 := by
    rw [map_prod, map_prod] at hfz
    exact (Finset.prod_ne_zero_iff.mp hfz) c (Finset.mem_univ c)
  have hx := hcond c hyc _ (hs c hyc)
  obtain ⟨M, G, hG, hGe⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hyc hx
  refine ⟨M + (N c + fun k => ((τ : ℤ) * a k).toNat), N c + (M + fun k => (-((τ : ℤ) * a k)).toNat),
    G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N c + fun k => ((τ : ℤ) * a k).toNat) k,
    H c * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M + fun k => (-((τ : ℤ) * a k)).toNat) k,
    LocalRep.isMultiHomog_mul hG (LocalRep.isMultiHomog_chartMono c _),
    LocalRep.isMultiHomog_mul (hH c) (LocalRep.isMultiHomog_chartMono c _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  ·
    have hz' : ∀ p q : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ p k) * ∏ k, y ⟨k, c k⟩ ^ q k =
        ∏ k, y ⟨k, c k⟩ ^ (p k + q k) := fun p q => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => (zpow_add₀ (hyc k) _ _).symm
    have hnat : ∀ p : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ p k) = ∏ k, y ⟨k, c k⟩ ^ (p k : ℤ) := fun p =>
      Finset.prod_congr rfl fun k _ => (zpow_natCast _ _).symm
    have key : (∏ k, y ⟨k, c k⟩ ^ (-(N c k : ℤ))) * (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ M k) * (∏ k, y ⟨k, c k⟩ ^ (N c k + ((τ : ℤ) * a k).toNat)) =
        ∏ k, y ⟨k, c k⟩ ^ (M k + (-((τ : ℤ) * a k)).toNat) := by
      simp only [hnat]
      rw [hz', hz', hz']
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      push_cast
      omega
    simp only [map_mul, map_prod, map_pow, aeval_X, Pi.add_apply]
    rw [hGe]
    linear_combination (s * aeval y (H c)) * key
  · simp only [map_mul, map_prod, map_pow, map_X, eval_X]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
