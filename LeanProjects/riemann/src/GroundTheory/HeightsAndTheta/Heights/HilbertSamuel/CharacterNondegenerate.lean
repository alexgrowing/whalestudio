import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace NormCountBounded

section Coords

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem exists_coord_ne_zero {x : Ix κ → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) d) :
    ∃ c : κ, x ⟨(), c⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 ()
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem aeval_mul_zpow_mem (x : Ix κ → Ω) (c : κ) {τ : ℕ} {g : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g (fun _ => τ)) :
    aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) ∈ chartRingZ (ι := GlobalTheory κ) x (fun _ => c) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = τ := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have key : aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) =
      aeval (fun p : Ix κ => x p / x ⟨(), c⟩) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm,
      zpow_neg, zpow_natCast]
    ring
  rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem secM_le_chartLat (x : Ix κ → Ω) (τ : ℕ) :
    secM (ι := GlobalTheory κ) x (fun _ => τ) ≤ chartLat (ι := GlobalTheory κ) x 1 τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (GlobalTheory κ), IsMultiHomog g (fun _ => τ) ∧ aeval x g = s} ≤
      (chartLat (ι := GlobalTheory κ) x 1 τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have hc : c = fun _ => c () := rfl
    rw [hc]
    simpa using aeval_mul_zpow_mem x (c ()) hg
  exact hle hs

end Coords

section Counts

variable {Ω : Type} [Field Ω]

theorem smallSectionCount_mono_lattice {P : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {τ : ℕ} (hle : La τ ≤ La' τ)
    (hfin : {s : La' τ | P τ (s : Ω)}.Finite) : smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hcard : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨s.1.1, hle s.1.2⟩, s.2⟩) fun s t h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

theorem smallSectionCount_nonneg (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : 0 ≤ smallSectionCount P La τ :=
  Real.log_natCast_nonneg _

theorem liminf_le_limsup_of_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n)
    (hg : ∃ B, ∀ᶠ n in atTop, g n ≤ B) : liminf f atTop ≤ limsup g atTop := by
  obtain ⟨B, hB⟩ := hg
  have hfb : IsBoundedUnder (· ≤ ·) atTop f := ⟨B, by simpa using hB.mono fun n hn => (hfg n).trans hn⟩
  have hfb' : IsBoundedUnder (· ≥ ·) atTop f := isBoundedUnder_of ⟨0, fun n => hf n⟩
  have hgb : IsBoundedUnder (· ≤ ·) atTop g := ⟨B, by simpa using hB⟩
  exact (liminf_le_limsup hfb hfb').trans
    (limsup_le_limsup (Eventually.of_forall hfg) hfb'.isCoboundedUnder_flip hgb)

theorem norm_count_bounded {h : ℕ → ℝ} {C : ℝ} (D : ℕ) (hC : ∀ τ, h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)) :
    ∃ B, ∀ᶠ τ in atTop, h τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ B := by
  refine ⟨|C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ), eventually_atTop.2 ⟨1, fun τ hτ => ?_⟩⟩
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hfac : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hden : 0 < (τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have h1 : ((τ : ℝ) + 1) ^ (D + 1) ≤ 2 ^ (D + 1) * (τ : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1) := hC τ
    _ ≤ |C| * ((τ : ℝ) + 1) ^ (D + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (D + 1) * (τ : ℝ) ^ (D + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
      field_simp

end Counts

end NormCountBounded

namespace NormCountBounded

theorem semipositiveH_of_rel {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P0 P : Ideal (MRing ι)} {A : HermLine ι} (hle : P0 ≤ P) (h : IsSemipositiveRel P0 P A) :
    IsSemipositiveH P A :=
  ⟨h.1, fun z hz w hw => h.2 z hz w fun f hf => hw f (hle hf)⟩

end NormCountBounded

open NormCountBounded in

theorem G6.proof (hA : ArithmeticVolumeResolution.Statement) (hRE : ResExistsStatement) (hRB : ResBridgeStatement)
    (hP : PackingStatement) (hC : BirationalCoordinates.Statement) (hG : ArithmeticVolumeBig.Statement) :
    G6.Statement := by
  refine ⟨?_, G6.statementB_of_G6Prime hG⟩
  intro D Ω _ _ κ _ x m II hII hg
  have harx : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hg.arith
  obtain ⟨c, hc⟩ := exists_coord_ne_zero harx
  obtain ⟨Ω', _, _, x', hI, hbir, hcount⟩ := hC Ω κ x c hc
  obtain ⟨P0, hP0, hsemi⟩ := hg.semipos
  rw [coordIdeal_eq_mCoordIdeal, ← hI] at hP0 hsemi
  have har' : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x') (D + 1) := hI ▸ harx
  have hsm : IsSmoothHerm (HermLine.ofCone m) := hsemi.1
  have key := hA hRE hRB κ Ω' (fun i => x' ⟨(), i⟩) D (HermLine.ofCone m) II hg.one_le hII rfl har' hbir
    (semipositiveH_of_rel hP0 hsemi) (fun z => hg.conjInv z)
  have hpack := hP Unit (GlobalTheory κ) Ω' x' D (HermLine.ofCone m) (chartLat (ι := GlobalTheory κ) x' (HermLine.ofCone m).a)
    har' hbir hsm (fun τ s hs c hc => isIntegral_algebraMap (x := (⟨_, hs c hc⟩ : chartRingZ (ι := GlobalTheory κ) x' c)))
  obtain ⟨C, hCb⟩ := hpack.2
  have htop : top II x m D = II Unit (GlobalTheory κ) (mCoordIdeal (ι := GlobalTheory κ) x') (D + 1)
      (fun _ => HermLine.ofCone m) := by
    change II Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (fun _ => HermLine.ofCone m) = _
    rw [coordIdeal_eq_mCoordIdeal, hI]
  have hvol : arVolP (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x (HermLine.ofCone m))
        (chartLat (ι := GlobalTheory κ) x (HermLine.ofCone m).a) 1 D =
      limsup (fun τ : ℕ => smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x') x' (HermLine.ofCone m))
        (chartLat (ι := GlobalTheory κ) x' (HermLine.ofCone m).a) τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
        atTop := by
    simp only [arVolP, one_mul, hcount]
  rw [htop, hvol]
  refine key.trans (liminf_le_limsup_of_le (fun τ => div_nonneg (smallSectionCount_nonneg _ _ _) (by positivity))
    (fun τ => div_le_div_of_nonneg_right (smallSectionCount_mono_lattice (secM_le_chartLat x' τ) (hpack.1 τ)) (by positivity))
    (norm_count_bounded D hCb))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
