import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
set_option maxSynthPendingDepth 1

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem slX_lower_of_stokesAt (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}
    {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (Ch Cu : ℝ)
    (hII : IsIntersectionSystem II) (hpos : CuspBundlePos X) (hconj : MUConjInvariant X)
    (hint : HtInterior Ch X) (hbd : HtBoundary Ch X) (hmean : CuspMean Cu X) (hdeg : 0 < degMu X.H)
    (hN : 3 * D.j' + 1 ≤ D.N) (B : ℕ) (hB1 : 4 * D.f + 2 ≤ B) (hB2 : 4 * D.f * D.N ^ 2 ≤ B)
    (hS : StokesAt X B) :
    -((Ch + Cu / 2) * D.f * D.j' * X.La B) ≤ slX X B := by
  set a : ℝ := -(Ch * D.f * D.j' * X.La B) with ha
  have hyp : StokesLimit.Hyp X B a := by
    intro p q hp hpq
    have hq0 : 0 < q := by omega
    have hq : (0 : ℝ) < q := Nat.cast_pos.2 hq0
    obtain ⟨t₁, ht₁, hpos'⟩ := hpos B p q hB1 hp hpq
    obtain ⟨t₂, ht₂, hconj'⟩ := hconj B p q hB1 hp hpq
    obtain ⟨t₃, ht₃, hint'⟩ := hint B p q hB2 hp hpq
    obtain ⟨t₄, ht₄, hbd'⟩ := hbd B p q hB2 hp hpq
    refine ⟨min (min t₁ t₂) (min t₃ t₄), lt_min (lt_min ht₁ ht₂) (lt_min ht₃ ht₄), fun t' ht0 ht1 => ?_⟩
    have h1 : t' ≤ t₁ := ht1.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : t' ≤ t₂ := ht1.trans ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : t' ≤ t₃ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h4 : t' ≤ t₄ := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hsemi, hnef, -⟩ := hpos' t' ht0 h1
    have hz := hZ K ι (mCoordIdeal D.y) (mCoordIdeal D.y) D.n (X.MUq B p q t')
      ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) II hII D.arith le_rfl hsemi hnef
      (hconj' t' ht0 h2) (fun W hW hXW => by
        have hh : a - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W := by
          by_cases hoff : OffBoundary D.Bd W
          · exact hint' t' ht0 h3 W hW hXW hoff
          · exact hbd' t' ht0 h4 W hW hXW hoff
        have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
        have e : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) (X.MUq B p q t') W =
            (q : ℝ) * htMUc X.H X.S' B p q t' W := by
          simp only [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height, htMUc, ComponentSetting.MUq]
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hh hq.le)
    simp only [topMUc, geomDegMUc]
    rw [le_div_iff₀ (pow_pos hq _)]
    have e : ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) *
        (geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n / (q : ℝ) ^ D.n) * (q : ℝ) ^ (D.n + 1) =
        ((D.n + 1 : ℕ) : ℝ) * ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) *
          geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n := by
      rw [pow_succ]
      field_simp
    rw [e]
    exact hz
  have h6 := hS a hyp
  have hj' : 1 ≤ D.j' := by
    have := D.j_le
    have := D.two_le_N
    simp only [ComponentData.j']
    omega
  have hm := hmean hj' hN B hB2
  have hn : (0 : ℝ) < ((D.n + 1 : ℕ) : ℝ) * degMu X.H := mul_pos (by positivity) hdeg
  rw [slX, le_div_iff₀ hn]
  have hm' := mul_le_mul_of_nonneg_left hm hn.le
  nlinarith

theorem ppc_lower_of_setting (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} (hII : IsIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} [Nonempty Ψ] (T : RootTower Ψ N) {Ch Cu rd Lval : ℝ}
    (hvol : ∀ c, 0 < T.vol c) (hN : 3 * (N - T.j) + 1 ≤ N) {B : ℕ} (hB : 4 * Fintype.card Ψ * N ^ 2 ≤ B)
    {c : T.Comp} (h : T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) :
    -((Ch + Cu / 2) * Fintype.card Ψ * (min T.j (N - T.j) : ℕ) * bigLam B rd Lval) *
        (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j)) ≤ T.PPc II B c (testPoly T.j) := by
  obtain ⟨K, _, ι, _, Ω, _, _, E, _, _, D, O, Lt, _, _, _, X, hDN, hDj, hrd, hL, h1, h2, h3, h4, h5, h6, -, h7, h8⟩ := h
  have hJ : 0 < testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hf : D.f = Fintype.card Ψ := rfl
  have hj' : D.j' = N - T.j := by simp only [ComponentData.j', hDN, hDj]
  have hmin : min T.j (N - T.j) = N - T.j := by
    have := T.j_lt
    omega
  have hcard : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hN2 : 2 ≤ N := by
    have := T.j_pos
    have := T.j_lt
    omega
  have hsq : 4 * Fintype.card Ψ * 4 ≤ 4 * Fintype.card Ψ * N ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have hB1 : 4 * D.f + 2 ≤ B := by
    rw [hf]
    omega
  have hB2 : 4 * D.f * D.N ^ 2 ≤ B := by rwa [hf, hDN]
  have hN' : 3 * D.j' + 1 ≤ D.N := by rwa [hj', hDN]
  have hl := slX_lower_of_stokesAt hZ X Ch Cu hII h1 h2 h3 h4 h5 h6 hN' B hB1 hB2 h7
  have hLa : X.La B = bigLam B rd Lval := by
    simp only [ComponentSetting.La, abelian₂, bigLam, hrd, hL]
  rw [hLa, hf, hj'] at hl
  rw [h8, hmin]
  have hw : (0 : ℝ) < ((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j) :=
    mul_pos (by positivity) (mul_pos (hvol c) hJ)
  exact mul_le_mul_of_nonneg_right hl hw.le

theorem slope_lower_of_base_settings : ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ),
    T.Proportional → 3 * (N - T.j) + 1 ≤ N →
    (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c,
      T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) →
    T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  intro hZ II hII Ψ _ _ N _ T Ch Cu rd Lval hP hN hset B hB1 hB2 hB3
  rw [RootTower.PPt, RootTower.volT, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => ppc_lower_of_setting hZ hII T hP.1 hN hB2 (hset B hB1 hB2 hB3 c)

end GlobalTheory.CompanionTheory.Ar.Top
