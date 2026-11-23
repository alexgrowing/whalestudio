import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsCurveOfFunctionField
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

open MvPolynomial PositivityTheory.HtPt.Gf

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

theorem cone_homog (y : (Σ k, J k) → K) {g : MRing J} {d : B → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mConeMap, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  congr 1
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Finset.prod_pow_eq_pow_sum, hg m hm k]

theorem exists_homog_val {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1) (f : MRing J) :
    ∃ (N : ℕ) (g : MRing J), IsMultiHomog g (fun _ => N) ∧ aeval w g = aeval w f := by
  classical
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, fun m hm k => ?_, rfl⟩
    have : m = 0 := by
      by_contra h
      exact mem_support_iff.1 hm (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [this]
  | add f g hf hg =>
    obtain ⟨N, f', h1, h2⟩ := hf
    obtain ⟨M, g', h3, h4⟩ := hg
    refine ⟨N + M, f' * mon c (fun _ => M) + g' * mon c (fun _ => N), hom_add (hom_mul h1 (hom_mon _ _))
      (hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _), ?_⟩
    simp only [map_add, map_mul, hm, h2, h4, mul_one]
  | mul_X f q hf =>
    obtain ⟨N, f', h1, h2⟩ := hf
    refine ⟨N + 1, f' * mon (Function.update c q.1 q.2) (fun _ => 1), hom_mul h1 (hom_mon _ _), ?_⟩
    rw [map_mul, map_mul, h2, aeval_mon, aeval_X, Finset.prod_eq_single q.1 (fun l _ hl => by
      rw [Function.update_of_ne hl, hc, one_pow]) (by simp), Function.update_self, pow_one]

theorem birational_of_frac {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1)
    (hfr : ∀ s : K, ∃ f g : MRing J, aeval w g ≠ 0 ∧ aeval w f = s * aeval w g) : Birational w := by
  intro s
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  obtain ⟨f, g, h0, h⟩ := hfr s
  obtain ⟨N, f', h1, h2⟩ := exists_homog_val hc f
  obtain ⟨M, g', h3, h4⟩ := exists_homog_val hc g
  refine ⟨fun _ => N + M, f' * mon c (fun _ => M), g' * mon c (fun _ => N), hom_mul h1 (hom_mon _ _),
    hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _, ?_, ?_⟩
  · rwa [map_mul, hm, h4, mul_one]
  · rw [map_mul, map_mul, hm, hm, h2, h4, mul_one, mul_one, h]

theorem isFunctionField_of_dim {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] {w : (Σ k, J k) → K} {c : ∀ k, J k}
    (hc : ∀ k, w ⟨k, c k⟩ = 1) (hb : Birational w) {W : Ideal (MRing J)} (hW : mCoordIdeal w = W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞)) :
    GroundTheory.FunctionField.IsFunctionField (ZMod p) K := by
  refine GlobalTheory.CompanionTheory.Ar.Flat.isFunctionField_of_fg_trdeg ?_ ?_
  · refine IntermediateField.fg_def.2 ⟨Set.range w, Set.finite_range w, top_le_iff.1 fun s _ => ?_⟩
    have key : ∀ f : MRing J, aeval w f ∈ IntermediateField.adjoin (ZMod p) (Set.range w) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | mul_X f q hf => rw [map_mul, aeval_X]; exact mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    obtain ⟨d, g, h, -, -, h0, h1⟩ := hb s
    rw [← div_eq_iff h0] at h1
    exact h1 ▸ div_mem (key g) (key h)
  · have hker : RingHom.ker (mConeMap w).toRingHom = W := hW
    have hprime : W.IsPrime := hker ▸ RingHom.ker_isPrime _
    have hchar : CharP (MRing J ⧸ W) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk W), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
    let _ := ZMod.algebra (MRing J ⧸ W) p
    have : IsScalarTower ℤ (ZMod p) (MRing J ⧸ W) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) (MRing J ⧸ W) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
    obtain ⟨n, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MRing J ⧸ W)
    have hn : n = 1 + Fintype.card B := by
      rw [hdim] at h1
      exact_mod_cast h1.symm
    let μ : MRing J ⧸ W →+* MvPolynomial B K :=
      Ideal.Quotient.lift W (mConeMap w).toRingHom fun a ha => (hker.ge ha :)
    have hμ : Function.Injective μ := RingHom.lift_injective_of_ker_le_ideal W _ hker.le
    let _ := μ.toAlgebra
    have hμ' : ∀ f, algebraMap (MRing J ⧸ W) (MvPolynomial B K) (Ideal.Quotient.mk W f) = mConeMap w f :=
      fun f => rfl
    have : FaithfulSMul (MRing J ⧸ W) (MvPolynomial B K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hμ
    have : IsScalarTower (ZMod p) (MRing J ⧸ W) (MvPolynomial B K) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
    have hX : ∀ k, IsAlgebraic (MRing J ⧸ W) (X k : MvPolynomial B K) := fun k => by
      have := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W (X ⟨k, c k⟩))
      rw [hμ'] at this
      simpa [mConeMap, hc] using this
    have : Algebra.IsAlgebraic (MRing J ⧸ W) (MvPolynomial B K) := ⟨fun f => by
      induction f using MvPolynomial.induction_on with
      | C s =>
        obtain ⟨d, g, h, hg, hh, h0, h1⟩ := hb s
        refine IsAlgebraic.of_smul (y := Ideal.Quotient.mk W h) (mem_nonZeroDivisors_of_ne_zero fun e => ?_) ?_
        · have h3 := hμ' h
          rw [e, map_zero, cone_homog w hh] at h3
          exact mul_ne_zero (mt C_eq_zero.1 h0)
            (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h3.symm
        · have h3 := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W g)
          rw [hμ', cone_homog w hg, h1, map_mul, mul_assoc, mul_comm, ← cone_homog w hh] at h3
          rwa [Algebra.smul_def, hμ']
      | add f g hf hg => exact hf.add hg
      | mul_X f k hf => exact hf.mul (hX k)⟩
    have e1 := trdeg_add_eq (ZMod p) (MRing J ⧸ W) (A := MvPolynomial B K)
    have e2 := trdeg_add_eq (ZMod p) K (A := MvPolynomial B K)
    rw [h2, trdeg_eq_zero, add_zero, hn] at e1
    rw [MvPolynomial.trdeg_of_isDomain, ← e1, Cardinal.lift_id, Cardinal.mk_fintype, Nat.cast_add, Nat.cast_one] at e2
    exact (Cardinal.add_nat_inj _).1 e2

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  intro B _ J _ W p _ ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩ hchar hdim
  choose c hc using hrel
  have hp := natCast_mem_of_charOf hchar
  let F := FractionRing (MRing J ⧸ W)
  let π : MRing J →+* F := (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W)
  have hπ : ∀ f, π f = 0 ↔ f ∈ W := fun f => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F)
  have ht : ∀ k, π (X ⟨k, c k⟩) ≠ 0 := fun k h => hc k ((hπ _).1 h)
  let w' : (Σ k, J k) → F := fun q => π (X q) / π (X ⟨q.1, c q.1⟩)
  let K := Subfield.closure (Set.range w')
  let w : (Σ k, J k) → K := fun q => ⟨w' q, Subfield.subset_closure ⟨q, rfl⟩⟩
  have hw : ∀ k, w ⟨k, c k⟩ = 1 := fun k => Subtype.ext (div_self (ht k))
  have hK : CharP K p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (K.subtype.injective (by
    rw [map_natCast, map_zero, ← map_natCast π, hπ]; exact hp))
  let ε : MvPolynomial B K →+* F := eval₂Hom K.subtype fun k => π (X ⟨k, c k⟩)
  have hε : ε.comp (mConeMap w).toRingHom = π := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun q => ?_
    · simp
    · change ε (mConeMap w (X q)) = _
      rw [mConeMap, aeval_X, map_mul, eval₂Hom_C, eval₂Hom_X']
      exact div_mul_cancel₀ _ (ht _)
  have hε' : ∀ f, ε (mConeMap w f) = π f := fun f => RingHom.congr_fun hε f
  have hW : mCoordIdeal w = W := by
    refine le_antisymm (fun f hf => (hπ f).1 ?_) (hWS.le.trans (Ideal.span_le.2 fun f hf => ?_))
    · rw [← hε', show mConeMap w f = 0 from hf, map_zero]
    · obtain ⟨a, ha⟩ := hS f hf
      refine mem_mCoordIdeal ha ?_
      have h1 := (hε' f).trans ((hπ f).2 (hWS.ge (Ideal.subset_span hf)))
      rw [cone_homog w ha, map_mul, eval₂Hom_C, map_prod, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact (map_eq_zero_iff _ K.subtype.injective).1 h1
      · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h1
        rw [map_pow, eval₂Hom_X'] at hk
        exact absurd hk (pow_ne_zero _ (ht k))
  have hb : Birational w := birational_of_frac hw fun s => by
    have hr : Subring.closure (Set.range w') ≤ (K.subtype.comp (aeval w : MRing J →ₐ[ℤ] K).toRingHom).range := by
      refine Subring.closure_le.2 ?_
      rintro _ ⟨q, rfl⟩
      exact ⟨X q, congrArg K.subtype (aeval_X w q)⟩
    obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 s.2
    obtain ⟨f, rfl⟩ := hr hy
    obtain ⟨g, rfl⟩ := hr hz
    have e' : aeval w f / aeval w g = s := K.subtype.injective (by rw [map_div₀]; exact e)
    by_cases h0 : aeval w g = 0
    · exact ⟨0, 1, by simp, by simp [← e', h0]⟩
    · exact ⟨f, g, h0, (div_eq_iff h0).1 e'⟩
  let _ := ZMod.algebra K p
  exact ⟨K, inferInstance, inferInstance, isFunctionField_of_dim hw hb hW hp hdim, w, hW, hb,
    fun k => ⟨c k, hw k ▸ one_ne_zero⟩⟩

end PositivityTheory.HtPt.Ci
