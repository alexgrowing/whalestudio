import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.LatFull.CMInt

theorem exists_denom {K : Type} [Field K] [NumberField K] (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (c : K) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ x ∈ J, IsIntegral ℤ ((N : K) * (x * c)) := by
  obtain ⟨a, ha, h⟩ := (J * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := h (x * c) (FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mem_spanSingleton_self _ _))
  rw [Algebra.smul_def] at hw
  have : (a : K) * (x * c) = (w : K) := hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem exists_denom_eval {K σ : Type} [Field K] [NumberField K] [Finite σ]
    (J : (σ →₀ ℕ) → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : σ → K) (d : ℕ) :
    ∃ N : K, N ≠ 0 ∧ ∀ G : MvPolynomial σ K, G.IsHomogeneous d → (∀ μ, MvPolynomial.coeff μ G ∈ J μ) →
      IsIntegral ℤ (N * MvPolynomial.eval x G) := by
  classical
  choose M hM0 hM using fun μ : σ →₀ ℕ => exists_denom (J μ) (∏ i ∈ μ.support, x i ^ μ i)
  let S := (Finsupp.finite_of_degree_le (σ := σ) d).toFinset
  refine ⟨((∏ μ ∈ S, M μ : 𝓞 K) : K), ?_, fun G hG hJ => ?_⟩
  · have : (∏ μ ∈ S, M μ : 𝓞 K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => hM0 μ
    exact fun h => this (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [MvPolynomial.eval_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun μ hμ => ?_
    have hS : μ ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := hG (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this.le
    rw [← Finset.prod_erase_mul _ _ hS]
    have e : (((∏ ν ∈ S.erase μ, M ν) * M μ : 𝓞 K) : K) = ((∏ ν ∈ S.erase μ, M ν : 𝓞 K) : K) * (M μ : K) :=
      map_mul (algebraMap (𝓞 K) K) _ _
    rw [e, mul_assoc]
    exact (RingOfIntegers.isIntegral_coe _).mul (hM μ _ (hJ μ))

theorem coeff_mem_of_loc {K : Type} [Field K] [NumberField K] {g : ℕ} {B : Type} [Fintype B] {m : B → ℕ}
    (e : (Σ b, Fin (m b)) ≃ Fin g) (T abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (G : MvPolynomial (FrVar m) K) (n : ℕ) (hT : T.Good) (hℓ : ∀ j, (ℓ j).Good)
    (hloc : ∀ p, Step5Loc e T abelian₂ ℓ U G n p) (μ : FrVar m →₀ ℕ) :
    MvPolynomial.coeff μ G ∈ (lineNN T ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
  classical
  refine coeff_mem_of_local K g ℓ T (FrVar m) _ μ n _ hT hℓ fun p => ?_
  obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hloc p
  refine ⟨t, cl, ht, hcl, ?_⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
  have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
  obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
    (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
  have hrange : f (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
      Set.range (algebraMap V K') := by
    refine ⟨w, ?_⟩
    rw [map_div₀, map_mul, map_prod]
    simp only [map_pow]
    rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
  have h1 := (hind _).mp hrange
  calc p.valuation K (MvPolynomial.coeff μ G * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
      = p.valuation K (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
          p.valuation K (t ^ n) := by
        rw [← map_mul, div_mul_cancel₀ _ htn]
    _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

theorem exists_det_ne_zero_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (hG : G ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr G Y ≠ 0 := by
  classical
  have hev : ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K m b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly m _ Y]
    simp only [evalFr, map_prod]
  have hD : (∏ b, FieldPoly.blockDetPoly K m b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  have hP := mul_ne_zero hD hG
  obtain ⟨x, hx⟩ : ∃ x : FrVar m → K, MvPolynomial.eval x ((∏ b, FieldPoly.blockDetPoly K m b) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  refine ⟨X, fun b => ?_, right_ne_zero_of_mul hx⟩
  have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact left_ne_zero_of_mul hx
  exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)

theorem exists_frame_bounded_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F₀ ∈ sec Xo c a n, (∀ G, IsFrPoly F₀ z.y G → G ≠ 0) → ∃ (y : FrPt Xo c z.K) (N : z.K), N * evR Xo c F₀ y ≠ 0 ∧ ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F₀ hF₀ hne
  classical
  obtain ⟨G₀, hG₀, -⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F₀ hF₀
  obtain ⟨Y, hY, hY0⟩ := exists_det_ne_zero_evalFr_ne_zero G₀ (hne G₀ hG₀)
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c z.K z.y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit)
  rw [Units.val_one] at hy
  have hval : ∀ (F : Rul Xo c) (G : MvPolynomial (FrVar Dw.mult) z.K), IsFrPoly F z.y G →
      evR Xo c F y = evalFr G Y := fun F G hG => by
    have h1 := hG z.K (AlgHom.id c.F z.K) z.y y Y (fun b => (hY b).isUnit) (GlobalTheory.Frames.frMapUniq_refl z.y) hy
    have h2 : MvPolynomial.map (AlgHom.id c.F z.K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hgood : z.Tl.dual.Good ∧ ∀ k, (z.ℓ k).Good := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, -⟩, ⟨-, -, -, hℓ⟩, -⟩ := hz
    refine ⟨(degree_algebraic z.K z.Tl z.Tl hT hT).2.2.1, fun k => ?_⟩
    have h := hℓ k
    change (z.letters.ℓ k).Good
    generalize z.letters = L at h
    revert h
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  obtain ⟨N, hN, hint⟩ := exists_denom_eval
    (fun μ : FrVar Dw.mult →₀ ℕ => (lineNN z.Tl.dual z.ℓ (fun v : FrVar Dw.mult => z.e ⟨v.1, v.2.2⟩) μ n).I)
    (fun v : FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ)))
  refine ⟨y, N, by rw [hval F₀ G₀ hG₀]; exact mul_ne_zero hN hY0, fun F hF hv => ?_⟩
  obtain ⟨G, hG, hh⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F hF
  rw [hval F G hG]
  exact hint G hh (coeff_mem_of_loc z.e z.Tl.dual z.LamL z.ℓ z.U G n hgood.1 hgood.2
    (LocClause.step5Loc_cmPt E H Dw l Xo c z f La hz a n F hF hv G hG))

end GlobalTheory.LatFull.CMInt
