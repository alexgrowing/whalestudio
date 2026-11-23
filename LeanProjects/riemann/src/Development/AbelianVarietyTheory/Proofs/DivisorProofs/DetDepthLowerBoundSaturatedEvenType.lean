import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtBasisMapGood
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvariaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadiiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolutionOrdGeRadius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowEqZeroOfDegreeLt

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthLow

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem radius_nonneg {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 0 ≤ radius p k := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  refine div_nonneg ?_ (by nlinarith)
  have : (0 : ℝ) < (p : ℝ) ^ (-(2 * k + 1)) := zpow_pos (by linarith) _
  linarith

theorem radius_anti {p : ℕ} (hp : 3 ≤ p) {k l : ℤ} (h : k ≤ l) : radius p l ≤ radius p k := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  refine div_le_div_of_nonneg_right ?_ (by nlinarith)
  have : (p : ℝ) ^ (-(2 * l + 1)) ≤ (p : ℝ) ^ (-(2 * k + 1)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  linarith

theorem ordGe_mono {M : ℕ} {ρ : Fin M → ℝ} {g : MvPowerSeries (Fin M) C} {r r' : ℝ}
    (h : OrdGe v ρ g r) (hr : r' ≤ r) : OrdGe v ρ g r' := fun α =>
  le_trans (WithTop.coe_le_coe.2 (by linarith)) (h α)

theorem coeff_lin {M : ℕ} (x : Fin M → C) (α : Fin M →₀ ℕ) :
    coeff α (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) =
      ∑ m, if α = Finsupp.single m 1 then x m else 0 := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, coeff_X]
  split_ifs <;> simp

theorem coeff_lin_eq_zero {M : ℕ} (x : Fin M → C) (α : Fin M →₀ ℕ) (h : Finsupp.degree α ≠ 1) :
    coeff α (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) = 0 := by
  rw [coeff_lin]
  refine Finset.sum_eq_zero fun m _ => if_neg fun e => h ?_
  rw [e]; simp

theorem ordGe_lin {M : ℕ} (ρ : Fin M → ℝ) (x : Fin M → C) (r : ℝ) (hx : ∀ m, IsIntV v (x m))
    (h : ∀ m, x m ≠ 0 → r ≤ ρ m) :
    OrdGe v ρ (∑ m, x m • (X m : MvPowerSeries (Fin M) C)) r := by
  intro α
  rw [coeff_lin]
  refine v.map_le_sum fun m _ => ?_
  split_ifs with e
  · by_cases h0 : x m = 0
    · rw [h0, v.map_zero]; exact le_top
    · refine le_trans ?_ (hx m)
      have h1 : ∑ k, ρ k * (α k : ℝ) = ρ m := by
        rw [e, Finset.sum_eq_single m]
        · simp
        · intro k _ hk
          simp [Finsupp.single_eq_of_ne hk]
        · simp
      rw [h1, ← WithTop.coe_zero]
      exact WithTop.coe_le_coe.2 (by linarith [h m h0])
  · rw [v.map_zero]; exact le_top

theorem det_int {n : ℕ} (M : Matrix (Fin n) (Fin n) C) (hM : ∀ a b, IsIntV v (M a b)) :
    IsIntV v M.det := by
  let M' : Matrix (Fin n) (Fin n) (PTb.intRing v) := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hMM : (PTb.intRing v).subtype.mapMatrix M' = M := by
    ext a b; rfl
  have := RingHom.map_det (PTb.intRing v).subtype M'
  rw [hMM] at this
  rw [← this]
  exact (M'.det).2

theorem isSatFrame_of_mul {i d : ℕ} {x u : Fin i → Fin d → C} {T : Matrix (Fin d) (Fin d) C}
    (hx : ∀ a b, IsIntV v (x a b)) (hT : ∀ a b, IsIntV v (T a b))
    (hxT : ∀ a e, u a e = ∑ b, x a b * T b e) (hu : IsSatFrame v u) : IsSatFrame v x := by
  obtain ⟨-, r, hr⟩ := hu
  refine ⟨hx, ?_⟩
  have hm : (Matrix.of fun a b => u a (r b)) = (Matrix.of x) * (T.submatrix id r) := by
    ext a b
    simp [Matrix.mul_apply, hxT]
  rw [hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet] at hr
  by_contra hne
  have hlt : (0 : WithTop ℝ) < v (∑ S : {S : Finset (Fin d) // S.card = i},
      ((Matrix.of x).submatrix id (S.1.orderEmbOfFin S.2)).det *
        ((T.submatrix id r).submatrix (S.1.orderEmbOfFin S.2) id).det) := by
    refine v.map_lt_sum (by simp) fun S _ => ?_
    rw [v.map_mul]
    have h1 : (0 : WithTop ℝ) < v ((Matrix.of x).submatrix id (S.1.orderEmbOfFin S.2)).det :=
      lt_of_le_of_ne (det_int _ fun a b => hx _ _) fun e => hne ⟨S.1.orderEmbOfFin S.2, e.symm⟩
    have h2 : (0 : WithTop ℝ) ≤ v ((T.submatrix id r).submatrix (S.1.orderEmbOfFin S.2) id).det :=
      det_int _ fun a b => hT _ _
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right h2)
  exact hlt.ne' hr

theorem lgSum_change {d M : ℕ} (p : ℕ) (l c : Fin d → ℕ → Fin d → C)
    (T : Matrix (Fin d) (Fin d) C) (h : ∀ a n e, l a n e = ∑ b, c a n b * T b e)
    (t : Fin d → MvPowerSeries (Fin M) C) (e : Fin d) :
    lgSum p l t e = ∑ b, T b e • lgSum p c t b := by
  ext α
  have hc : ∀ (c : Fin d → ℕ → Fin d → C) b, coeff α (lgSum p c t b) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n)) :=
    fun _ _ => rfl
  rw [map_sum, hc]
  simp only [coeff_smul, hc, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem exists_least_exponent {p c : ℕ} (hp : 3 ≤ p) :
    ∃ K : ℕ, c ≤ p ^ (2 * K + 1) ∧ (K = 0 ∨ p ^ (2 * K - 1) < c) := by
  classical
  have hex : ∃ K : ℕ, c ≤ p ^ (2 * K + 1) :=
    ⟨c, le_trans (Nat.lt_pow_self (by omega : 1 < p)).le
      (Nat.pow_le_pow_right (by omega) (by omega))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · right
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show 2 * (Nat.find hex - 1) + 1 = 2 * Nat.find hex - 1 by omega] at h1
    exact not_le.1 h1

theorem sum_two_radii {i cr : ℕ} (h : cr ≤ i) (r s : ℝ) :
    ∑ a : Fin i, (if a.val < cr then r else s) = i * s + cr * (r - s) := by
  have h1 : ∀ a : Fin i, (if a.val < cr then r else s) = s + (if a.val < cr then r - s else 0) := by
    intro a; split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    Fin.card_filter_val_lt, min_eq_right h]
  simp

theorem coeff_in_tangent_basis [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime)
    (hvp : v (p : C) = 1) {d h : ℕ} {ty : Fin d → ZMod h} {G : LogFGL v d}
    {γ : Fin d → Fin d → PowerSeries C} (hB : IsBasis G p ty γ) (dp : Fin d → ℤ)
    (hlc : ∀ a, 0 ≤ dp a → G.lc p (γ a) 1 = 0 ∧
      G.lc p (γ a) 2 ∈ Submodule.span C
        (Set.range fun b : {b // dp a - 1 ≤ dp b} => tangent (γ b.1))) :
    ∃ c : Fin d → ℕ → Fin d → C,
      (∀ a n e, G.lc p (γ a) n e = ∑ b, c a n b * PTb.tmat γ b e) ∧
      (∀ a, c a 0 = Pi.single a 1) ∧
      (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
      (∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b)) := by
  classical
  have hv := pt5v' C v p hp hvp d h ty G γ hB
  obtain ⟨hγ, -, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have hbound : ∀ (w : Fin d → C) (r : WithTop ℝ), (∀ e, r ≤ v (w e)) →
      ∀ b, r ≤ v (Matrix.vecMul w (PTb.tmat γ)⁻¹ b) := by
    intro w r hw b
    simp only [Matrix.vecMul, dotProduct]
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_trans (hw e) (le_add_of_nonneg_right (PTb.isIntV_tmat_inv hγ hdet' e b))
  have hrow : ∀ a, Matrix.vecMul (tangent (γ a)) (PTb.tmat γ)⁻¹ = Pi.single a 1 := by
    intro a
    have e : tangent (γ a) = Matrix.vecMul (Pi.single a 1) (PTb.tmat γ) := by
      rw [Matrix.single_one_vecMul]; rfl
    rw [e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (PTb.tmat_isUnit_det hdet'),
      Matrix.vecMul_one]
  refine ⟨fun a n => Matrix.vecMul (G.lc p (γ a) n) (PTb.tmat γ)⁻¹, fun a n e => ?_, fun a => ?_,
    fun a n => hbound _ _ ((hv a).1 n), fun a ha => ?_⟩
  · exact (congrFun (PTb.vecMul_inv_tmat hdet' (G.lc p (γ a) n)) e).symm
  · dsimp only
    rw [← PTb.tangent_eq_lc_zero G p (fun b => (hγ a b).1), hrow]
  · obtain ⟨h1, h2⟩ := hlc a ha
    refine ⟨?_, fun n b hn => hbound _ _ (fun e => (hv a).2 h1 n e hn) b, fun b hb => ?_⟩
    · dsimp only
      rw [h1, Matrix.zero_vecMul]
    · by_contra hn
      apply hb
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 h2
      dsimp only
      rw [← hy, Matrix.sum_vecMul, Finset.sum_apply]
      refine Finset.sum_eq_zero fun b' _ => ?_
      rw [Matrix.smul_vecMul, hrow, Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
      intro e
      exact hn (e ▸ b'.2)

theorem detDepth_lower : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → 3 ≤ p → ∀ (d h : ℕ), 0 < h → Even h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j : ℕ), (∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ j) → ∀ (τ : ZMod h), Even τ.val → ∀ (i c : ℕ), 1 ≤ c → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ cr : ℕ, cr ≤ i ∧ (cr : ℝ) ≤ j * (3 / 2 + Real.logb p c / 2) ∧ ((((i : ℝ) - cr) * c * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p c + 1) : ℝ) : EReal) ≤ detDepth G u c := by
  intro C _ _ _ v p hp hvp hp3 d h hh hev ty G μ j hj τ hτ i c hc u hu huτ
  classical
  obtain ⟨K, hK1, hK2⟩ := exists_least_exponent (c := c) hp3
  obtain ⟨γ, dp, hB, hdp, -, hcard, hlc⟩ :=
    GlobalTheory.T.logFGL_depth_stages_lowA C v p hp hp3 hvp d h hh hev ty G μ j K hj
  obtain ⟨cc, hcT, hc0, hcv, hcdp⟩ := coeff_in_tangent_basis hp hvp hB dp hlc
  obtain ⟨⟨Ψ, hΨint, hΨ0, hΨΦ, hΦΨ⟩, hlg⟩ :=
    (GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases.2 C v p hp hvp d h hh ty G μ).2 γ hB
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have hΦ : PTGood v (basisMap G γ) := by
    rw [GlobalTheory.basisMap_eq_ptBasisMap]; exact ptBasisMap_good G hγ

  obtain ⟨x, hxint, hxT, hxτ⟩ : ∃ x : Fin i → Fin d → C, (∀ a b, IsIntV v (x a b)) ∧
      (∀ a e, u a e = ∑ b, x a b * PTb.tmat γ b e) ∧ ∀ a b, ty b ≠ τ → x a b = 0 := by
    refine ⟨fun a => Matrix.vecMul (u a) (PTb.tmat γ)⁻¹,
      fun a b => PTb.isIntV_vecMul_inv hγ hdet' (hu.1 a) b,
      fun a e => (congrFun (PTb.vecMul_inv_tmat hdet' (u a)) e).symm, fun a => ?_⟩
    refine PTb.vecMul_tmat_support ty hdet' (fun b e he => ?_) _ τ fun e he => ?_
    · rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
      exact (hγty b).2 0 e (by simpa using he)
    · rw [PTb.vecMul_inv_tmat hdet']
      exact huτ a e he
  have hxsat : IsSatFrame v x :=
    isSatFrame_of_mul hxint (fun a b => (hγ a b).2 1) hxT hu
  obtain ⟨g, cr, hcri, hcrS, hgint, hgdet, hgS⟩ :=
    GlobalTheory.LowU.adapted_basis C v i d x (Finset.univ.filter fun b => ty b = τ ∧ dp b < K) hxsat
  obtain ⟨hcount, hKb⟩ := GlobalTheory.T.low_count_all_bounds.2.2 p i cr K c hp3 hc hcri hK1 hK2
  refine ⟨cr, hcri, ?_, ?_⟩
  · have h1 : (cr : ℝ) ≤ ((K : ℝ) + 1) * j := by exact_mod_cast hcrS.trans (hcard τ hτ)
    rw [mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_right hKb (Nat.cast_nonneg j))

  set ρ : Fin i → ℝ := fun a => if a.val < cr then radius p (-1) else radius p K with hρ
  set x' : Fin i → Fin d → C := fun a b => ∑ a', g a a' * x a' b with hx'
  have hρK : ∀ a, radius p K ≤ ρ a := by
    intro a
    simp only [hρ]
    split_ifs
    · exact radius_anti hp3 (by omega)
    · exact le_rfl
  have hz : ∀ b, OrdGe v ρ (∑ a, x' a b • (X a : MvPowerSeries (Fin i) C)) (radius p (dp b)) := by
    intro b
    refine ordGe_lin ρ _ _ (fun a => ?_) fun a ha => ?_
    · exact (PTb.intRing v).sum_mem fun a' _ => (PTb.intRing v).mul_mem (hgint a a') (hxint a' b)
    · have hb : ty b = τ := by
        by_contra hb
        exact ha (Finset.sum_eq_zero fun a' _ => by rw [hxτ a' b hb, mul_zero])
      by_cases hK : dp b < K
      · have hacr : a.val < cr := by
          by_contra hacr
          exact ha (hgS a (not_lt.1 hacr) b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb, hK⟩))
        simp only [hρ, if_pos hacr]
        exact radius_anti hp3 (hdp b).1
      · exact (radius_anti hp3 (not_lt.1 hK)).trans (hρK a)
  obtain ⟨t, ht0, hteq, htord, -⟩ := GlobalTheory.DepthRadii.exists_solution_ordGe_radius C v p hp hp3 hvp d i dp cc (fun a => (hdp a).1)
    hc0 hcv hcdp ρ (fun a => (radius_nonneg hp3 _).trans (hρK a))
    (fun b => ∑ a, x' a b • (X a : MvPowerSeries (Fin i) C))
    (fun b α hα => coeff_lin_eq_zero _ α hα) hz
  have heq : ∀ e, subst t (subst (basisMap G γ) (G.lg e)) =
      ∑ a, (∑ a', g a a' • u a') e • (X a : MvPowerSeries (Fin i) C) := by
    intro e
    rw [hlg e, GlobalTheory.LgSubst.subst_sum_lgCurve_eq_lgSum C v p hp d i G γ (fun a => (hγty a).1) t ht0 e,
      lgSum_change p _ cc (PTb.tmat γ) hcT]
    simp only [hteq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [hx', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hxT, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet,
    GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G _ (basisMap G γ) Ψ
      (fun a => ⟨(hΦ a).2, (hΦ a).1, hΨint a, hΨ0 a⟩) (fun a => ⟨hΨΦ a, hΦΨ a⟩) t ht0 heq]
  refine le_iInf fun f => WithBot.coe_le_coe.2 ?_
  refine GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t _ ht0
    (fun a => ordGe_mono (htord a) (radius_nonneg hp3 _)) (fun α hα => ?_) f.1 f.2
  have hk : ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤
      toE (v ((detPow C i c).coeff α * mfact α)) :=
    (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hvp i c).2.trans (iInf₂_le α hα)
  refine le_trans (WithTop.coe_le_coe.2 ?_) (WithBot.coe_le_coe.1 hk)
  rw [hρ, sum_two_radii hcri]
  linarith

end GlobalTheory.DepthLow
