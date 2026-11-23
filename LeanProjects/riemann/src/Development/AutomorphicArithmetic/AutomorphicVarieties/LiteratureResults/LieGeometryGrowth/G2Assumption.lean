import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.StepEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConeConvex

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs Filter Topology
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem cone_open (E : Type) [Field E] [NumberField E] (a : ℕ) : IsOpen (cone E a) :=
  isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := UpperTheory.V.Lit.Dr.locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩

private theorem homOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : homOm G W (0 : G.Om (q + 1)) = 0 := by
  have e : (fun s => hom (W s) ((0 : G.Om (q + 1)).1 s)) = fun _ _ => 0 := by
    funext s p
    have : (fun t => hk (W s) t ((0 : G.Om (q + 1)).1 s) p) = fun _ => 0 := by
      funext t
      ext v
      simp [hk_apply]
    rw [hom, this, intervalIntegral.integral_zero]
  rw [homOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem pbOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : pbOm G W (0 : G.Om q) = 0 := by
  have e : (fun s => pb (flow (W s) 1) ((0 : G.Om q).1 s)) = fun _ _ => 0 := by
    funext s p
    ext v
    simp [pb_apply]
  rw [pbOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem corr_sub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} {α β : Co Ξ q} {w w' : (geo ho U Ξ).Om q}
    (h : Corr U Ξ α w.1) (h' : Corr U Ξ β w'.1) : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← h g x X, ← h' g x X]
  rfl

private theorem corr_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) :
    Corr U Ξ (0 : Co Ξ q) (0 : (geo ho U Ξ).Om q).1 := fun g x X => by
  simp

private theorem half (D c : ℝ) (hD : 0 ≤ D) (hc : 0 < c) : D * Real.exp (-(2 * D / c * c)) ≤ 1 / 2 := by
  rw [div_mul_cancel₀ _ hc.ne', Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have := Real.add_one_le_exp (2 * D)
  linarith

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Lit.Geo.Cs.galois_twist_preserves_siegel_bound (h1 : LamEx) (h2 : DescEx) (h3 : DescFun) (h4 : RapidAll) (h5 : CorrSz) (h6 : DecP)
    (h7 : DecK) (h8 : Loc) (h9 : GeoSum) (h10 : GeoRet) (h11 : Supp) : G2 := by
  intro E _ _ _ a ha U hUo hUc Ξ q ω hω hd hR
  have ho := cone_open E a
  obtain ⟨f, Y, C, c, f₀, hS⟩ := stepEx E a ha U hUc
  have hC : 0 ≤ C := (abs_nonneg _).trans (hS.near 1 0 1 (by simp) (by simp))
  obtain ⟨W, hW⟩ := fieldDef E a U Y C hS.fld
  have hF := (fieldFlow E a ho U Ξ Y C hS.fld W hW).1
  have hH := omHom _ _ _ _ _ W hF
  obtain ⟨lam, hl⟩ := h1 E a ha
  obtain ⟨Φ, hΦ⟩ := h2 E a U f Y C c f₀ hS
  have hΦf := h3 E a ho U Ξ f Y C c f₀ hS Φ hΦ
  obtain ⟨w, hw, hg⟩ := (levGood E a ho U Ξ q).1 ω hω
  have hdw : (geo ho U Ξ).dOm q w = 0 := by
    have c1 := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q ω w hw
    rw [hd] at c1
    exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ (q + 1)).2 _ _ _ c1 (corr_zero ho U Ξ _)
  obtain ⟨B, hB, hrap⟩ := h4 E a U Ξ f lam C hl hS.f_le q ω hω hR
  obtain ⟨u, u0, us⟩ : ∃ u : ℕ → (geo ho U Ξ).Om q, u 0 = w ∧ ∀ j, u (j + 1) = pbOm (geo ho U Ξ) W (u j) :=
    ⟨fun j => (pbOm (geo ho U Ξ) W)^[j] w, rfl, fun j => Function.iterate_succ_apply' _ _ _⟩
  have ug : ∀ j, Good (geo ho U Ξ) (u j) := fun j => by
    induction j with
    | zero => rwa [u0]
    | succ j ih => rw [us]; exact ((omGood _ _ _ _ _ W hF q).1 _ ih).1
  have ud : ∀ j, (geo ho U Ξ).dOm q (u j) = 0 := fun j => by
    induction j with
    | zero => rwa [u0]
    | succ j ih => rw [us, hH.1, ih, pbOm_zero]
  have dec : ∀ k, ∃ A M : ℝ, 0 ≤ A ∧ 0 ≤ M ∧ ∀ j, Dec U Ξ f lam f₀ k A B ((1 / 2) ^ j * M) (u j).1 := fun k => by
    obtain ⟨D, hD, hP⟩ := h6 E a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
    have hA : 0 ≤ 2 * D / c := div_nonneg (by linarith) hS.c_pos.le
    obtain ⟨M, hM, hM'⟩ := h5 E a U Ξ q ω w.1 hw (fun g => Real.exp (B * |lam g| - 2 * D / c * f g))
      (fun _ => (Real.exp_pos _).le) (hrap _ hA) k
    refine ⟨2 * D / c, M, hA, hM, fun j => ?_⟩
    induction j with
    | zero =>
      rw [u0, pow_zero, one_mul]
      exact fun g x _ => hM' g x
    | succ j ih =>
      rw [us]
      have hj : (0 : ℝ) ≤ (1 / 2) ^ j * M := by positivity
      refine Dec.of_le U Ξ (hP _ _ hA hj _ ih) ?_
      rw [pow_succ', mul_assoc (1 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_right (half D c hD hS.c_pos) hj
  have geom : ∀ x : ℝ, Summable fun j : ℕ => x * (1 / 2 : ℝ) ^ j := fun x => summable_geometric_two.mul_left x
  have lim : ∀ s, ∀ p ∈ cone E a, f₀ + C < Φ s p → Tendsto (fun j => (u j).1 s p) atTop (𝓝 0) := fun s p hp hlt => by
    obtain ⟨A, M, hA, hM, hj⟩ := dec 0
    obtain ⟨N, hN, D, hD⟩ := h8 E a ho U Ξ f lam hS.f_nonneg hl Φ hΦ hΦf q 0 A B f₀ hA hB s p hp (by linarith)
    refine squeeze_zero_norm (fun j => ?_) (geom (D * M)).tendsto_atTop_zero
    refine (hD _ (by positivity) _ (hj j) p (mem_of_mem_nhds hN)).norm_le.trans_eq ?_
    ring
  cases q with
  | zero =>
    refine ⟨ω, hω, hd, h11 E a U Ξ f Y C c f₀ hS Φ hΦ 0 ω w.1 (f₀ + C) hw fun s p hp hlt => ?_, sub_self ω⟩
    have e : ∀ j, u j = w := fun j => by
      induction j with
      | zero => exact u0
      | succ j ih =>
        have := hH.2.2.1 w
        rw [hdw, homOm_zero, sub_eq_zero] at this
        rw [us, ih, this]
    have := lim s p hp hlt
    simp only [e] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  | succ q =>
    have hO := omGood _ _ _ _ _ W hF q
    obtain ⟨z, hz, hz'⟩ := h9 _ _ _ _ (geo ho U Ξ) Φ hΦf (f₀ + C) q (fun j => homOm (geo ho U Ξ) W (u j)) u
      (fun j => (hO.2.2 _ (ug j)).inv)
      (fun j => by
        have := hH.2.2.2 q (u j)
        rw [ud j, homOm_zero, add_zero] at this
        exact this.symm.trans (congrArg (· - u j) (us j).symm))
      (fun k s p hp hlt => by
        obtain ⟨A, M, hA, hM, hj⟩ := dec k
        obtain ⟨D', hD', hK⟩ := h7 E a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
        obtain ⟨N, hN, D, hD⟩ := h8 E a ho U Ξ f lam hS.f_nonneg hl Φ hΦ hΦf q k A B (f₀ + C) hA hB s p hp hlt
        refine ⟨N, hN, _, geom (D * D' * M), fun j x hx => ?_⟩
        have p1 : (0 : ℝ) ≤ (1 / 2) ^ j * M := mul_nonneg (pow_nonneg (by norm_num) _) hM
        have p2 := hK _ p1 _ (hj j)
        have p3 := hD _ (mul_nonneg hD' p1) _ p2 x hx
        have p4 : D * (D' * ((1 / 2) ^ j * M)) = D * D' * M * (1 / 2) ^ j := by ring
        rw [p4] at p3
        exact p3) lim
    obtain ⟨l, hgl⟩ := UpperTheory.V.Lit.Dr.gauge E a ha ho U Ξ hUc
    rw [u0] at hz'
    obtain ⟨z', g', hz''⟩ := h10 _ _ _ _ (geo ho U Ξ) (UpperTheory.V.Lit.Dr.coneConvex E a).2 l hgl Φ hΦf (f₀ + C + 1) q w z
      hdw hg.basic hz hz'
    obtain ⟨η, cη, lη⟩ := (levGood E a ho U Ξ q).2 _ g'
    have cd := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q η z' cη
    have cs := corr_sub ho U Ξ hw cd
    refine ⟨ω - dCo (smLie Ξ) η, (levD E a U Ξ _ ω hω).2 _ (levD E a U Ξ q η lη).1, ?_,
      h11 E a U Ξ f Y C c f₀ hS Φ hΦ _ _ _ (f₀ + C + 1) cs fun s p hp hlt => ?_, η, lη, (sub_sub_cancel _ _).symm⟩
    · have c1 := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ _ _ _ cs
      rw [map_sub, hdw, hH.2.1, sub_zero] at c1
      exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ _).1 _ _ _ c1 (corr_zero ho U Ξ _)
    · change w.1 s p - ((geo ho U Ξ).dOm q z').1 s p = 0
      rw [hz'' s p hp hlt, sub_self]
