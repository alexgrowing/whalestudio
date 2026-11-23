import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CurvNumStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MarginsOfGaps
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsHomogeneousAevalEqZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.ArchInputs

section Model

open ReciprocityTheory.ChartRestriction.G.I2 (phiFD PT)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem one_le_rd : 1 ≤ PT.rd E := by
  unfold PT.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h

theorem phi_nonneg (X : Data E r) (th : ℝ) (x : Frame X.Ψ r) : 0 ≤ phiFD X th x := by
  unfold phiFD
  split_ifs
  · positivity
  · exact le_rfl

theorem phi_inv (X : Data E r) (hr : 0 < r) (th : ℝ) : IsInvFn X (phiFD X th) := by
  intro γ hγ x hx b hb
  unfold phiFD
  rw [(GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames r X hr).1 γ hγ x hx b hb]

theorem phi_lower (X : Data E r) (hf : 0 < PT.f E) {th : ℝ} (hth : 0 < th) :
    ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ phiFD X th x := by
  have h1 := one_le_rd (E := E)
  refine ⟨2 * PT.f E / PT.rd E ^ 2, th, by positivity, hth, fun x _ hx => ?_⟩
  unfold phiFD
  rw [if_pos hx, div_div]

theorem phi_le (X : Data E r) (th : ℝ) (x : Frame X.Ψ r) : phiFD X th x ≤ 2 * PT.f E / X.la1 x ^ 2 := by
  have h1 := one_le_rd (E := E)
  unfold phiFD
  split_ifs
  · rw [← div_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact div_le_self (by positivity) (one_le_pow₀ h1)
  · positivity

theorem phi_threshold (X : Data E r) (th : ℝ) {th' : ℝ} (h' : 0 < th') :
    ∃ C : ℝ, ∀ x, phiFD X th x ≤ phiFD X th' x + C := by
  refine ⟨2 * PT.f E / th' ^ 2, fun x => ?_⟩
  have hC : (0 : ℝ) ≤ 2 * PT.f E / th' ^ 2 := by positivity
  by_cases hx : X.la1 x < th'
  · have : phiFD X th x ≤ phiFD X th' x := by
      have h0 := phi_nonneg X th' x
      unfold phiFD at h0 ⊢
      rw [if_pos hx] at h0 ⊢
      split_ifs
      · exact le_rfl
      · exact h0
    linarith
  · have h0 := phi_nonneg X th' x
    have h1 := phi_le X th x
    have h2 : 2 * PT.f E / X.la1 x ^ 2 ≤ 2 * PT.f E / th' ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ h'.le (not_lt.1 hx) 2)
    linarith

theorem decay_threshold (X : Data E r) (th : ℝ) {th' : ℝ} (h' : 0 < th') (i : ℕ) (g : Frame X.Ψ r → ℝ) (K : ℝ)
    (hK : ∀ x ∈ X.dom, g x ≤ K * Real.exp (-(2 * (i : ℝ) * phiFD X th' x))) :
    ∃ K' : ℝ, ∀ x ∈ X.dom, g x ≤ K' * Real.exp (-(2 * (i : ℝ) * phiFD X th x)) := by
  obtain ⟨C, hC⟩ := phi_threshold X th h'
  refine ⟨|K| * Real.exp (2 * i * C), fun x hx => (hK x hx).trans ?_⟩
  rw [mul_assoc |K|, ← Real.exp_add]
  refine mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left (hC x) (show (0 : ℝ) ≤ 2 * i by positivity)
  linarith

theorem gap_of_adjacent {p : ℕ} (G L : Fin r → ℤ)
    (h : ∀ a b : Fin r, (b : ℕ) = a + 1 → (b : ℕ) ≠ p → G b + 2 * (L a - L b) ≤ G a) (a b : Fin r) (hab : a ≤ b)
    (hp : (b : ℕ) < p ∨ p ≤ (a : ℕ)) : G b + 2 * (L a - L b) ≤ G a := by
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h1 := ih (by omega) hn (by simp only at hp ⊢; omega)
    have h2 := h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl (by simp only at hp ⊢; omega)
    linarith

theorem gaps_all (X : Data E r) (L G : Wt X.Ψ r) (T : ℕ) (hL : IsStrictDom X L)
    (h : ∀ τ : X.Ψ, (∀ a b : Fin r, (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → G τ b + 2 * (L τ a - L τ b) ≤ G τ a) ∧
      ∀ a b : Fin r, (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → 19 * (T : ℤ) ≤ 10 * (L τ b - L τ a) ∧
        2 * (L τ ⟨r - 1, by have := a.2; omega⟩ - L τ ⟨0, by have := a.2; omega⟩) ≤
          G τ ⟨r - 1, by have := a.2; omega⟩ - G τ ⟨0, by have := a.2; omega⟩) :
    (∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) → G τ b ≤ G τ a) ∧
    (∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → 19 / 5 * (T : ℝ) ≤ ((G τ b : ℤ) : ℝ) - ((G τ a : ℤ) : ℝ) ∧
      19 / 10 * (T : ℝ) ≤ ((L τ b : ℤ) : ℝ) - ((L τ a : ℤ) : ℝ)) ∧
    ∀ s : ℝ, 0 ≤ s → s ≤ T → IsDominantR X fun τ a =>
      (G τ a : ℝ) - s * (de2W X τ a : ℝ) - 2 * (1 / 4) * (L τ a : ℝ) := by
  have hg : ∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) →
      G τ b + 2 * (L τ a - L τ b) ≤ G τ a ∧ L τ b ≤ L τ a := by
    intro τ a b hab hp
    refine ⟨gap_of_adjacent (G τ) (L τ) (h τ).1 a b hab hp, ?_⟩
    rcases hab.eq_or_lt with rfl | h'
    · exact le_rfl
    · rcases hp with hp | hp
      · exact ((hL τ).1 a b h' hp).le
      · exact ((hL τ).2.1 a b hp h').le
  have hn : ∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) →
      38 * (T : ℤ) ≤ 10 * (G τ b - G τ a) ∧ 19 * (T : ℤ) ≤ 10 * (L τ b - L τ a) ∧
        57 * (T : ℤ) ≤ 10 * (2 * (G τ b - G τ a) - (L τ b - L τ a)) := by
    intro τ a b ha hb
    have hr0 : 0 < r := by have := a.2; omega
    have hr1 : r - 1 < r := by omega
    obtain ⟨h1, h2⟩ := (h τ).2 a b ha hb
    obtain ⟨h3, -⟩ := (h τ).2 ⟨0, hr0⟩ ⟨r - 1, hr1⟩ (by simp only; omega) (by have := b.2; simp only; omega)
    obtain ⟨h4, h5⟩ := hg τ ⟨0, hr0⟩ a (Nat.zero_le _) (Or.inl ha)
    obtain ⟨h6, h7⟩ := hg τ b ⟨r - 1, hr1⟩ (by have := b.2; rw [Fin.le_def]; simp only; omega) (Or.inr hb)
    refine ⟨by linarith, h1, by linarith⟩
  refine ⟨fun τ a b hab hp => ?_, fun τ a b ha hb => ?_, fun s hs0 hs τ => ⟨fun a b hab hb => ?_, fun a b ha hab => ?_,
    fun a b ha hb => ?_⟩⟩
  · have := hg τ a b hab hp
    linarith [this.1, this.2]
  · obtain ⟨h1, h2, -⟩ := hn τ a b ha hb
    have h1' : 38 * (T : ℝ) ≤ 10 * ((G τ b : ℝ) - G τ a) := by exact_mod_cast h1
    have h2' : 19 * (T : ℝ) ≤ 10 * ((L τ b : ℝ) - L τ a) := by exact_mod_cast h2
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hg τ a b hab (Or.inl hb)
    have ha : (a : ℕ) < X.p0 := lt_of_le_of_lt hab hb
    have h1' : (G τ b : ℝ) + 2 * (L τ a - L τ b) ≤ G τ a := by exact_mod_cast h1
    have h2' : (L τ b : ℝ) ≤ L τ a := by exact_mod_cast h2
    simp only [de2W, if_neg (not_le.2 ha), if_neg (not_le.2 hb)]
    linarith
  · obtain ⟨h1, h2⟩ := hg τ a b hab (Or.inr ha)
    have hb : X.p0 ≤ (b : ℕ) := ha.trans hab
    have h1' : (G τ b : ℝ) + 2 * (L τ a - L τ b) ≤ G τ a := by exact_mod_cast h1
    have h2' : (L τ b : ℝ) ≤ L τ a := by exact_mod_cast h2
    simp only [de2W, if_pos ha, if_pos hb]
    linarith
  · obtain ⟨-, -, h3⟩ := hn τ a b ha hb
    have h3' : 57 * (T : ℝ) ≤ 10 * (2 * ((G τ b : ℝ) - G τ a) - (L τ b - L τ a)) := by exact_mod_cast h3
    simp only [de2W, if_neg (not_le.2 ha), if_pos hb]
    push_cast
    linarith

theorem margin_numbers {f r D T u : ℝ} (hf : 1 ≤ f) (hr : 8 ≤ r) (hD : 2 * D = f * (r * (r - 1))) (hT : 11 * D ^ 2 ≤ T)
    (hu0 : 0 ≤ u) (hu : 2 * u ≤ f * r) :
    4 * f * r ^ 2 < 5 * f * r ^ 2 ∧ 5 * f * r ^ 2 + 2 * T < 19 / 5 * T ∧
      (5 * f * r ^ 2) ^ 2 * u + 5 * f * r ^ 2 < 19 / 5 * T + D * (19 / 10 * T) ∧ 2 * r < 19 / 5 * T := by
  have hr0 : 0 < r := by linarith
  have hf0 : 0 < f := by linarith
  have hfr : 0 < f * r := by positivity
  have h1 : 7 * (f * r) ≤ 2 * D := by rw [hD]; nlinarith
  have hD0 : 0 < D := by linarith
  have h2 : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith [sq_nonneg r, mul_pos hf0 (pow_pos hr0 2)]
  have h3 : 49 * (f * r) ^ 2 ≤ 4 * D ^ 2 := by nlinarith
  have h4 : 0 < f * r ^ 2 := by positivity
  have h5 : r ≤ f * r ^ 2 := by nlinarith
  have h6 : 5 * r ^ 2 ≤ (r - 1) ^ 3 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 8 := ⟨r - 8, by ring⟩
    have hs : 0 ≤ s := by linarith
    nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]
  have h7 : 5 * r ^ 2 * (f * r) ^ 3 ≤ 8 * D ^ 3 := by
    have : 8 * D ^ 3 = (r - 1) ^ 3 * (f * r) ^ 3 := by
      rw [show 8 * D ^ 3 = (2 * D) ^ 3 by ring, hD]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  have h8 : (5 * f * r ^ 2) ^ 2 * (2 * u) ≤ (5 * f * r ^ 2) ^ 2 * (f * r) := mul_le_mul_of_nonneg_left hu (by positivity)
  have h9 : D * (11 * D ^ 2) ≤ D * T := mul_le_mul_of_nonneg_left hT hD0.le
  have h10 : 0 < D ^ 3 := by positivity
  refine ⟨by linarith, by linarith, by nlinarith, by linarith⟩

end Model

section Record

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have h' : Module.finrank ℚ D.host.E = 2 * D.R.f := by exact_mod_cast h
  omega

theorem f_pos (D : D7) : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity

theorem two_mul_half (p : ℕ) : (2 : ℝ) * ((p * (p - 1) / 2 : ℕ) : ℝ) = p * (p - 1) := by
  rw [← Nat.choose_two_right, Nat.cast_choose_two]; ring

include hj in
theorem two_mul_dimY : (2 : ℝ) * WeightFamilies.dimY D j = D.R.f * (D.R.r * (D.R.r - 1)) := by
  have hr : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.r, Ranks.sigW]; omega
  have h1 := two_mul_half (D.R.sigW j).1
  have h2 := two_mul_half (D.R.sigW j).2
  rw [hr, WeightFamilies.dimY]
  simp only [Nat.cast_mul, Nat.cast_add]
  linear_combination (D.R.f : ℝ) * h1 + (D.R.f : ℝ) * h2

theorem wt_ext {u v : WeightFamilies.Wt D j} (h1 : u.aP = v.aP) (h2 : u.aM = v.aM) (h3 : u.n = v.n) : u = v := by
  cases u; cases v; simp_all

def valAt (k : (T.U j T.σ₀).Comp) (x : ((T.U j T.σ₀).X k).dom) : T.R j →+* ℂ where
  toFun f := rdU (T.U j T.σ₀) f k x.1
  map_zero' := by rw [map_zero]; rfl
  map_add' f g := by rw [map_add]; rfl
  map_mul' f g := by rw [rdU_mul]; rfl
  map_one' := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom]
    exact congrArg (toC (σ := T.σ₀)) (evalAt_one _ _ ((T.U j T.σ₀).un k x) (h.unTest j hj T.σ₀ T.good_σ₀ k x))

theorem valAt_algebraMap (k : (T.U j T.σ₀).Comp) (x : ((T.U j T.σ₀).X k).dom) (a : T.Q.c.F) :
    valAt h j hj k x (algebraMap T.Q.c.F (T.R j) a) = T.σ₀ a := by
  have h1 : rdU (T.U j T.σ₀) 1 k x.1 = 1 := (valAt h j hj k x).map_one
  rw [Algebra.algebraMap_eq_smul_one]
  change rdU (T.U j T.σ₀) (a • 1) k x.1 = _
  rw [map_smulₛₗ]
  change T.σ₀ a * rdU (T.U j T.σ₀) 1 k x.1 = _
  rw [h1, mul_one]

include h hj in

theorem homRel_of_cusp (u : WeightFamilies.Wt D j) {m : ℕ} (hm : WeightFamilies.dimY D j + 2 ≤ m) (F : Fin m → T.R j)
    (hF : ∀ a, F a ∈ T.C j u) (k : (T.U j T.σ₀).Comp) (v : Fin m → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hv : ∀ a (x : ((T.U j T.σ₀).X k).dom), v a x.1 = valAt h j hj k x (F a)) :
    HomRel T.σ₀ ((T.U j T.σ₀).X k) v := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨Q, d, h1, h2, h3⟩ := GlobalTheory.SecRelation.exists_homogeneous_relation D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (wtA u) u.n m
    (by rw [finrank_host, hp, hq]; exact hm) F (fun a => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (hF a))
  refine ⟨Q, d, h1, h2, fun x hx => ?_⟩
  have h4 := congrArg (valAt h j hj k ⟨x, hx⟩) h3
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left] at h4
  rw [← h4]
  congr 1
  · ext a
    exact (valAt_algebraMap h j hj k _ a).symm
  · funext a
    exact hv a ⟨x, hx⟩

include h hj in
theorem pow_mem_cusp (u : WeightFamilies.Wt D j) {f : T.R j} (hf : f ∈ T.C j u) {n : ℕ} (hn : 1 ≤ n) :
    f ^ n ∈ T.C j (wsmul n u) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [pow_one, show wsmul 1 u = u from wt_ext j (by funext τ i; simp [wsmul]) (by funext τ i; simp [wsmul])
      (by simp [wsmul])]
    exact hf
  | succ n _ ih =>
    rw [pow_succ, show wsmul (n + 1) u = wadd (wsmul n u) u from
      wt_ext j (by funext τ i; simp [wsmul, wadd, add_mul]) (by funext τ i; simp [wsmul, wadd, add_mul])
        (by simp [wsmul, wadd, add_mul])]
    exact h.toLawsCore.mul j hj _ _ _ ih _ hf

end Record

theorem archAt_nonempty : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (CRm c : ℝ) (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (i : ℕ) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) (w1 w2 : WeightFamilies.Wt D j) (th1 : (recB h.toLawsCore).Cusp j w1) (th2 : (recB h.toLawsCore).Cusp j w2), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → j < D.R.m → 8 ≤ D.R.r → 0 < c → (Tn : ℝ) * c * g0 D ≤ 1 → 1 ≤ WeightFamilies.RRv D CRm → (D.R.r : ℝ) * (1 + WeightFamilies.c1 D CRm Tn c j / (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) ≤ 2 * Tn → 2 ≤ WeightFamilies.dimY D j → 0 < i → IsDoubledWeightWithShift wL w1 nW → IsG2 wL wF w2 → (∀ k : (T.U j T.σ₀).Comp, ∀ x ∈ ((T.U j T.σ₀).X k).dom, ∃ a, rdR h j (w a) k x ≠ 0) → (∀ k : (T.U j T.σ₀).Comp, ∃ x ∈ ((T.U j T.σ₀).X k).dom, rdR h j et k x ≠ 0) → (∀ k : (T.U j T.σ₀).Comp, ∃ x ∈ ((T.U j T.σ₀).X k).dom, rdR h j th1 k x ≠ 0) → (∀ k : (T.U j T.σ₀).Comp, ∃ x ∈ ((T.U j T.σ₀).X k).dom, rdR h j th2 k x ≠ 0) → (∀ k : (T.U j T.σ₀).Comp, ∃ G : (recB h.toLawsCore).Cusp j wF, ∃ x ∈ ((T.U j T.σ₀).X k).dom, rdR h j G k x ≠ 0) → (∀ k : (T.U j T.σ₀).Comp, ∃ th K : ℝ, 0 < th ∧ ∀ x ∈ ((T.U j T.σ₀).X k).dom, Real.exp (-(2 * c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j T.σ₀).X k) th x)) ≤ K * ∑ i, ((T.U j T.σ₀).X k).pnorm (laR T j wL k) (rdR h j (w i) k) x ^ 2) → (∀ k : (T.U j T.σ₀).Comp, ∃ th K : ℝ, 0 < th ∧ ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laR T j (etWt D j i) k) (rdR h j et k) x ^ 2 ≤ K * Real.exp (-(2 * (i : ℝ) * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j T.σ₀).X k) th x))) → (∀ k : (T.U j T.σ₀).Comp, BasePotentialExistence ((T.U j T.σ₀).X k) (de2W ((T.U j T.σ₀).X k)) D.R.r (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CRm Tn c j)) := by
  intro D T h j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 CRm c N w i et w1 w2 th1 th2 hP hjm hr hc hTc hRR hrr hD2 hi
    hG1 hG2 hw het hth1 hth2 hthp hI1 hI2 hPsi
  obtain ⟨R, e, hR⟩ := GlobalTheory.Shares.exists_isRdgU D T h j hj (SecNorm.sup _)
  have hSS := fun u => (GlobalTheory.Shares.span_readings_components D T h j hj _ R e hR u).2.2
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIsL, -, -, hT0, -, -, -, -, -, hT11, -⟩, -⟩ := id hP
  have hLn : wL.n = nW := hIsL.1
  have hf := f_pos D
  have hq : 0 < (D.R.sigW j).2 := by simp only [Ranks.sigW]; omega
  have hqr : (D.R.sigW j).2 < D.R.r := by
    have := hj.1; have := D.R.m_add_three_le_k
    simp only [Ranks.r, Ranks.sigW]; omega
  have hg2 : g0 D = 2 * (g0 D / 2) := by unfold g0; omega
  have hg1 : 1 ≤ g0 D / 2 := by unfold g0; omega
  have hn1 : 1 ≤ i * (g0 D / 2) := Nat.mul_pos hi hg1
  have hW1 : wadd w1 (wscalar D j 2 even_two) = wsmul 2 wL :=
    wt_ext j (by funext τ a; simp [wadd, wsmul, wscalar, hG1.2.1]) (by funext τ a; simp [wadd, wsmul, wscalar, hG1.2.2])
      (by simp [wadd, wsmul, wscalar, hG1.1, hLn])
  have hW2 : wadd w2 wF = wsmul (WeightFamilies.dimY D j + 4) wL :=
    wt_ext j (by funext τ a; exact hG2.2.1 τ a) (by funext τ a; exact hG2.2.2 τ a) hG2.1
  have hW3 : wadd (etWt D j i) (wsmul (i * (g0 D / 2)) w1) = wsmul (2 * (i * (g0 D / 2))) wL := by
    refine wt_ext j ?_ ?_ ?_
    · funext τ a; simp only [wadd, wsmul, wscalar, etWt, hG1.2.1]; ring
    · funext τ a; simp only [wadd, wsmul, wscalar, etWt, hG1.2.2]; ring
    · change g0 D * i + i * (g0 D / 2) * w1.n = 2 * (i * (g0 D / 2)) * wL.n
      have h1 := hG1.1
      rw [hLn, show 2 * (i * (g0 D / 2)) * nW = i * (g0 D / 2) * (2 * nW) by ring, ← h1]
      nth_rewrite 1 [hg2]
      ring
  have hc1 : (Tn : ℝ) * c * (2 * D.R.f) ≤ WeightFamilies.c1 D CRm Tn c j := by
    unfold WeightFamilies.c1 WeightFamilies.dP WeightFamilies.rho
    have a1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have a2 : (1 : ℝ) ≤ (D.R.sigW j).2 := by exact_mod_cast hq
    have a3 : (0 : ℝ) ≤ (Tn : ℝ) * c * (2 * D.R.f) := by positivity
    have a4 : (1 : ℝ) ≤ WeightFamilies.RRv D CRm * (D.R.f * ((D.R.sigW j).2 : ℝ) ^ 3) :=
      one_le_mul_of_one_le_of_one_le hRR (one_le_mul_of_one_le_of_one_le a1 (one_le_pow₀ a2))
    have := mul_le_mul_of_nonneg_left a4 a3
    push_cast
    linarith
  have hc1' : 0 < WeightFamilies.c1 D CRm Tn c j := lt_of_lt_of_le (by positivity) hc1
  have key : ∀ k : (T.U j T.σ₀).Comp, ∃ (Xa : ArchInM ((T.U j T.σ₀).X k)) (hN : Xa.N = N),
      Xa.L = laR T j wL k ∧ Xa.Fp = laR T j wF k ∧ Xa.T = Tn ∧ Xa.c1 = WeightFamilies.c1 D CRm Tn c j ∧
      (∀ a, Xa.w a = rdR h j (w (Fin.cast hN a)) k) ∧ RelIn T.σ₀ ((T.U j T.σ₀).X k) Xa ∧
      Margins ((T.U j T.σ₀).X k) Xa := by
    intro k
    obtain ⟨ladd, lsmul, -, let', hnd, hp0, hcard, tt, htt⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
    obtain ⟨hsL, hsL2, hgap⟩ := GlobalTheory.RunWeightDom.run_weight_dom D T h j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hjm hr k
    rw [← hnd] at hgap
    obtain ⟨g1, g2, g3⟩ := gaps_all _ _ _ Tn hsL hgap
    have hr0 : (0 : ℝ) < D.R.r := by positivity
    obtain ⟨q1, q2, q3⟩ := curvNumStatement_holds D.R.r ((T.U j T.σ₀).X k) (laR T j wL k) (de2W _) (laR T j wF k) Tn D.R.r
      (1 / 4) (by norm_num) hr0 (by positivity) hsL hsL2 (by
        rintro t (rfl | rfl)
        · exact g3 _ (by simp) (by simp)
        · exact g3 _ (by positivity) (le_of_eq (by field_simp)))
    have hde : laR T j (wscalar D j 2 even_two) k = de2W _ := by
      funext τ a
      rw [htt]
      simp [wscalar, ext0, de2W]
    have e1 : laR T j w1 k = 2 • laR T j wL k - de2W _ := by
      rw [← lsmul, ← hW1, ladd, hde, add_sub_cancel_right]
    have e2 : laR T j w2 k = (nd ((T.U j T.σ₀).X k) + 4) • laR T j wL k - laR T j wF k := by
      rw [← lsmul, hnd, ← hW2, ladd, add_sub_cancel_right]
    obtain ⟨th, K, hth, hK⟩ := hI1 k
    obtain ⟨th', K', hth', hK'⟩ := hI2 k
    obtain ⟨G, hG⟩ := hthp k
    obtain ⟨ps0, s1, s2, s3, s4⟩ := hPsi k
    have hfE : ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E = D.R.f := finrank_host D
    have hdisc : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    let Xa : ArchInM ((T.U j T.σ₀).X k) :=
      { L := laR T j wL k
        de := de2W _
        Fp := laR T j wF k
        T := Tn
        i := i
        g0 := g0 D
        N := N
        c := c
        c1 := WeightFamilies.c1 D CRm Tn c j
        a1 := 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f))
        rr := D.R.r
        n_ge := by rw [hnd]; exact hD2
        T_ge := by rw [hnd]; exact hT11
        i_pos := hi
        genus_pos := by omega
        c_pos := hc
        frame_theta_const_pos := hc1'
        frame_theta_weight_pos := by positivity
        rr_nonneg := hr0.le
        Tcg0 := hTc
        rr_le := hrr
        w := fun a => rdR h j (w a) k
        w_van := fun a => hSS wL (w a) k
        w_nz := hw k
        ph := ReciprocityTheory.ChartRestriction.G.I2.phiFD _ th
        ph_inv := phi_inv _ (by omega) th
        ph_nonneg := fun x _ => phi_nonneg _ th x
        p1 := phi_lower _ (by rw [hfE]; exact hf) hth
        p2 := fun x _ => by
          have a1 := mul_le_mul_of_nonneg_left (phi_le _ th x) (show 0 ≤ (Tn : ℝ) * c by positivity)
          rw [hfE, ← mul_div_assoc] at a1
          exact a1.trans (div_le_div_of_nonneg_right hc1 (sq_nonneg _))
        p3 := ⟨K, hK⟩
        et := rdR h j et k
        genus_even := ⟨g0 D / 2, by omega⟩
        et_sec := by rw [← let']; exact (hSS _ et k).1.1.1
        et_ne := het k
        p4 := by rw [← let']; exact decay_threshold _ th hth' i _ K' hK'
        th1 := rdR h j th1 k
        firstTheta_vanishes := by rw [← e1]; exact hSS _ th1 k
        firstTheta_ne_zero := hth1 k
        th2 := rdR h j th2 k
        secondTheta_vanishes := by rw [← e2]; exact hSS _ th2 k
        secondTheta_ne_zero := hth2 k
        thp := rdR h j G k
        thp_van := hSS _ G k
        thp_ne := hG
        ps0 := ps0
        potential_invariant := s1
        potential_smooth := s2
        base_psi_levi_lower_bound := s3
        base_psi_weighted_cf := s4
        posL := q1
        posLde := q2
        posF := ⟨1 / 4, by norm_num, q3⟩ }
    refine ⟨Xa, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ⟨fun jj => ?_, fun jj => ?_⟩, ?_⟩
    · exact homRel_of_cusp h j hj wL (by rw [hnd]) (fun a => (w (jj a)).1) (fun a => cutR_le T.C j _ (w (jj a)).2) k _
        fun _ _ => rfl
    · refine homRel_of_cusp h j hj (wsmul (2 * (i * (g0 D / 2))) wL) (by rw [hnd])
        (Fin.cons (et.1 * th1.1 ^ (i * (g0 D / 2))) fun a => (w (jj a)).1 ^ (2 * (i * (g0 D / 2)))) (fun a => ?_) k _
        fun a x => ?_
      · refine Fin.cases ?_ (fun a => ?_) a
        · rw [Fin.cons_zero, ← hW3]
          exact h.toLawsCore.mul j hj _ _ _ (cutR_le T.C j _ et.2) _ (pow_mem_cusp h j hj _ (cutR_le T.C j _ th1.2) hn1)
        · rw [Fin.cons_succ]
          exact pow_mem_cusp h j hj _ (cutR_le T.C j _ (w (jj a)).2) (by omega)
      · refine Fin.cases ?_ (fun a => ?_) a
        · rw [Fin.cons_zero, Fin.cons_zero, map_mul, map_pow]; rfl
        · rw [Fin.cons_succ, Fin.cons_succ, map_pow]; rfl
    · have hu : 2 * (D.R.f * min (D.R.sigW j).2 (D.R.r - (D.R.sigW j).2)) ≤ D.R.f * D.R.r := by
        rw [mul_left_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      obtain ⟨m1, m2, m3, m4⟩ := margin_numbers (f := D.R.f) (r := D.R.r) (D := WeightFamilies.dimY D j) (T := Tn)
        (u := ((D.R.f * min (D.R.sigW j).2 (D.R.r - (D.R.sigW j).2) : ℕ) : ℝ)) (by exact_mod_cast hf)
        (by exact_mod_cast hr) (two_mul_dimY j hj) (by exact_mod_cast hT11) (Nat.cast_nonneg _) (by exact_mod_cast hu)
      refine GlobalTheory.Shares.margins_of_gaps _ _ _ Xa (by rw [hp0]; exact hq) (by rw [hp0]; exact hqr)
        (by obtain ⟨τ, hτ⟩ := Finset.card_pos.1 (hcard.symm ▸ hf); exact ⟨⟨τ, hτ⟩⟩) rfl hsL g1
        (5 * D.R.f * (D.R.r : ℝ) ^ 2) (19 / 5 * Tn) (19 / 10 * Tn) (by rw [hcard]; exact m1) g2 m2 ?_ m4
      rw [hcard, hp0, hnd]
      exact m3
  choose Xa hN h1 h2 h3 h4 h5 h6 h7 using key
  exact ⟨⟨Xa, fun k => (GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k).2.2.2.2.1, hN, h1, h2, h3, h4, h5, h6, h7⟩⟩

end GlobalTheory.ArchInputs
