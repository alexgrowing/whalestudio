import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutationStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top SheetDecomposition

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem herm_ext {A B : HermLine J} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem comb_some {σ : Type} [Fintype σ] (c₀ : HermLine J) (l : σ → HermLine J) (n : σ → ℤ) :
    combLine (fun o : Option σ => o.elim c₀ l) (fun o => o.elim 0 n) = combLine l n :=
  herm_ext (by simp [combLine, Fintype.sum_option]) (by funext z; simp [combLine, Fintype.prod_option])

theorem comb_none {σ : Type} [Fintype σ] (c₀ : HermLine J) (l : σ → HermLine J) :
    combLine (fun o : Option σ => o.elim c₀ l) (fun o => o.elim 1 0) = c₀ :=
  herm_ext (by simp [combLine, Fintype.sum_option]) (by funext z; simp [combLine, Fintype.prod_option])

theorem pts_deg (hI : PB.Inputs) {P : Ideal (MRing J)} {e : ℕ} (hP : IsArithVar P (e + 1)) {L L' : Fin e → HermLine J}
    (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j)) (h : ∀ j, (L j).a = (L' j).a) :
    ptsIntegral (e := e) P (fun i z => Real.log ((L i).h z)) (fun _ => 1) =
      ptsIntegral (e := e) P (fun i z => Real.log ((L' i).h z)) (fun _ => 1) := by
  have h1 := hI.degree K J P e L 2 hP hL Nat.prime_two
  have h2 := hI.degree K J P e L' 2 hP hL' Nat.prime_two
  simp only [h] at h1
  exact h1.trans h2.symm

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def gapc (c : Ψ × Fin N → ℤ) (r : Ψ × Fin N) : ℤ := (if h : (r.2 : ℕ) + 1 < N then c (r.1, ⟨r.2 + 1, h⟩) else 0) - c r

theorem sum_gapc {A : Type} [AddCommGroup A] (c : Ψ × Fin N → ℤ) (x : Ψ × Fin N → A) :
    ∑ r, gapc c r • -∑ k ∈ Finset.Iic r.2, x (r.1, k) = ∑ r, c r • x r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  let c' : ℕ → ℤ := fun i => if h : i < N then c (τ, ⟨i, h⟩) else 0
  have h1 : ∀ i : Fin N, gapc c (τ, i) = c' (i + 1) - c' i := fun i => by simp [gapc, c']
  have h2 : ∀ k : Fin N, ∑ i : Fin N, (if k ≤ i then gapc c (τ, i) else 0) = -c (τ, k) := fun k => by
    have h3 := Finset.sum_Ico_sub c' k.2.le
    have h4 : ∑ i : Fin N, (if k ≤ i then gapc c (τ, i) else 0) =
        ∑ i ∈ Finset.range N, if (k : ℕ) ≤ i then c' (i + 1) - c' i else 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => if (k : ℕ) ≤ i then c' (i + 1) - c' i else 0)]
      simp only [h1, Fin.le_def]
    rw [h4, ← Finset.sum_filter, show (Finset.range N).filter (fun i => (k : ℕ) ≤ i) = Finset.Ico (k : ℕ) N by
      ext i; simp [and_comm], h3]
    simp [c']
  calc ∑ i, gapc c (τ, i) • -∑ k ∈ Finset.Iic i, x (τ, k)
      = ∑ i, ∑ k, -((if k ≤ i then gapc c (τ, i) else 0) • x (τ, k)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_neg, Finset.smul_sum, Finset.sum_neg_distrib, show Finset.Iic i = Finset.univ.filter (· ≤ i) by ext; simp,
          Finset.sum_filter]
        simp only [ite_smul, zero_smul]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_neg_distrib, ← Finset.sum_smul, h2, neg_smul, neg_neg]

variable (M : RootModel Ψ N) {II : IntersectionSystem}

theorem line_smooth (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j
  exacts [M.A_smooth, M.x_smooth _ _]

theorem arFun_word (hII : IsFullIntersectionSystem II) (t : ℝ) (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    M.arFun II t (toA (∏ j, X (w j))) * M.δ = II M.K M.ι M.P (dimFl Ψ N + 1) fun j => M.x t (w j) := by
  classical
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  obtain ⟨h2, -, -, h4⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 M.K M.ι M.P _ _ (M.line t) (fun j => some (w j)) M.arith (line_smooth M t)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.arFun, Module.Basis.constr_basis, RootModel.arMono, if_pos h2, h3, pow_zero, mul_one,
    div_mul_cancel₀ _ hδ, h4]
  rfl

theorem arFun_prod (hII : IsFullIntersectionSystem II) (t : ℝ) {d : ℕ} (hd : d = dimFl Ψ N + 1) (c : Fin d → Ψ × Fin N → ℤ) :
    M.arFun II t (toA (∏ j, ∑ x, c j x • X x)) * M.δ = II M.K M.ι M.P d fun j => combLine (M.x t) (c j) := by
  classical
  subst hd
  rw [GlobalTheory.T.arith_intersection_multilinear_all II hII M.K M.ι M.P _ _ (M.x t) c M.arith (M.x_smooth t), Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _
  rw [h2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, smul_eq_mul, mul_assoc, arFun_word M hII, Int.cast_prod]

theorem geoFun_pts (hI : PB.Inputs) (t : ℝ) {d : ℕ} (hd : d = dimFl Ψ N) (c : Fin d → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      ptsIntegral (e := d) M.P (fun j z => Real.log ((combLine (M.x t) (c j)).h z)) fun _ => 1 := by
  classical
  subst hd
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P _ (fun j => combLine (M.x t) (c j)) M.arith
    fun j => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ _).1 (M.x_smooth t)
  refine (geoFun_prod M hI c).trans (Eq.trans ?_ h.symm)
  simp only [combLine, M.x_deg]

theorem tendsto_arFun (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have e : (monomial m a : RPA Ψ N) = a • basisMonomials (Option (Ψ × Fin N)) ℝ m := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    obtain ⟨L, hL⟩ := h m
    simp only [e, map_smul, RootModel.arFun, RootModel.PP, Module.Basis.constr_basis, hL.limUnder_eq]
    exact hL.const_smul a
  | add p q hp hq => simpa only [map_add] using hp.add hq

theorem test_factor' [DecidableEq Ψ] {p q n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (testPoly p : RP Ψ (p + q)) =
      ∏ j : Fin (n + 1 + r), ∑ x, Fin.append (fun _ : Fin (n + 1) => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have h := test_factor e hq hn
  rw [Fin.prod_univ_add] at h ⊢
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h ⊢
  rw [testPoly, pow_succ', mul_assoc, h, pow_succ', mul_assoc, sum_muCoef, muSmall, if_pos (by omega)]

end LevelTowerAlt.Comparison₂
