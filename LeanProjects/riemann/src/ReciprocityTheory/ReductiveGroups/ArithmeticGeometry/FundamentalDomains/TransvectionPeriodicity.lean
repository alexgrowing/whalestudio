import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.AdmissibleHermitianColumns

namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]

lemma cR_neg (p : X.Ψ → ℝ) : cR X (-p) = -cR X p := by
  funext τ
  simp [cR]

lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
