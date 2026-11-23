import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomVMul

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem nf_coef_unique {E : Type*} [AddCommGroup E] [Module ℂ E] (M : ℕ) (a : ℕ → E) (S : Set ℂ)
    (hS : S.Infinite) (h : ∀ s ∈ S, ∑ i ∈ Finset.range M, s ^ i • a i = 0) : ∀ i < M, a i = 0 := by
  intro i hi
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a i)).mp fun f => ?_
  have hp : (∑ j ∈ Finset.range M, Polynomial.C (f (a j)) * Polynomial.X ^ j) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ hS
    intro s hs
    have hfs := congrArg f (h s hs)
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hfs
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfs]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q i) hp
  simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mpr hi] using hc

section scoef

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_sum_pad {E : Type*} [AddCommGroup E] [Module ℂ E] {Q M : ℕ} (hQ : Q + 1 ≤ M) (x : ℂ)
    (u : Fin (Q + 1) → E) :
    ∑ i ∈ Finset.range M, x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) = ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
  have h1 : ∑ i ∈ Finset.range (Q + 1), x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) =
      ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [q.isLt]
  rw [← h1]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hi' : ¬ i < Q + 1 := by simpa using hi
    rw [dif_neg hi', smul_zero]

theorem nf_scoef_unique (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q Q' : ℕ}
    {L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq} {L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq}
    (hS : IsSCoef p w e Q L) (hS' : IsSCoef p w e Q' L') (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (g : B.Mat P.k P.r) (hg : g ∈ C6.domL p.T.base ∅) (qq : Fin (Q + 1)) :
    B.opApply (L qq) F g = if h : (qq : ℕ) ≤ Q' then B.opApply (L' ⟨qq, by omega⟩) F g else 0 := by
  have hq1 : Q + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_left _ _)
  have hq2 : Q' + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_right _ _)
  have key : ∀ s : ℝ, ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g =
      ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g := by
    intro s
    have h1 := hS s F hF g hg
    have h2 := hS' s F hF g hg
    rw [h1] at h2
    simpa [Complex.ofReal_pow] using h2
  have hz := nf_coef_unique (max Q Q' + 1)
    (fun i => (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) -
      (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0))
    (Set.range (fun s : ℝ => (s : ℂ))) (Set.infinite_range_of_injective Complex.ofReal_injective) ?_ qq
    (lt_of_lt_of_le qq.isLt hq1)
  · simp only [sub_eq_zero] at hz
    rw [dif_pos qq.isLt] at hz
    by_cases hq : (qq : ℕ) ≤ Q'
    · rw [dif_pos hq]
      rw [dif_pos (by omega : (qq : ℕ) < Q' + 1)] at hz
      exact hz
    · rw [dif_neg hq]
      rw [dif_neg (by omega : ¬ (qq : ℕ) < Q' + 1)] at hz
      exact hz
  · rintro _ ⟨s, rfl⟩
    have e1 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g :=
      nf_sum_pad hq1 (s : ℂ) (fun q => B.opApply (L q) F g)
    have e2 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g :=
      nf_sum_pad hq2 (s : ℂ) (fun q => B.opApply (L' q) F g)
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [e1, e2, key s, sub_self]

end scoef

section extract

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_xD_pow (b : ℕ) : xD (fun x : ℝ => x ^ b) = fun x => (b : ℝ) * x ^ b := by
  funext x
  show x * deriv (fun x : ℝ => x ^ b) x = (b : ℝ) * x ^ b
  rw [(hasDerivAt_pow b x).deriv]
  rcases b with _ | b
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem nf_xD_const_mul (c : ℝ) (φ : ℝ → ℝ) : xD (fun x => c * φ x) = fun x => c * xD φ x := by
  funext x
  show x * deriv (fun x => c * φ x) x = c * (x * deriv φ x)
  rw [deriv_const_mul_field]
  ring

theorem nf_xD_iter_pow (b q : ℕ) : xD^[q] (fun x : ℝ => x ^ b) = fun x => (b : ℝ) ^ q * x ^ b := by
  induction q with
  | zero => funext x; simp
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := nf_xD_const_mul ((b : ℝ) ^ q) (fun x => x ^ b)
    rw [h1, nf_xD_pow]
    funext x
    push_cast
    ring

private theorem sum_pow_mul_choose_eq_add_pow (Q' p₀ : ℕ) (s : ℂ) (j : Fin (Q' + 1)) :
    ∑ q : Fin (Q' + 1), s ^ (q : ℕ) * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ) =
      ((p₀ : ℂ) + s) ^ (j : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => s ^ q * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)),
    show (p₀ : ℂ) + s = s + p₀ from add_comm _ _, add_pow]
  have hterm : ∀ m, s ^ m * ((Nat.choose j m * p₀ ^ ((j : ℕ) - m) : ℕ) : ℂ) =
      s ^ m * (p₀ : ℂ) ^ ((j : ℕ) - m) * (Nat.choose j m : ℂ) := by
    intro m
    push_cast
    ring
  simp only [hterm]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hji : (j : ℕ) < i := by simpa using hi
    simp [Nat.choose_eq_zero_of_lt hji]

private theorem coeff_eq_zero_of_sum_pow_smul_eq_zero_nat {E : Type*} [AddCommGroup E] [Module ℂ E] {Q' : ℕ}
    (w : Fin (Q' + 1) → E) (h : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) • w q = 0)
    (qq : Fin (Q' + 1)) : w qq = 0 := by
  have hS : (Set.range (Nat.cast : ℕ → ℂ)).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have := nf_coef_unique (Q' + 1) (fun i => if hi : i < Q' + 1 then w ⟨i, hi⟩ else 0) _ hS
    (fun x hx => by
      obtain ⟨s, rfl⟩ := hx
      rw [nf_sum_pad le_rfl]
      exact h s) qq qq.isLt
  simpa [Nat.lt_succ_iff.mp qq.isLt] using this

theorem nf_vExtract (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q' : ℕ}
    (L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq) (CcL : ℝ)
    (hLe : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
      B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
        p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
          ∑ q : Fin (Q' + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L' q) F) γ)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcc : ∀ m : ℕ, B.InCC A₀ m f)
    (hthr : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ))
    (γ : C.LPt) (hl : D.IsLocPt γ (P.r + 1)) (hG : 0 < TBB.Gp p γ) (qq : Fin (Q' + 1)) :
    p.V (B.opApply (L' qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j qq * p₀ ^ ((j : ℕ) - qq) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ := by
  have hfp := fpm_id p f p₀
  rw [hfp]
  have hthr0 : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ := hthr.trans (sub_le_self _ (Nat.cast_nonneg _))
  have hck : B.CkOn ⊤ (B.GV P.k P.r)
      (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) :=
    ckOn_Gpow_smul _ _ p₀ hf
  have hcc' := inCC_fpm_id p p₀ hcc
  rw [hfp] at hcc'
  have hG0 : ((TBB.Gp p γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have hsum_c : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((p₀ : ℂ) + s) ^ (j : ℕ)) • p.V (B.opApply (L' j) f) γ := by
    intro s
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_pow_mul_choose_eq_add_pow Q' p₀ (s : ℂ) j, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  have key : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (p.V (B.opApply (L' q) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g)) γ -
        ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
          (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) = 0 := by
    intro s
    have e1 := hLe (fun x => x ^ s) (contDiff_id.pow s) _ _ hck hcc' hthr γ hl hG
    have e2 := hLe (fun x => x ^ (p₀ + s)) (contDiff_id.pow _) f A₀ hf hcc hthr0 γ hl hG
    simp only [nf_xD_iter_pow] at e1 e2
    have hH : (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ s : ℝ) : ℂ) •
        ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) =
        (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ (p₀ + s) : ℝ) : ℂ) • f g) := by
      funext g
      rw [smul_smul, ← Complex.ofReal_mul, ← pow_add, add_comm]
    rw [hH, e2] at e1
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hsum_c s, sub_eq_zero]
    apply smul_right_injective _ (pow_ne_zero s hG0)
    simp only [Finset.smul_sum, smul_smul]
    have h3 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s * (s : ℂ) ^ (x : ℕ) =
        (((s : ℝ) ^ (x : ℕ) * TBB.Gp p γ ^ s : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    have h4 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s *
        (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) * ((p₀ : ℂ) + s) ^ (x : ℕ)) =
        (((((p₀ + s : ℕ) : ℝ)) ^ (x : ℕ) * TBB.Gp p γ ^ (p₀ + s) : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    simp only [h3, h4]
    exact e1.symm
  have := coeff_eq_zero_of_sum_pow_smul_eq_zero_nat _ key qq
  exact sub_eq_zero.mp this

end extract

end

end Formalism.FourierDecayAlt.P.CutBP
