import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoEigOrth

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace LagrangeInterpolation

theorem aeval_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (C : E →L[ℂ] E) (d : ℂ) (v : E)
    (hv : C v = d • v) (p : Polynomial ℂ) : Polynomial.aeval C p v = p.eval d • v := by
  have hpow : ∀ n : ℕ, (C ^ n) v = d ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, ContinuousLinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ContinuousLinearMap.mul_apply, hpow,
      Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul]

def lagP {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) (ρ : ι) : Polynomial ℂ :=
  ∏ σ ∈ bad ρ, (Polynomial.C (c ρ - d σ)⁻¹ * (Polynomial.X - Polynomial.C (d σ)))

theorem lagrangePoly_eval_eq_zero_of_mem {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (hb : σ ∈ bad ρ) : (lagP c d bad ρ).eval (d σ) = 0 := by
  rw [lagP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hb (by simp)

theorem lagrangePoly_eval_eq_one {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (h : d σ = c ρ) (hne : ∀ τ ∈ bad ρ, d τ ≠ c ρ) : (lagP c d bad ρ).eval (d σ) = 1 := by
  rw [lagP, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun τ hτ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [h]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne τ hτ).symm)

def qP (P : M.Par) (ρ : M.Ty P) : Polynomial ℂ :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((M.rho P ρ i : ℝ) : ℂ))

theorem eval_qP (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (qP P ρ).eval Y = M.xC P ρ Y := by
  rw [qP, Polynomial.eval_prod]
  simp [M.xC]

theorem generic (P : M.Par) : ∃ Y : ℂ, ∀ (ρ : M.Ty P) (σ : M.Ty (Qx8.P2 P)),
    (∃ Y', M.xC (Qx8.P2 P) σ Y' ≠ M.xC P ρ Y') → M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y := by
  classical
  let D : Polynomial ℂ := ∏ ρ : M.Ty P, ∏ σ : M.Ty (Qx8.P2 P),
    (if qP (Qx8.P2 P) σ = qP P ρ then 1 else qP (Qx8.P2 P) σ - qP P ρ)
  have hD : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ _ => Finset.prod_ne_zero_iff.mpr fun σ _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · exact sub_ne_zero.mpr h
  obtain ⟨Y, hY⟩ : ∃ Y, D.eval Y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hD (Polynomial.funext fun y => by rw [hcon y, Polynomial.eval_zero])
  refine ⟨Y, fun ρ σ hex hEq => ?_⟩
  obtain ⟨Y', hY'⟩ := hex
  have hne : qP (Qx8.P2 P) σ ≠ qP P ρ := fun h => hY' (by rw [← eval_qP, ← eval_qP, h])
  apply hY
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ ρ) ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
  rw [if_neg hne, Polynomial.eval_sub, eval_qP, eval_qP, hEq, sub_self]

end LagrangeInterpolation

open LagrangeInterpolation in
theorem lagrange_annihilation : Lagrange := by
  classical
  intro hE P hOK hk
  have hOK2 : (Qx8.P2 P).OK := by
    unfold Qx8.P2
    refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u, fun i hmem => ?_⟩
    have g := hOK.gap i hmem
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at g ⊢
    linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1)), min_le_left (P.u i) (P.u' i)]
  obtain ⟨Y, hY⟩ := generic P
  refine ⟨Y + ((P.k : ℂ) - 2) / 2, fun ρ => lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
    (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ, ?_⟩
  intro Wp _ _ _ z e π hz hT hπ he hez hee Fr hFr C hC ρ
  obtain ⟨S, hSi, -, hSc⟩ := branching_proof Wp (Qx8.P2 P) hOK2 rfl z e π hz hT hπ he hez hee
  have hSv : ∀ σ, ∀ v ∈ S σ, ∀ Fr' : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr' →
      ∀ w', capRep P.k P.r π Fr' w' v = M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ v hv Fr' hFr' w' => hSc Fr' hFr' σ w' v hv
  have hCv : ∀ σ, ∀ v ∈ S σ, C v = M.xC (Qx8.P2 P) σ Y • v := by
    intro σ v hv
    rw [hC, hSv σ v hv Fr hFr, add_sub_cancel_right]
  have hKs : ∀ σ, ∀ v ∈ S σ,
      v ∈ Kset P.k P.r z e π (fun w' => M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2)) :=
    fun σ v hv Fr' hFr' w' => hSv σ v hv Fr' hFr' w'
  have hRep : Qr.IsRepW P.k P.r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  have hOrth : ∀ σ, M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)))ᗮ := by
    intro σ hne v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hu
    · exact hE Wp P.k P.r z e π hz hT hRep hπ.2.2.2.1 ⟨Fr, hFr⟩ _ _ x v hx (hKs σ v hv)
        ⟨Y + ((P.k : ℂ) - 2) / 2, by simpa using hne.symm⟩
    · exact inner_zero_left _
    · rw [inner_add_left, hx, hy, add_zero]
    · rw [inner_smul_left, hx, mul_zero]
  have hIn : ∀ σ, M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)) := by
    intro σ heq v hv
    have hfun : ∀ Y', M.xC (Qx8.P2 P) σ Y' = M.xC P ρ Y' := by
      by_contra hc
      push_neg at hc
      exact hY ρ σ hc heq
    refine Submodule.subset_span (fun Fr' hFr' w' => ?_)
    show capRep P.k P.r π Fr' w' v = M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2) • v
    rw [hSv σ v hv Fr' hFr' w', hfun]
  ext v
  have hv : v ∈ ⨆ σ, S σ := by
    rw [hSi.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun x =>
    (Polynomial.aeval C) (lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
      (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ) x =
    (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection x) hv ?_ ?_ ?_
  · intro σ x hx
    rw [aeval_eig C _ x (hCv σ x hx)]
    by_cases hb : M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y
    · rw [lagrangePoly_eval_eq_one (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) hb (fun τ hτ => (Finset.mem_filter.mp hτ).2), one_smul]
      exact ((Submodule.starProjection_eq_self_iff).mpr (hIn σ hb x hx)).symm
    · rw [lagrangePoly_eval_eq_zero_of_mem (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩), zero_smul]
      exact ((Submodule.starProjection_apply_eq_zero_iff _).mpr (hOrth σ hb x hx)).symm
  · simp only [map_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
