import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransferStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultLiftDividedPowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountConjIdealEqCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchEmbeddingConjByAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOfPartialDerivativeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ListProdUpdateConjugateStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThKAutV.Smooth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_list_prod_mat {k N : ℕ} {ι : Type} (l : List ι) (f : ι → (Fin k → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ fun t => (l.map fun i => f i t).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf i List.mem_cons_self).mul (ih fun j hj => hf j (List.mem_cons_of_mem _ hj))

theorem contDiff_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ (c • G.W.J.map σ)), (∀ i, IsRealLine σ (c • G.W.J.map σ) (γ i)) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (g * (List.ofFn fun i => γ i (t i)).prod)) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcc Φ hΦ k γ hγ g
  have hcm : IsCMExt F E σ := hT.base.cm
  haveI : CompleteSpace (Matrix (Fin (a + a')) (Fin (a + a')) ℂ) := FiniteDimensional.complete ℝ _
  let J' := c • G.W.J.map σ
  let FF : ((Fin a × Fin (a + a') → AF F) → ℂ) → GAd σ J' → ℂ :=
    fun Ψ x => G.M.I om Ψ ((toGAd hσ G.W.J hc).symm x)
  let P : (Fin k → ℝ) → GAd σ J' := fun t => (List.ofFn fun i => γ i (t i)).prod
  let S : Set ((Fin k → ℝ) → ℂ) := {f | ∃ Ψ ∈ GlobalTheory.ThK.PolData B G.M, f = fun t => FF Ψ (g * P t)}
  have hP : Continuous P := by
    have e : P = fun t => ((List.finRange k).map fun i => γ i (t i)).prod := by
      funext t; simp [P, List.ofFn_eq_map]
    rw [e]
    exact continuous_list_prod (f := fun (i : Fin k) (t : Fin k → ℝ) => γ i (t i)) _ fun i _ =>
      (GlobalTheory.T.real_line_continuous F E σ hcm _ J' (γ i) (hγ i)).comp (continuous_apply i)
  refine GlobalTheory.T.cont_diff_of_partial_derivative_closure k S ?_ ?_ _ ⟨Φ, hΦ, rfl⟩
  · rintro f ⟨Ψ, hΨ, rfl⟩
    exact (GlobalTheory.T.continuous_theta_lift_transfer F E σ hσ B a a' G X om om' hK hT c hc hcc Ψ hΨ).comp (continuous_const.mul hP)
  · rintro f ⟨Ψ, hΨ, rfl⟩ j
    obtain ⟨w, τ, Z, -, hZ⟩ := hγ j
    obtain ⟨D, hDP, hDd⟩ := GlobalTheory.T.polynomial_theta_archimedean_lie_action F E σ hσ B a a' G X om om' hK hT c hc hcc w τ
    let A : GAd σ J' →* Matrix (Fin (a + a')) (Fin (a + a')) ℂ := (GlobalTheory.Orb.archMat σ J' τ).comp (projArch σ J' w)
    let suf : (Fin k → ℝ) → GAd σ J' := fun t => (List.ofFn fun i => if j < i then γ i (t i) else 1).prod
    let Zt : (Fin k → ℝ) → Matrix (Fin (a + a')) (Fin (a + a')) ℂ := fun t => A (suf t)⁻¹ * Z * A (suf t)
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin (a + a')) (Fin (a + a')) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    have hA : ContDiff ℝ ∞ fun t => A (suf t) := by
      choose Zi hZi using fun i => GlobalTheory.UAut.Model.exists_exp hcm τ (hγ i)
      have e : (fun t => A (suf t)) = fun t => ((List.finRange k).map fun i =>
          (if j < i then NormedSpace.exp (t i • Zi i) else 1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)).prod := by
        funext t
        simp only [suf, List.ofFn_eq_map, map_list_prod, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply]
        split_ifs
        · exact hZi i (t i)
        · exact map_one A
      rw [e]
      refine contDiff_list_prod_mat _ _ fun i _ => ?_
      by_cases h : j < i
      · simp only [h, if_true]
        exact hexp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
      · simp only [h, if_false]
        exact contDiff_const
    have hinv : ∀ t, A (suf t)⁻¹ = Ring.inverse (A (suf t)) := fun t => by
      rw [← MonoidHom.coe_toHomUnits A (suf t), Ring.inverse_unit, ← map_inv, MonoidHom.coe_toHomUnits]
    have hAi : ContDiff ℝ ∞ fun t => A (suf t)⁻¹ := by
      simp only [hinv]
      refine contDiff_iff_contDiffAt.2 fun t => ?_
      have h1 := contDiffAt_ringInverse ℝ (n := ∞) (A.toHomUnits (suf t))
      rw [MonoidHom.coe_toHomUnits] at h1
      exact h1.comp t hA.contDiffAt
    have hZt : ContDiff ℝ ∞ Zt := (hAi.mul contDiff_const).mul hA
    let bm : Fin (a + a') × Fin (a + a') × Bool → Matrix (Fin (a + a')) (Fin (a + a')) ℂ :=
      fun x => Matrix.single x.1 x.2.1 (if x.2.2 then Complex.I else 1)
    let cf : Fin (a + a') × Fin (a + a') × Bool → (Fin k → ℝ) → ℝ :=
      fun x t => if x.2.2 then (Zt t x.1 x.2.1).im else (Zt t x.1 x.2.1).re
    have hcf : ∀ x, ContDiff ℝ ∞ fun t => ((cf x t : ℝ) : ℂ) := by
      intro x
      have he : ContDiff ℝ ∞ fun t => Zt t x.1 x.2.1 :=
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ x.1 x.2.1)).contDiff.comp hZt
      rcases x with ⟨p, q, b⟩
      cases b
      · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp he)
      · exact Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp he)
    have hZe : ∀ t, Zt t = ∑ x, cf x t • bm x := by
      intro t
      ext p q
      simp only [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.smul_apply, bm, cf,
        Matrix.single_apply, if_true, Bool.false_eq_true, if_false]
      simp [Finset.sum_add_distrib, Complex.real_smul, ite_and]
      conv_lhs => rw [← Complex.re_add_im (Zt t p q)]
      ring
    refine ⟨Fin (a + a') × Fin (a + a') × Bool, inferInstance, fun x t => (cf x t : ℂ),
      fun x t => FF (D (bm x) Ψ) (g * P t), hcf, fun x => ⟨_, hDP _ Ψ hΨ, rfl⟩, fun t => ?_⟩
    let γ' : ℝ → GAd σ J' := fun s => (suf t)⁻¹ * γ j s * suf t
    have hγe : ∀ s, ∃ y, γ' s = embArch σ J' w ((projArch σ J' w (suf t))⁻¹ * y * projArch σ J' w (suf t)) ∧
        GlobalTheory.Orb.archMat σ J' τ y = NormedSpace.exp (s • Z) := by
      intro s
      obtain ⟨y, hy, hy2⟩ := hZ s
      exact ⟨y, by simp only [γ']; rw [hy]; exact GlobalTheory.T.arch_embedding_conj_by_adelic F E σ _ J' w y (suf t), hy2⟩
    have h1 : ∀ s, embArch σ J' w (projArch σ J' w (γ' s)) = γ' s := by
      intro s
      obtain ⟨y, hy, -⟩ := hγe s
      rw [hy, projArch_embArch_self]
    have h2 : ∀ s, GlobalTheory.Orb.archMat σ J' τ (projArch σ J' w (γ' s)) = NormedSpace.exp (s • Zt t) := by
      intro s
      obtain ⟨y, hy, hy2⟩ := hγe s
      rw [hy, projArch_embArch_self, map_mul, map_mul, hy2]
      let Ui : (Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ˣ := A.toHomUnits (suf t)⁻¹
      have hU1 : (Ui : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) = A (suf t)⁻¹ := MonoidHom.coe_toHomUnits _ _
      have hU2 : ((Ui⁻¹ : (Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ˣ) : Matrix _ _ ℂ) = A (suf t) := by
        simp only [Ui]
        rw [← map_inv, inv_inv, MonoidHom.coe_toHomUnits]
      have e1 : s • Zt t = (Ui : Matrix _ _ ℂ) * (s • Z) * ((Ui⁻¹ : (Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ˣ) : Matrix _ _ ℂ) := by
        rw [hU1, hU2]
        simp only [Zt, smul_mul_assoc, mul_smul_comm]
      rw [e1, Matrix.exp_units_conj, hU1, hU2]
      simp only [A, MonoidHom.comp_apply, map_inv]
    have hPs : ∀ s, g * P (t + s • Pi.single j 1) = g * P t * γ' s := by
      intro s
      have e1 : (fun i => γ i ((t + s • (Pi.single j 1 : Fin k → ℝ)) i)) =
          Function.update (fun i => γ i (t i)) j (γ j (t j) * γ j s) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [GlobalTheory.T.real_line_one_parameter_homomorphism F E σ hcm _ J' (γ i) (hγ i)]
        · simp [hi, Function.update_of_ne hi]
      simp only [P, γ', suf, e1, GlobalTheory.T.list_prod_update_conjugate, mul_assoc]
    have hd := hDd (Zt t) γ' h1 h2 Ψ hΨ (g * P t)
    have hval : G.M.I om (D (Zt t) Ψ) ((toGAd hσ G.W.J hc).symm (g * P t)) =
        ∑ x, (cf x t : ℂ) * FF (D (bm x) Ψ) (g * P t) := by
      have e2 : D (Zt t) Ψ = ∑ x, (cf x t : ℂ) • D (bm x) Ψ := by
        rw [hZe t, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        funext y
        simp [Complex.real_smul]
      rw [e2]
      exact GlobalTheory.T.theta_integral_linear_combination F E σ B a a' G X om om' hK hT _ _ _ (fun x => hDP _ Ψ hΨ) _
    rw [← hval]
    refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [FF, hPs]

end GlobalTheory.ThKAutV.Smooth
