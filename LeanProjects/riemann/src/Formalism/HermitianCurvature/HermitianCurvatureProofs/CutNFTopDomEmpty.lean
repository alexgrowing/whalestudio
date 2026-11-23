import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section mul

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nfMulOp (c : B.Mat k r → ℂ) : B.DiffOp k r Wp Wq :=
  [{ coef := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     coefAdj := fun g => star (c g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     word := []
     word_lie := by simp
     adj_id := by
       intro x A B'
       unfold B.hsInner
       simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply]
       rw [TBBx2.Tri.hsVec_smul, TBBx2.Tri.hsVec_smul, inner_smul_right, inner_smul_left]
       simp }]

theorem nfMulOp_apply (c : B.Mat k r → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) F g = c g • F g := by
  unfold B.opApply nfMulOp B.Rw
  simp

theorem nfMulOp_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) :
    CutMP.PolyOp 0 κ (nfMulOp (Wp := Wp) (Wq := Wq) c) := by
  unfold CutMP.PolyOp
  intro Tm hTm
  simp only [nfMulOp, List.mem_singleton] at hTm
  subst hTm
  exact ⟨le_refl _, c, hc, fun g => rfl, fun g => rfl⟩

end mul

theorem nf_isPolyDeg_one {N : ℕ} : U.IsPolyDeg (N := N) 0 (fun _ => (1 : ℂ)) := by
  unfold U.IsPolyDeg
  exact ⟨1, by simp, fun g => by simp⟩

theorem nf_isPolyDeg_pow {N κ : ℕ} {c : Matrix (Fin N) (Fin N) ℂ → ℂ} (hc : U.IsPolyDeg κ c) (e : ℕ) :
    U.IsPolyDeg (κ * e) (fun g => c g ^ e) := by
  unfold U.IsPolyDeg at hc ⊢
  obtain ⟨q, hq, hcq⟩ := hc
  refine ⟨q ^ e, ?_, fun g => ?_⟩
  · calc (q ^ e).totalDegree ≤ e * q.totalDegree := MvPolynomial.totalDegree_pow q e
      _ ≤ e * κ := Nat.mul_le_mul_left e hq
      _ = κ * e := Nat.mul_comm e κ
  · simp only [hcq g, map_pow]

theorem empty_operator_list_holds : NFEmptyOps := by
  refine ⟨2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p N
  have hn : (1 : ℝ) ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; push_cast; linarith
  have ok : ∀ (κ : ℕ) (c : B.Mat P.k P.r → ℂ), U.IsPolyDeg κ c → (κ : ℝ) ≤ 2 * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) →
      (∀ pp : B.SS P.k P.r, p.T.base.inSS pp → ∀ g, c (B.sgs pp g) = c g) → NFOpOK 2 p N (nfMulOp c) := by
    intro κ c hc hκ hinv
    obtain ⟨hs, hg, ho⟩ := CutMP.polynomial_decay_admissible P.k P.r Wp Wq 0 κ (nfMulOp c) (nfMulOp_poly hc)
    refine ⟨hs _, ?_, hg _ hκ, ?_⟩
    · intro pp hpp f _ g _
      have hfun : B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) f = fun g => c g • f g := funext (nfMulOp_apply c f)
      rw [nfMulOp_apply, hfun]
      unfold B.rho
      show _ = (p.T.base.π (Matrix.of pp.1.1)).comp ((c (B.sgs pp g) • f (B.sgs pp g)).comp (p.T.base.π' (Matrix.of pp.2.1)⁻¹))
      rw [hinv pp hpp g, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    · have : (B.opOrder (nfMulOp (Wp := Wp) (Wq := Wq) c) : ℝ) ≤ 0 := by exact_mod_cast ho
      have : (0 : ℝ) ≤ 2 * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
      linarith
  refine ⟨nfMulOp (fun _ => (1 : ℂ)), nfMulOp (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ)),
    ok 0 _ nf_isPolyDeg_one (by push_cast; positivity) (fun _ _ _ => rfl), ok ((2 * P.r + 2) * N) _ ?_ ?_ ?_, fun F g => ?_⟩
  · have h := nf_isPolyDeg_pow (Formalism.FourierDecayAlt.P.gram_function_polynomial P.k P.r p.T.base.z p.T.base.z') N
    refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
    rw [← h.choose_spec.2 g]; push_cast; rfl
  · push_cast
    have h1 : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul h1 hn (by norm_num) (by positivity)]
  · intro pp hpp g
    rw [TBBx2.Gf_sgs p.T.base pp hpp g]
  · rw [nfMulOp_apply, nfMulOp_apply, one_smul]
    exact ⟨rfl, rfl⟩

end

end Formalism.FourierDecayAlt.P.CutBP
