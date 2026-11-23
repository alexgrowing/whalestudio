import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.StabInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hv, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB (hv.and hM.std |>.mono fun v h => h.1.trans h.2)

theorem fix_of_mem_closure {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : Fin n → AE F E) {q : UA σ J}
    (hq : q ∈ Subgroup.closure {g : UA σ J | mat g *ᵥ x = x}) : mat q *ᵥ x = x := by
  have hmul : ∀ g g' : UA σ J, mat (g * g') = mat g * mat g' := fun g g' => by simp [mat]
  have hone : mat (1 : UA σ J) = 1 := by simp [mat]
  induction hq using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => rw [hone, Matrix.one_mulVec]
  | mul g g' _ _ h h' => rw [hmul, ← Matrix.mulVec_mulVec, h', h]
  | inv g _ h =>
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec]

theorem xTerm_left_inv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∀ q ∈ (ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}), ∀ g,
      thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (q * g, h) Φ))) = thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he X om om' om₁ om₁' hT hT₁ Φ hΦ h q hq g
  have hP := Inhab.pairV hT
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hT.base (b + 2) (b + a') G.V G₁.W _ _ _ _ hT.geo.hV hT₁.geo.hW
  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M _ _ om _ _ _ _
    hP (b + a') G.V G₁.W H' 0 (b + 1) M₁ rfl hc.hH' hM₁).1
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_unipotent_fundamental_domain F E σ B b a' G G₁ H H' hc X om om' hT
  obtain ⟨C, hC, hiso⟩ := GlobalTheory.T.eigen_intertwiner_double_restriction hKP F E σ B (b + 2) (b + 2 + a') (b + a') G.V G.W G₁.W G.M M₁ H' 0 (b + 1)
    hc.hH' hM₁ e₀ he₀ b G₁.V H 0 (b + 1) G₁.M hc.hH hT₁.geo.hM e he
  have hΨ : om (g, h) Φ ∈ schA F _ := hT.weil.isUSplitting.pres _ Φ (polData_le_schA hT.geo.hM hΦ)
  have hx0 : H.x ≠ 0 := by
    intro h0
    have := hc.hH.xy
    rw [h0] at this
    simp [form] at this
  have key := hiso _ _ om _ _ _ _ hP μ 𝓕 hμ h𝓕 h1 _ hΨ H.x hx0 hc.hH.xx
  have k1 := key q hq.1 (fix_of_mem_closure _ hq.2)
  have k2 := key 1 (one_mem _) (by simp [mat])
  rw [k1] at k2
  have k3 := mul_left_cancel₀ hC k2
  rw [Prod.mk_one_one, map_one, Module.End.one_apply, ← Module.End.mul_apply (om (q, 1)), ← map_mul, Prod.mk_mul_mk,
    one_mul] at k3
  exact k3

end GlobalTheory.ThK.StabInv

end
