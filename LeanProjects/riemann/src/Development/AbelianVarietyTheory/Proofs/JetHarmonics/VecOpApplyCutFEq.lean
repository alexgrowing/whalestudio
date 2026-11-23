import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem vec_opApply_cutF_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Θ : B.DiffOp P.k P.r Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (δ : ℝ) (γ : C.LPt), C6.IsCut0 χ → 0 < δ → δ < TBB.Gp p γ → p.V (B.opApply Θ (D.cutF p.T.base χ f δ)) γ = p.V (B.opApply Θ f) γ := by
  intro Wp Wq _ _ _ _ _ _ P p Θ f χ δ γ hχ hδ hlt
  have hlt0 : δ < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hlt
  have hopen : IsOpen {x : B.Mat P.k P.r | δ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hloc : ∀ g, δ < Gf P.k P.r p.T.base.z p.T.base.z' g →
      B.opApply Θ (D.cutF p.T.base χ f δ) g = B.opApply Θ f g := by
    intro g hg
    refine Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hopen (fun x hx => ?_) g hg
    have hx' : δ < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    simp only [D.cutF]
    rw [hχ.2.2 _ ((one_le_div hδ).mpr hx'.le), Complex.ofReal_one, one_smul]
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose h.1 h'.choose_spec.2.1
    have hlt' : δ < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hlt0
    have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h'.choose
      (D.muR p.T.base h'.choose (h.1.2 ▸ D.ptPerm γ)) (B.opApply Θ (D.cutF p.T.base χ f δ)) (B.opApply Θ f) 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [hloc _ (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hlt')])
    rw [e, one_smul]
  · rfl
  · rfl

end GlobalTheory.HatNF
