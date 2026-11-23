import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFiniteRationalRealGaussian

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.NormExact

theorem heisO_finPt_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hf z
  subst hS hT
  have hc := hs.crv
  have hr := hs.scale
  have hr0 : r ≠ 0 := IsScale.ne_zero hc.1.1 hr
  rw [reads_iff hc hr] at hf ⊢
  refine ⟨GlobalTheory.TwistFactorCompare.isTheta_heisO hs.std hf.1 _, fun w hw => ?_⟩
  set X : VC D S.rank T.rank := fun τ i j => embT D τ (r⁻¹ * z i j) with hXdef
  have hX : (fun τ a b => -(((GlobalTheory.FockPos.frAt (1 : GL (Fin T.rank) D.host.E) τ)⁻¹ *
      Matrix.of (GlobalTheory.VacUnique.infRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) τ) *
      GlobalTheory.FockPos.frAt (1 : GL (Fin S.rank) D.host.E) τ) a b)) = X := by
    funext τ a b
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [e, inv_one, Matrix.one_mul, Matrix.mul_one]
    show -(embT D τ (-(r⁻¹ * z a b))) = embT D τ (r⁻¹ * z a b)
    rw [map_neg, neg_neg]
  have h := GlobalTheory.MovedTrans.heisO_finRat_real ψ θ S T 1 1 (by simp [Formalism.UG.cT_one, hs.gS])
    (by simp [Formalism.UG.cT_one, hs.gT]) hs.std hs.inf f hf.1 (fun Z => G fun τ i j => δ * embT D τ r * Z τ i j) hf.2
    (Matrix.of fun i j => -(r⁻¹ * z i j)) _ hX.symm w hw
  have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z =
      GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) := rfl
  have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * X τ i j := by
    funext τ i j
    show δ * embT D τ (z i j) = δ * embT D τ r * embT D τ (r⁻¹ * z i j)
    rw [mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  rw [e1, h, hpt]
  simp only [U]
  rw [Hf_scale hc hr, Hf_scale hc hr]
  have hY : ((fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j) + fun τ i j => δ * embT D τ r * X τ i j) =
      fun τ i j => δ * embT D τ r * (GlobalTheory.FockPos.zCo θ 1 1 w + X) τ i j := by
    funext τ i j
    simp only [Pi.add_apply]
    ring
  rw [hY]

end GlobalTheory.NormExact
