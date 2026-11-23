import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfPrintsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesIsotropicVectorStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.EvFunProps

section Comm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem locOp_rho_comm (hA : ActsEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {v : Pl F}
    {q : UA σ X.J} (hq : q ∈ UAt σ X (evFin F v)) {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : mat q * w = w)
    {ψ : (Fin n × Fin d → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) :
    locOp v (M.co.rho B.ψ (partFin v w)) (locOp v (om (q, 1)) ψ) =
      locOp v (om (q, 1)) (locOp v (M.co.rho B.ψ (partFin v w)) ψ) := by
  have hstd : IsStd B.ψ := hP.base.std
  have h1m : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  have hspl := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  refine GlobalTheory.TensUniq.eq_of_tens_eq v ψ _ _ hψ fun r hr => ?_
  have h1 : Acts (evFin F v) (om (q, 1)) ψ (locOp v (om (q, 1)) ψ) := acts_locOp_om hA hP hq h1m hψ
  have hR1 : Rest (evFin F v) (locOp v (om (q, 1)) ψ) r := ⟨hr.1, by rw [← h1 r hr]; exact hspl.pres _ _ hr.2⟩
  have h2 := (locOp_rho M.co hstd.1 v w hψ).1
  have hR2 : Rest (evFin F v) (locOp v (M.co.rho B.ψ (partFin v w)) ψ) r :=
    ⟨hr.1, by rw [← h2 r hr]; exact GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hr.2⟩
  have h3 := (locOp_rho M.co hstd.1 v w (locOp_mem v (om (q, 1)) ψ)).1 r hR1
  have h4 := acts_locOp_om hA hP hq h1m (locOp_mem v (M.co.rho B.ψ (partFin v w)) ψ) r hR2
  rw [← h3, ← h4, ← h1 r hr, ← h2 r hr, hspl.impl _ _ _ hr.2]
  congr 2
  simp only [actAB, partFin]
  rw [show (((1 : UA σ W.J) : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1 from rfl,
    Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  exact congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z) hw.symm

end Comm
end GlobalTheory.ThK.EvFunProps

namespace GlobalTheory.ThK.EvFunProps

theorem evFunProps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        (∀ q ∈ UAt σ G.V (evFin F v), mat q *ᵥ incV F H.x = incV F H.x → ∀ x ∈ UAt σ G.V (evFin F v),
          coneEvFun B G H H' om v (ev v) l φ (q * x) = coneEvFun B G H H' om v (ev v) l φ x) ∧
        (∀ g ∈ UAt σ G.V (evFin F v), ∀ x ∈ UAt σ G.V (evFin F v),
          coneEvFun B G H H' om v (ev v) l (locOp v (om (g, 1)) φ) x = coneEvFun B G H H' om v (ev v) l φ (x * g)) ∧
        Continuous (fun x : UAtSub σ G.V (evFin F v) => coneEvFun B G H H' om v (ev v) l φ x.1) := by
  intro hPr F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he ei ev hloc X om om' om₁ om₁' hT hT₁ v l hl φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have hP := Inhab.pairV hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).one_mem
  have hcomp : ∀ x y, x ∈ UAt σ G.V (evFin F v) → y ∈ UAt σ G.V (evFin F v) →
      ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        locOp v (om (x * y, 1)) ψ = locOp v (om (x, 1)) (locOp v (om (y, 1)) ψ) := by
    intro x y hx hy ψ hψ
    have h := locOpMul hPr F E σ B _ _ G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP v (x, 1) (y, 1) hx h1W hy h1W ψ hψ
    rwa [Prod.mk_mul_mk, mul_one] at h
  have hEv := GlobalTheory.T.eval_invariance_first_of_hypotheses hPr F E σ B b a' G G₁ H H' hC e he ei ev hloc X om om' om₁ om₁' hT hT₁ v l hl
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hqx x hx
    have hw : mat q * shiftA H H' 1 = shiftA H H' 1 := by
      rw [shiftA, Units.val_one, one_smul]
      ext i j
      have hi := congrFun hqx i
      refine (show _ = ∑ k, mat q i k * (incV F H.x k * incV F H'.y j) from rfl).trans ?_
      rw [Matrix.vecMulVec_apply, ← hi]
      refine Eq.trans ?_ (show (∑ k, mat q i k * incV F H.x k) * incV F H'.y j = _ from rfl)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
    simp only [coneEvFun]
    rw [hcomp q x hq hx φ hφ, locOp_rho_comm hA hP hq hw (locOp_mem v _ φ)]
    obtain ⟨u, hu, huv, g₀, g, hlev, hg, hg₀, rfl⟩ := GlobalTheory.T.stabilizer_fixes_isotropic_vector F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v q hq hqx
    rw [hcomp u g huv hg _ (locOp_mem v _ _), hEv.1 u hu huv _ (locOp_mem v _ _), hEv.2 g₀ g hlev hg hg₀ _ (locOp_mem v _ _)]
  · intro g hg x hx
    simp only [coneEvFun]
    rw [hcomp x g hx hg φ hφ]
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
    obtain ⟨U, hU, hUfix⟩ := (hA F E σ B _ _ G.V G.W G.M X.β _ om _ _ _ _ hP v).2.2 φ hφ
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hc : Continuous fun y : UAtSub σ G.V (evFin F v) =>
        ((x.1⁻¹ * y.1, (1 : UA σ G.W.J)) : UA σ G.V.J × UA σ G.W.J) :=
      (continuous_const.mul continuous_subtype_val).prodMk continuous_const
    have hx1 : ((x.1⁻¹ * x.1, (1 : UA σ G.W.J)) : UA σ G.V.J × UA σ G.W.J) = 1 := by
      rw [inv_mul_cancel]; rfl
    have hS : {y : UAtSub σ G.V (evFin F v) | ((x.1⁻¹ * y.1, (1 : UA σ G.W.J)) : UA σ G.V.J × UA σ G.W.J) ∈ U} ∈ 𝓝 x :=
      hc.continuousAt.preimage_mem_nhds (by rw [hx1]; exact hU)
    refine (continuousAt_const :
      ContinuousAt (fun _ : UAtSub σ G.V (evFin F v) => coneEvFun B G H H' om v (ev v) l φ x.1) x).congr ?_
    filter_upwards [hS] with y hy
    have hmem : x.1⁻¹ * y.1 ∈ UAt σ G.V (evFin F v) := (UAtSub σ G.V (evFin F v)).mul_mem (inv_mem x.2) y.2
    have hfix : locOp v (om (x.1⁻¹ * y.1, 1)) φ = φ := locOp_eq hφ hφ (hUfix _ hy hmem h1W)
    have hy' : y.1 = x.1 * (x.1⁻¹ * y.1) := (mul_inv_cancel_left _ _).symm
    simp only [coneEvFun]
    conv_rhs => rw [hy', hcomp x.1 _ x.2 hmem φ hφ, hfix]

end GlobalTheory.ThK.EvFunProps
