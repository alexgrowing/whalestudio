import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSumStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
end GlobalTheory.ThetaLineDeriv
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hS := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ
  have key : ∀ i, ∃ (v : ℝ → ℂ) (w : ℂ), (∀ t : ℝ, HasSum (fun ξ : Fin a × Fin (a + a') → F =>
      G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))
        (fun j => algebraMap F (AF F) (ξ j))) (v t)) ∧
      HasSum (fun ξ : Fin a × Fin (a + a') → F => G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))
        (fun j => algebraMap F (AF F) (ξ j))) w ∧ HasDerivAt v w 0 := by
    intro i
    by_cases h0 : f i = 0
    · have ht0 : tens (evI F) (⇑(f i)) (r i) = 0 := by funext x; simp [tens, h0]
      have ht1 : tens (evI F) (⇑(f₁ i)) (r i) = 0 := by
        funext x
        have h := hD i (r i) (hR i) x
        simp only [ht0, map_zero, Pi.zero_apply] at h
        exact h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      refine ⟨fun _ => 0, 0, fun t => ?_, ?_, hasDerivAt_const _ _⟩
      · rw [ht0, map_zero, rho_zero]; exact hasSum_zero
      · rw [ht1, rho_zero]; exact hasSum_zero
    · obtain ⟨c, c', hc0, hl, hact⟩ := hS (f i)
      obtain ⟨T, hT'⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) h0
      have htens : tens (evI F) (⇑(f₁ i)) (r i) = tens (evI F) (⇑c') (r i) := by
        funext x
        have h1 := hD i (r i) (hR i) x
        have h2 : HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x)
            (tens (evI F) (⇑c') (r i) x) 0 := by
          have e : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x) =
              fun t => c t (fun j => evI F (x j)) * r i x := by
            funext t; rw [hact t (r i) (hR i)]; rfl
          rw [e]
          exact (hasDerivAt_eval c (f i) c' hc0 hl _).mul_const _
        exact h1.unique h2
      refine ⟨fun t => T (c t), T c', fun t => ?_, ?_, hasDerivAt_clm c (f i) c' hc0 hl T⟩
      · rw [hact t (r i) (hR i)]; exact hT' (c t)
      · rw [htens]; exact hT' c'
  choose v w hv hw hd using key
  have e1 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i)))) = ∑ i, v i t := by
    intro t
    rw [map_sum, rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hv i t) using 1
    funext ξ
    simp [Finset.sum_apply]
  have e2 : GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i))) = ∑ i, w i := by
    rw [rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hw i) using 1
    funext ξ
    simp [Finset.sum_apply]
  rw [show (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i))))) = fun t => ∑ i, v i t from funext e1, e2]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  have e3 : (fun t : ℝ => ∑ i, v i t) = ∑ i, v i := by funext t; simp [Finset.sum_apply]
  rw [e3]
  exact hs
end GlobalTheory.ThetaLineDeriv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | exact _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally <;> assumption)
end
