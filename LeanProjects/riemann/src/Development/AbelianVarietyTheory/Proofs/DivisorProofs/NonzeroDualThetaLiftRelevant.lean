import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKAnisoSmallReG

theorem nonZero_reG : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')), IsTriple B G X om om' →
    IsTriple B (reG G V V' W) X om om' → G.q = 0 → (∃ Φ' ∈ PolData B (reG G V V' W).M', (reG G V V' W).M'.I om' Φ' ≠ 0) →
    ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' V V' W hT hT' hq ⟨Φ₀, hΦ₀, hne⟩
  by_contra hcon
  push_neg at hcon
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hWC := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q) _ _ hP
    (Or.inr (by simp [hq]))
  have hD := GlobalTheory.T.polynomial_fock_dense F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q) _ _ hP
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hPol : PolData B (reG G V V' W).M' ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have key : ∀ Φ ∈ PolData B (reG G V V' W).M', G.M'.I om' Φ = 0 := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hx
      funext h
      have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
      have hg := GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB hstd
      have hc := hWC.2 _ hg h
      have hz : ∀ f' ∈ (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))),
          G.M'.I om' (pureA F f' (fun y : Fin a' × Fin (a + a') → FiniteAdeleRing (𝓞 F) F =>
            ∏ᶠ v, φ v fun i => evalV F v (y i))) h = 0 := by
        intro f' hf'
        have hm : pure f' φ ∈ PolData B G.M' := Submodule.subset_span ⟨f', hf', φ, hSB, hev, rfl⟩
        exact congrFun (hcon _ hm) h
      have hcl : f ∈ closure (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))) := by
        rw [hD.closure_eq]; exact Set.mem_univ _
      have := map_mem_closure hc hcl (t := {0}) (fun f' hf' => hz f' hf')
      rw [closure_singleton] at this
      exact Set.mem_singleton_iff.mp this
    | zero =>
      funext h
      have e : ∀ g, theta om' (0 : (Fin a' × Fin (a + a') → AF F) → ℂ) g h = 0 := fun g => by
        have := thetaSum_smul F (0 : ℂ) (om' (g, h) 0)
        simp only [theta, map_zero] at this ⊢
        simpa using this
      simp [Model.I, e]
    | add x y hx hy ihx ihy =>
      funext h
      have hxS := hPol hx
      have hyS := hPol hy
      have e : ∀ g, theta om' (x + y) g h = theta om' x g h + theta om' y g h := fun g => by
        simp only [theta, map_add]
        exact thetaSum_add F (pres _ x hxS) (pres _ y hyS)
      have ix := (hWC.1 x hxS).1 h
      have iy := (hWC.1 y hyS).1 h
      have h1 := congrFun ihx h
      have h2 := congrFun ihy h
      simp only [Model.I, Pi.zero_apply] at h1 h2 ⊢
      rw [show (fun g => theta om' (x + y) g h) = fun g => theta om' x g h + theta om' y g h from funext e,
        integral_add ix iy, h1, h2, add_zero]
    | smul c x hx ihx =>
      funext h
      have e : ∀ g, theta om' (c • x) g h = c * theta om' x g h := fun g => by
        simp only [theta, map_smul]
        exact thetaSum_smul F c _
      have h1 := congrFun ihx h
      simp only [Model.I, Pi.zero_apply] at h1 ⊢
      rw [show (fun g => theta om' (c • x) g h) = fun g => c * theta om' x g h from funext e,
        integral_const_mul, h1, mul_zero]
  exact hne (key Φ₀ hΦ₀)

end GlobalTheory.ThKAnisoSmallReG
