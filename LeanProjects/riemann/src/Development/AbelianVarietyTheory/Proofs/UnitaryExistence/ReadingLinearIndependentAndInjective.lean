import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReadingStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in

theorem reading_linearIndependent_and_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))) ∧ ∀ f ∈ sec Xo c a n, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0 := by
  intro hS E _ _ _ H Dw l Xo c σ r U hU a n
  have h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
      ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
        cvalR σ (ψ (f p y)) = u * rdU U f k x.1 :=
    fun p y ψ => GlobalTheory.T.test_point_value_eq_const_mul_reading hS E H Dw l Xo c σ r U hU a n p y ψ
  have : CharZero c.F := RingHom.charZero σ
  refine ⟨fun m b hb hli => ?_, fun f hf h0 => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro w hw
    have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
      intro θ
      have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
        funext p y
        have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
          obtain ⟨k', x, u, hk⟩ := h p y ψ
          have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
            intro i; rw [hk (b i) (hb i)]; ring
          have e2 := congrFun (congrFun hw k') x.1
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
          simp_rw [e1]
          rw [← Finset.mul_sum, e2, mul_zero]) θ
        simpa [Finset.sum_apply] using hpt
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
    intro i
    exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i
  · funext p y
    show f p y = 0
    refine eq_zero_of_cpts σ p _ fun ψ => ?_
    obtain ⟨k, x, u, hk⟩ := h p y ψ
    have e := hk f hf
    rw [h0 k x.1 x.2, mul_zero] at e
    exact e

end GlobalTheory
