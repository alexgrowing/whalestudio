import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HolSubMul

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

open Classical in

theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem holSub_mul (hM : SiegelSpaceAlgebra (E := E)) {Comp : Type} {X : Comp → Data E r} {la la' : ∀ k, Wt (X k).Ψ r}
    {P Q : FDSec X} (hP : P ∈ holSub X la) (hQ : Q ∈ holSub X la') : P * Q ∈ holSub X (la + la') := by
  first | exact UpperTheory.Reformulated.B.Qe28.holSub_mul .. | (apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP hQ | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E

theorem cusp_mul_of_M5 (hM : SiegelSpaceAlgebra (E := E)) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMul Xo c U := by
  intro a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hd.2 hd'.2 k
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, hla]
  exact holSub_mul hM (hf.2 σ hσ) (hg.2 σ hσ)

end Formalism.L2.Pj
