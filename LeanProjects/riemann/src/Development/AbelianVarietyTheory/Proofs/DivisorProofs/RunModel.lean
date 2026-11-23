import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section RunModelSec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def RunModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp),

    (∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) ∧

    (∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) ∧

    (∃ a : p.P.Gp → C → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp) (c : C)
      (x : Frame M.Ψ D.R.r), x ∈ M.dom →
      ∀ (h1 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ)
        (h2 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e (g • c))).Ψ),
        rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀)
            (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (r.lev i g⁻¹) F.1)
            (e c) (castFrame h1 x) =
          (a g c : ℂ) * rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀) F.1 (e (g • c))
            (castFrame h2 (lact (M.tr g c) x))) ∧

    (∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • (M.comp c).L') ∧

    ∃ φ : ∀ c, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
        ((M.comp c).L' ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L'))),
      ∀ (c : C) (u : p.P.Gp), u • c = c → ∃ n : ℤ, ∀ w : (M.comp c).L',
        ∃ hw : Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L',
          Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L')) ⟨_, hw⟩ =
            φ c ((r.lev i u ^ n) ((φ c).symm (Submodule.Quotient.mk w)))

end RunModelSec

end GlobalTheory.ShareOn

end
