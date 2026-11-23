import Formalism.LocalToGlobal.ProjectiveLattices.TieGenRg
import Formalism.LocalToGlobal.ProjectiveLattices.TieGenR
import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
import Formalism.LocalToGlobal.ProjectiveLattices.ZeroWeightAlgebraicPart
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0

variable {D : D7} {T : Top D}

def SecRat (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ (u : WeightFamilies.Wt D j) (F G' : T.R j),
    F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → G' ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
    valC hG (wtA u) u.n G' Z ≠ 0 →
    rdU (T.U j T.σ₀) F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F Z)
      (valC hG (wtA u) u.n G' Z)) * rdU (T.U j T.σ₀) G' (κ Z) x

def RecogRgSt {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P)))
    (Z : Comp (T.Q.Xo j) T.Q.c) (R : RdData1 d Z ((T.U j T.σ₀).X (κ Z))) : Prop :=
  (∀ Z', CBase hG Z' (yP Z')) → ∀ (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (hx : x ∈ ((T.U j T.σ₀).X (κ Z)).dom) (P : Om Z →+* ℂ),
    P ∈ PT (Ω := Om Z) T.σ₀ → RatRg R x P → PtIs yP Z ((T.U j T.σ₀).un (κ Z) ⟨x, hx⟩) P

def GenDenseRgSt {j : ℕ}
    {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
    {Z : Comp (T.Q.Xo j) T.Q.c} {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X) : Prop :=
  ∃ S : ℕ → Set (Frame X.Ψ D.R.r), (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧ X.dom \ genRg R ⊆ ⋃ n, S n

end Formalism.L2.Pj
