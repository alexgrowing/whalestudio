import Formalism.LocalToGlobal.ProjectiveLattices.TieUpR
import Formalism.LocalToGlobal.ProjectiveLattices.TieGen

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def RatAt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ (u : WeightFamilies.Wt D j) (F G' : (recB h.toLawsCore).Cusp j u), Even u.n →
    valC hG (wtA u) u.n G'.1 Z ≠ 0 →
    rdR h j F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F.1 Z)
      (valC hG (wtA u) u.n G'.1 Z)) * rdR h j G' (κ Z) x

def genR (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) : Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) :=
  {x | x ∈ ((T.U j T.σ₀).X (κ Z)).dom ∧ ∃ P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀, RatAt h j hG κ Z x P}

open Classical in

def ptR (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (hne : Nonempty (Om Z →+* ℂ)) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) :
    Om Z →+* ℂ :=
  if hx : x ∈ genR h j hG κ Z then hx.2.choose else hne.some

def RecogSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r)
    (hx : x ∈ ((T.U j T.σ₀).X (κ Z)).dom) (P : Om Z →+* ℂ), P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    RatAt h j hG κ Z x P → PtIs yP Z ((T.U j T.σ₀).un (κ Z) ⟨x, hx⟩) P

def GenDenseSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ S : ℕ → Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r),
    (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧
    ((T.U j T.σ₀).X (κ Z)).dom \ genR h j hG κ Z ⊆ ⋃ n, S n

end Formalism.L2.Pj
