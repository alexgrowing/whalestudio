import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def KappaTie (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (f : T.R j), f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n →
    (evC hG Z f = 0 ↔ ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) f (κ Z) x = 0)

def DTie (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) : Prop :=
  ∃ (uL : WeightFamilies.Wt D j) (W : Fin (d.N + 1) → (recB h.toLawsCore).Cusp j uL), Even uL.n ∧
    d.wL = wtZ (wtA uL) uL.n ∧ (∀ i Z, d.w i Z = valC hG (wtA uL) uL.n (W i).1 Z) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra T.Q.c.F k] (y : FrPt (T.Q.Xo j) T.Q.c k),
      ∃ i, evR (T.Q.Xo j) T.Q.c (W i).1 y ≠ 0

def NrmTie (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (G : WTZ D.host.E) (P : Om Z →+* ℂ), d.nrm Z G 0 P = 0) ∧
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c), ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, ∀ P : Om Z →+* ℂ,
    P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    (∀ (u : WeightFamilies.Wt D j) (F G' : T.R j),
      F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → G' ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      valC hG (wtA u) u.n G' Z ≠ 0 →
      rdU (T.U j T.σ₀) F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F Z)
        (valC hG (wtA u) u.n G' Z)) * rdU (T.U j T.σ₀) G' (κ Z) x) →
    ∀ (u : WeightFamilies.Wt D j) (F : T.R j), F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      ((T.U j T.σ₀).X (κ Z)).pnorm (laU (T.U j T.σ₀) (wtA u) u.n (κ Z)) (rdU (T.U j T.σ₀) F (κ Z)) x =
        d.nrm Z (wtZ (wtA u) u.n) (valC hG (wtA u) u.n F Z) P

def KappaOnto (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) :
    Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ), P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    ∃ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, ∀ (u : WeightFamilies.Wt D j) (F G' : T.R j),
      F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → G' ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      valC hG (wtA u) u.n G' Z ≠ 0 →
      rdU (T.U j T.σ₀) F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F Z)
        (valC hG (wtA u) u.n G' Z)) * rdU (T.U j T.σ₀) G' (κ Z) x

def TieReadingSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  FnAlgClosed (T.Q.Xo j) T.Q.c → KappaTie j hG κ → KappaOnto h j hG κ → DTie h j hG d → NrmTie h j hG d κ →
  ∃ R : ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      ReciprocityTheory.ChartRestriction.G.AR.Up.Reading (𝒜 := fun Z G => AG Z G) d Z ((T.U j T.σ₀).X (κ Z)) T.σ₀,
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u)
      (hF : valC hG (wtA u) u.n F.1 Z ∈ (R Z).Rg),
        ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, (R Z).rd ⟨_, hF⟩ x = rdR h j F (κ Z) x) ∧
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), Even u.n →
      valC hG (wtA u) u.n F.1 Z ∈ (R Z).Rg) ∧
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j), Even u.n → wtZ (wtA u) u.n ∈ (R Z).WE) ∧
    ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (hu : wtZ (wtA u) u.n ∈ (R Z).WE),
      (R Z).wt ⟨_, hu⟩ = laU (T.U j T.σ₀) (wtA u) u.n (κ Z)

end Formalism.L2.Pj
