import Mathlib
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo

noncomputable section

namespace GlobalTheory.Published

section AutomorphicFormsHyp

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

def GoodChernNumbers : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0)
    (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
    Refines E E' φ f → IsGraded E' gr →
      ∀ (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → IsGood E O H →
        ∀ R : MvPolynomial (ι × ℕ) ℝ, HasChernIntegral E O H R (Y.interPoly gr (chernRoots m R * fibrePoint m))

def FlagPushForward : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0)
    (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
    Refines E E' φ f → IsGraded E' gr →
      ∀ (Q : MvPolynomial (Root m) ℝ) (R : MvPolynomial (ι × ℕ) ℝ), antisymm Q = chernRoots m R * rootDiscr m →
        Y.interPoly gr Q = Y.interPoly gr (chernRoots m R * fibrePoint m)

def GoodChernWeil : Prop := GoodChernNumbers ∧ FlagPushForward

theorem GoodChernWeil.flag (h : GoodChernWeil) {F : Type} [Field F] {σ : F →+* ℂ} {X Y : Var F} {ι : Type} [Fintype ι]
    {m : ι → ℕ} {E : Fr (ratOf X) m 0} {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} {gr : Root m → Y.Dv}
    (hf : Refines E E' φ f) (hg : IsGraded E' gr) {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    (hH : IsMetricOn E O H) (hG : IsGood E O H) {Q : MvPolynomial (Root m) ℝ} {R : MvPolynomial (ι × ℕ) ℝ}
    (hR : antisymm Q = chernRoots m R * rootDiscr m) : HasChernIntegral E O H R (Y.interPoly gr Q) := by
  have : CharZero F := σ.charZero
  rw [h.2 F X Y ι m E E' φ f gr hf hg Q R hR]
  exact h.1 F σ X Y ι m E E' φ f gr hf hg O H hH hG R

theorem GoodChernNumbers.line (h : GoodChernNumbers) {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (Δ : X.Dv)
    {O : X.X.Opens} {H : Mat (fun _ : Unit => 1) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => 1) ℂ}
    (hH : IsMetricOn (ofDivisor Δ) O H) (hG : IsGood (ofDivisor Δ) O H) :
    HasChernIntegral (ofDivisor Δ) O H (MvPolynomial.X ((), 1) ^ X.dim) (X.inter fun _ => Δ) := by
  have := h F σ X X Unit _ _ _ _ _ _ (refines_lineFlag _) (isGraded_ofDivisor Δ) O H hH hG
    (MvPolynomial.X ((), 1) ^ X.dim)
  have e : chernRoots (fun _ : Unit => 1) (MvPolynomial.X ((), 1) ^ X.dim) * fibrePoint _ =
      ∏ _i : Fin X.dim, MvPolynomial.X ⟨(), 0⟩ := by
    simp [chernRoots, fibrePoint, esymm_one]
  rwa [e, Var.interPoly_prod] at this

end AutomorphicFormsHyp

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

open Classical in

def MumfordProportionality : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp) (la : GlobalTheory.AllWt.Weight Dw),
      (((Φ.C k).Y.inter (fun _ => (Φ.C k).Lw la) : ℤ) : ℝ) =
        GlobalTheory.TrueCx.covol (U.X k) *
          Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))

end GlobalTheory.Published
