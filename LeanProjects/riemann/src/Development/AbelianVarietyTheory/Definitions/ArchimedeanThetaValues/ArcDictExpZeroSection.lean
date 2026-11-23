import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure GtAn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} (a : ArcIn D l β ℂ b) where
  star_eq : (inferInstance : StarRing (𝓞 E)) = H.starRing
  A : AnArc (𝓞 E)
  ε : A.X ≃ₗ[𝓞 E] a.D₀.X
  be_eq : ∀ x y, A.be x y = a.be (ε x) (ε y)
  gB_eq : A.gB = a.D₀.P.g
  u : HolUnif a.D₀.P.A a.D₀.P.L A.gB
  lam : u.Λ = A.abelian₂
  ah : u.IsAH A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩)
  rig : u.IsRig a.D₀.rig
  tan : (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  pow : ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ ∧ u.IsFnPow n s θ) ∧
    ∀ θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ → ∃! s, u.IsFnPow n s θ
  act : ∀ x z, u.ex (A.F x z) = u.ex z ≫ (letI := H.starRing; a.oa.onB.act x)
  ct : ∀ x, u.ex (A.ct x) = a.D₀.c (ε x)
  psi : ∀ x, FrameValue.genVal u a.D₀.P.isLB (a.D₀.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x
  ex0 : A.V → Out.GtPtF a.D₀ ℂ
  ex0_b : ∀ v, (show Sp ℂ ⟶ _ from (ex0 v).b.left) = (u.ex v.2).left
  arcDict_expZero_section : ∀ v x, FrameValue.genVal u a.D₀.P.isLB ((ex0 v).s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
    ![A.ct x + v.2, A.ct x, v.2, 0] = eTwoPi (v.1 x)

def GtAn.fn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (j : ℕ) (α : Λ.A.X)
    (s : a.D₀.SecB j (Λ.ε α)) (z : Fin Λ.A.gB → ℂ) : ℂ :=
  FrameValue.secVal Λ.u a.D₀.P.isLB s (Λ.u.ex z).left ![z, z + Λ.A.ct α, Λ.A.ct α, 0]

def GtAn.Rep [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (k : ℕ)
    (p : Out.QkPt a.D₀ (FractionRing ℂ) k) (la : Λ.A.La) : Prop :=
  ∀ q : Out.QkPt a.D₀ ℂ k, QkExt (algebraMap _ ℂ) p q → q.y = Λ.ε la.y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la)

end GlobalTheory.ArcPts
