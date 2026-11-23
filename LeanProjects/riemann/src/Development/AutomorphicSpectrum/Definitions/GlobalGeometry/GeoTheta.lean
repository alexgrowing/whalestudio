import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoSmallIn

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Q : Par D} (P : SlopeBoundParameters) (S : SlopeGeometry.SharpGeo Q (SlopeGeometry.Msh D P)) (i : Fin D.R.m)
  (El : SlopeGeometry.ELocIn P S i) (B : SlopeGeometry.MbarIn P S i) (r4 lmu : ℝ)

def GeoRef : Prop :=
  ∀ p : ℕ, p.Prime → ∀ la : HeightOneSpectrum (𝓞 S.c.F), (p : 𝓞 S.c.F) ∈ la.asIdeal →
    (Ref.pjSys (S.Xo i) S.c).RefBound (cuspZ (S.Xo i) S.c (S.U i) (SlopeGeometry.wtZ' D i (SlopeGeometry.u1R D P i))) la
      (ramOverZ la * (SlopeGeometry.packGeo P S i El B r4 lmu).e p) (3 / 625) (Ref.phU (S.Xo i) S.c la)

variable (D) in

def keyLoss (p : ℕ) : ℝ :=
  4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 *
    ((padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E + if p = 2 then 1 else 0)

def GeoTheta (Z : SlopeGeometry.Cmp P S i) : Prop :=
  ∃ (τ : Rul (S.Xo i) S.c) (rh : ∀ σ k, Frame ((S.U i σ).X k).Ψ D.R.r → ℝ),
    τ ∈ secZ (S.Xo i) S.c (fun _ => 4 * (D.R.r : ℤ)) ∧ evC (S.gen i) Z τ ≠ 0 ∧
    (∀ p : ℕ, p.Prime → ∀ la : HeightOneSpectrum (𝓞 S.c.F), (p : 𝓞 S.c.F) ∈ la.asIdeal →
      ∀ y : (Ref.pjSys (S.Xo i) S.c).Pt la,
        ((8 * (1 / 625) * Ref.phU (S.Xo i) S.c la y - ramOverZ la * keyLoss D p : ℝ) : EReal) ≤
          (Ref.pjSys (S.Xo i) S.c).val y τ) ∧
    ∀ σ, GoodEmb S.c σ → ∀ k, Over (S.U i σ) (S.e i Z) k →
      ∃ (x0 : Frame ((S.U i σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((S.U i σ).X k)))),
        IsOrth ((S.U i σ).X k) x0 ∧ IsFundSet ((S.U i σ).X k) x0 FF ∧ ∀ y ∈ ((S.U i σ).X k).dom,
          ThA.BergLB ((S.U i σ).X k) x0 FF (laZ (S.U i σ) (SlopeGeometry.wtZ' D i (SlopeGeometry.u1R D P i)) k) y
            (Real.exp (-((SlopeGeometry.packGeo P S i El B r4 lmu).U1 +
              (SlopeGeometry.lvOf D P i lmu (SlopeGeometry.elocOf P S i El)).PPA (SlopeGeometry.packGeo P S i El B r4 lmu) + 3 * rh σ k y))) ∧
          lieFacZ (Q.Dw ((i : ℕ) + 1)) (xiR D) (fun _ => 4 * (D.R.r : ℤ)) *
              ((S.U i σ).X k).pnorm (laZ (S.U i σ) (fun _ => 4 * (D.R.r : ℤ)) k) (rdU (S.U i σ) τ k) y ≤
            Real.exp (4 * (2 * (SlopeGeometry.lvOf D P i lmu (SlopeGeometry.elocOf P S i El)).Ptau0 (SlopeGeometry.packGeo P S i El B r4 lmu) -
              rh σ k y) + 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.pi))

end GlobalTheory.CompanionTheory.Ar.Rec
