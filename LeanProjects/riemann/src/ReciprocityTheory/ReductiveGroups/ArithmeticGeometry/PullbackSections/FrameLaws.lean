import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TanAddPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RdIndepOf
import Formalism.LocalToGlobal.ProjectiveLattices.AdelicContinuousOfUniform

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

variable (c : Coeff l)

def frBC (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S] [Algebra c.F S] [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) : FrPt Xo c K where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := Formalism.L2.Pj.bcOver ψ y.x_over
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := bcLieAll c ψ y τ w hw he
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frame y.x hS hT ψ.toRingHom y.s y.gen

theorem frMap_frBC (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S] [Algebra c.F S] [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) : FrMap ψ y (frBC c hS hT ψ y) :=
  ⟨rfl, fun _ _ => rfl, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm ψ.toRingHom y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _, fun _ _ => rfl⟩

theorem bcEx_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (σ : c.F →+* ℂ) : BCEx Xo c σ := by
  intro p y ψ
  let _ : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact ⟨frBC c hS hT ψ y, frMap_frBC c hS hT ψ y⟩

theorem wtField_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) :
    WtField Xo c :=
  wtField_of_bcR hW (tanAdd_holds Xo) (bcGenR hS hT c) (bcLieR c)

theorem rdIndep_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) : RdIndep Xo c U σ :=
  rdIndep_of_wt U σ hW hAT hU (bcEx_laws c hS hT σ) (wtField_laws c hS hT hW)

end ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj

end ReciprocityTheory.ChartRestriction.G.PullbackSections
