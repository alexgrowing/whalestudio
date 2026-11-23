import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l) in

def BcLieAnySt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber K) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → K,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo : Moduli Dw l} {c : Coeff l}

def bcPtAny (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) {S : Type} [CommRing S] [Algebra c.F S] {K : Type} [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K) (y : FrPt Xo c S) : FrPt Xo c K where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL S K ψ y τ w hw he
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frame y.x hS hT ψ.toRingHom y.s y.gen

theorem frMap_bcPtAny (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) {S : Type} [CommRing S] [Algebra c.F S] {K : Type} [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K) (y : FrPt Xo c S) : FrMap ψ y (bcPtAny hS hT hL ψ y) :=
  ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _, fun _ _ => rfl⟩

theorem frBCField_of (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (hL : BcLieAnySt Xo c) : FrBCFieldSt Xo c := by
  intro S _ _ y K _ _ ψ
  exact ⟨bcPtAny hS hT hL ψ y, frMap_bcPtAny hS hT hL ψ y⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
