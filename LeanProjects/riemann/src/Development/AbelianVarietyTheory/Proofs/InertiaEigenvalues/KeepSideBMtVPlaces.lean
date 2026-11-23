import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs

section Keep

variable (D : D7) (Dat : D.ntw.Tw → ℕ → Bool → Type) (th : ∀ i j b, Dat i j b → D.nexp.Fm i j b)
  (lev : ∀ i j b, Dat i j b → Finset (PlE D.host))
  (thPsi : ∀ i j b k (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Dat i j b →
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b))
  (h1 : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] th i j b d})
  (thU : ∀ i j b (Q : Finset (PlE D.host)) (M : ℕ), Dat i j b →
    D.nexp.Fm i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M))
  (thP : ∀ i j b k Q ψ, D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b))
  (MtLat : ∀ i j b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i j b k Q ψ))
  (h2 : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG)
  (h3 : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (D.ntw.Ok i k)) (MtLat i j b k Q ψ : Set (D.nexp.MtV i j b k Q ψ)) = ⊤)

def keepEx : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw :=
  { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }

variable (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3))

def keepTw : TwNew D := ⟨D.ntw, keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3, D.nStage_trivialCharacter_coeff_eq, nth', D.ntwbr, D.ntwbr_ind⟩

variable (hU : ∀ i j b M (d : Dat i j b), 1 ≤ j → j ≤ D.R.m →
  thU i j b ∅ M d = th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M)))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def keepExp (E : NExpTied D) : NExpTied (keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    thU_empty := fun i j b M d hj hj' => hU i j b M d hj hj'
    mtV := fun i j b k Q ψ hj hj' hA => by
      letI : AddCommGroup (E.Wt i j b) := E.acgWt i j b
      letI : Module (FractionRing ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7.ntw.O i)) (E.Wt i j b) := E.modWt i j b
      exact { E.mtV i j b k Q ψ hj hj' hA with } }

variable (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
  (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
  (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
  (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def keepSideB (Bs : SideB D cf Rw low Pq S hL eig θ) :
    SideB (keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').toD7 ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').cf cf) ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').row Rw) low Pq
      ((keepTw D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth').rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := keepExp D Dat th lev thPsi h1 thU thP MtLat h2 h3 nth' hU Bs.exp
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA }

section Same
variable (Bs : SideB D cf Rw low Pq S hL eig θ)

end Same

end Keep

section Keep

end Keep

end GlobalTheory.TwInputs

end
