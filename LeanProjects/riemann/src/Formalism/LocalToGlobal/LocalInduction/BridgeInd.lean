import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace Formalism.L2

variable {l : ℕ} [Fact l.Prime]

structure ArithTied (P : LocPrime l) : Prop where
  val : ∀ (LL : FinExt l) (x : ↥LL.1) (q : ℚ),
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ))

def BridgeInd {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (A : ValuationSubring Ω) : Prop :=
  ∀ x : Ω, x ∈ A ↔ ‖Bw.j x‖ ≤ 1

def vrep {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* GL (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r)

structure LocTied (D : D7) where
  arith : ∀ (l : ℕ) [Fact l.Prime], ArithTied (D.loc l)

  nbr : ∀ (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    BridgeInd (D.nbr i w hw) (D.nd.plOm.1 w)
  ntwbr : ∀ (i : D.ntw.Tw) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.ntw.l i)),
    BridgeInd (D.ntwbr i w hw) (D.nd.plOm.1 w)

def LocTiedP (D : D7) : Prop := Nonempty (LocTied D)

end Formalism.L2
