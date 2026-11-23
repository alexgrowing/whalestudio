import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

noncomputable section
open ValuativeRel NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open scoped Pointwise

namespace GlobalTheory.HL

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def Frames.datOf {L : LocE F E} {r k : ℕ} (S : Frames L r k) (Λ : Submodule L.O S.V) : S.Datum :=
  ((Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O,
    (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O, S.graphOf Λ)

variable [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure WCoord (P : LocNG.FPair H r) (S : Frames M.L r k) where
  e : V ≃ₗ[E] S.V
  h_eq : ∀ x y, S.h (e x) (e y) = H.h x y
  f_eq : ∀ a, S.f a = e (P.A.f a)
  f'_eq : ∀ a, S.f' a = e (P.B.f a)
  T_eq : (S.T : F) = P.A.T
  T'_eq : (S.T' : F) = P.B.T
  gg_none : M.split = none → S.gg = false
  gg_some : ∀ g, M.split = some g → S.gg = true ∧ S.ϖ = g.q

namespace WCoord

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)

def lat (Λ : Submodule M.L.O V) : Submodule M.L.O S.V :=
  Λ.map ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)

def inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) : Submodule M.L.O S.V :=
  c.lat ((L.comap ((H.mkW f).restrictScalars M.L.O)).map ((H.perp (H.X f)).subtype.restrictScalars M.L.O))

def dat (d : LocNG.Datum P) : S.Datum :=
  (c.inn P.A.f d.L, c.inn P.B.f d.L',
    {p | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧
      ((M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io)})

end WCoord

end Loc

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def placesOf (Z : LocDat D) : Places D.host.F D.host.E D.conjF where
  quad := Formalism.MainNotions.BridgeLemma.szf_finrankFE D
  loc := D.s.atP
  L := fun p => (Z.M p).L
  L_cj := Z.hcj

structure GCoord (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) where
  e : (VS D).V ≃ₗ[D.host.E] G.V
  h_eq : ∀ x y, (∑ i, ∑ j, e x i * G.Hm i j * star (e y j)) = brS (VS D) x y
  f_eq : ∀ a, G.f a = e (frame F0 a)
  f'_eq : ∀ a, G.f' a = e (frame F0' a)
  c : ∀ p, WCoord (FP p) (G.S p)
  compat : ∀ p x, (c p).e (baseChange₂ D p x) = (placesOf Z).bc p (e x)
  c_eq : ∀ p, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (G.c p).val =
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)

namespace GCoord

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

def lat (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : G.Lt :=
  Λ.map (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))

def grp (ρ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : G.GLV :=
  (((ρ.trans c.e).symm.trans n).trans (ρ.trans c.e))

end GCoord

def GFrames.datOf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (Γ : G.Lt) : G.Dat :=
  fun p => (G.S p).datOf (A.lat p Γ)

def MovesTo {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) : Prop :=
  ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ IsUpUni U ∧ IsUpUni U' ∧
    (∀ b, ρ (frame F b) = ∑ a, U a b • frame F0 a) ∧ ∀ b, ρ (frame F' b) = ∑ a, U' a b • frame F0' a

def realPts (X : HidaSetting D) (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : Set X.B.I.Ginf :=
  {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ y = x.1 ∧ n ∈ S}

end Glob

end GlobalTheory.HL
