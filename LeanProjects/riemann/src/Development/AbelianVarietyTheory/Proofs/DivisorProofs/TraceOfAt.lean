import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

abbrev delW : Formalism.L2.Host.HChar D.host.E := (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w))

abbrev plW : Finset (Pl D.host.E) := GlobalTheory.OnTies.placesOver (R2 p) ((R2 p).mu (D.plEq w)) (ownAt D (D.plEq w))

abbrev IsEv (u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j (sg0 D p.P.A3.A) τ

def KerOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ∧ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q = plW p w ∧
    ∃ ξR φ, KerDat (R2 p) j (delW p w) (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi ξR (plW p w)
      (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ

def TraceOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → ∀ h P,
  ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
    (series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1)
      (princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecBase h P)

def KerRat : Prop := ∀ χ ξR ω φ, KerDat (R2 p) j (delW p w) χ ξR (plW p w) ω φ → ∀ h ∈ GfC (Vc D j), ∀ y, InCoefLat (R2 p) j h y →
  ∀ u, IsEv p j u → ∃ x, adForm (R2 p) j x (fun τ => u τ) = singleSeries (R2 p) j ω φ h y u

def LatIo : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ∀ c : ℂ, c ≠ 0 →
  IsScale p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) c → ∃ u, IsEv p j u ∧ ∀ h ∈ GfC (Vc D j),
    ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h,
      ∃ y, InCoefLat (R2 p) j h y ∧ (R2 p).ioP j (PiTensorProduct.tprod ℂ u) y = c • P

def ReadCmp : Prop := ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (e : FractionRing (ex.nch.Oe w) →+* ℂ),
  (∀ x, e (ex.nch.embW w x) = D.what₂.embLL x) →
  (∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
    e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a) →
  ∀ ν : ℂ, ν ≠ 0 → ∀ rd : Can p w j, IsCan p rd → ∀ u, IsEv p j u → ∀ f x (a : ℂ),
    rdAt p w j hρ ν f = a • ν⁻¹ • adForm (R2 p) j x (fun τ => u τ) →
      f = 0 ∨ ∃ b, e b = a ∧ ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] f : Tgt ex w j) = b • rd x

end Point

def KerOfAt : Prop := AtTw fun _ _ _ _ p w j => KerOf p w j

def TraceOfAt : Prop := AtTw fun _ _ _ _ p w j => TraceOf p w j

def KerRatAt : Prop := AtTw fun _ _ _ _ p w j => KerRat p w j

def LatIoAt : Prop := AtTw fun _ _ _ _ p w j => LatIo p w j

def ReadCmpAt : Prop := AtTw fun _ _ _ _ p w j => ReadCmp p w j

def FlatKer : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R →
  ∀ i : Fin D.R.m, VStd D i → ∀ B : Base (Vc D i) (Wc D i), B.Good → BaseOf R i B →
  ∀ ξ ξR ω φ, KerDat R i ξ B.de.chi ξR B.de.Q ω φ → (∃ t, B.de.Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 →
    (∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i B.de.Q z ∧ UnitOff N c ∧
      ∀ h P, series B.F ω (princ B).vecBase h P = c • series B.F ω φ (h * z) P

def CentLat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
  (z : GA D (Vc D i)), IsCentAt i Q z → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ m : ℕ, ∀ h ∈ GfC (Vc D i), ∀ y, (InCoefLat R i h y → InCoefLat R i (h * z) ((N : ℂ) ^ m • y)) ∧
      (InCoefLat R i (h * z) y → InCoefLat R i h ((N : ℂ) ^ m • y))

def TraceRat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.LUnif →
  ∀ (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec), IsExtVec (R.MW i (sg0 D A)) v₀ →
  ∀ ξ χ ξR Q ω φ, KerDat R i ξ χ ξR Q ω φ → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) h y
    (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ), (∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) →
    ∀ x, adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u →
      ∃ x', ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i x' (fun τ => v τ) = levelTrace R i U ψ (singleSeries R i ω φ h y v)

def OwnUnit : Prop := ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl), IsUnit ((ownAt D (D.plEq w) : ℕ) : c.Oe w)

end GlobalTheory.BigOn.Exp.SerBase
