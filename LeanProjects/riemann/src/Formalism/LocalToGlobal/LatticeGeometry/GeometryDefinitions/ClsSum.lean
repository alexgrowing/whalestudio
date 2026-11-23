import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.HermitianLattices.StatementMaj

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev SW : HSpace D.host.E := D.sp.W D.R.m

abbrev nW : ℕ := (SW D).rank

def Lam0 : Submodule (𝓞 D.host.E) (Fin (nW D) → D.host.E) :=
  Formalism.L2.Herm.crdLat (SW D) (SW D).L0

def inLoc (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GL (Fin (nW D)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) : Prop :=
  x ∈ levelVL D.sp.cm.sig (SW D).gram v (Lam0 D) ∧
    ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      Formalism.L2.Herm.InPrinc D.sp.cm (SW D) v (D.host.g i) (Lam0 D) x

abbrev GAf : Subgroup (GL (Fin (nW D)) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :=
  Formalism.L2.Herm.UAf D.sp.cm (SW D)

def Kg : Subgroup (GL (Fin (nW D)) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :=
  Subgroup.closure {x | x ∈ GAf D ∧ ∀ v, inLoc D v (bc (prV (E := D.host.E) v) x)}

def KgU : Subgroup (GAf D) := (Kg D).subgroupOf (GAf D)

def KstU : Subgroup (GAf D) :=
  (levelAfL D.sp.cm.sig (SW D).gram (Lam0 D)).subgroupOf (GAf D)

abbrev GamF : Subgroup (GAf D) := Formalism.L2.Herm.UFin D.sp.cm (SW D)

abbrev XDef : Type := ClassSet (GamF D) (KgU D)

def rep (c : XDef D) : GAf D := Quotient.out c

def GammaC (c : XDef D) : Set (GamF D) := stabAt (GamF D) (KgU D) (rep D c)

def wtC (c : XDef D) : ℝ := ((Nat.card (GammaC D c) : ℝ))⁻¹

def clsSum (f : XDef D → ℝ) : ℝ := ∑ᶠ c, wtC D c * f c

def latX (c : XDef D) : Submodule (𝓞 D.host.E) (Fin (nW D) → D.host.E) :=
  Formalism.UG.CS.globLat ((rep D c : GAf D) : GL (Fin (nW D)) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) (Lam0 D)

def embT (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def gramT (τ : D.what₂.Tau) : Matrix (Fin (nW D)) (Fin (nW D)) D.what₂.LL := (SW D).gram.map (embT D τ)

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K]

open Classical in

def frameOf {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M then h.choose else 1

open Classical in

def lineE (A : HLat K) : A.V := if h : Nonempty A.ι then A.b h.some else 0

def lineI (A : HLat K) : Submodule (𝓞 K) K :=
  Submodule.comap ((LinearMap.toSpanSingleton K A.V (lineE A)).restrictScalars (𝓞 K)) A.L

def lineN (A : HLat K) (v : InfinitePlace K) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v (lineE A)

end Frames

def TxLat (ell : D.what₂.Tau → HLat D.what₂.LL) (c : XDef D) (τ : D.what₂.Tau) :
    Submodule (𝓞 D.what₂.LL) (Fin (nW D) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) {y | ∃ a ∈ lineI (ell τ), ∃ z ∈ latX D c, y = a • (fun i => embT D τ (z i))}

def Tx (ell : D.what₂.Tau → HLat D.what₂.LL) (c : XDef D) (τ : D.what₂.Tau) : HLat D.what₂.LL where
  V := Fin (nW D) → D.what₂.LL
  ι := Fin (nW D)
  b := Pi.basisFun D.what₂.LL (Fin (nW D))
  X := fun v => (((lineN (ell τ) v)⁻¹ : ℝ) : ℂ) • frameOf ((gramT D τ).map v.embedding)
  L := TxLat D ell c τ

def degHHc (ell : D.what₂.Tau → HLat D.what₂.LL) (c : XDef D) (τ : D.what₂.Tau) : ℝ := -(Tx D ell c τ).lcv / 2

end Formalism.L2.Geo.Def
