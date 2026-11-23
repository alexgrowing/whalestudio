import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def nfE (D : D7) : ℕ := Fintype.card (InfinitePlace D.host.E)

def plE (D : D7) : Fin (nfE D) ≃ InfinitePlace D.host.E := (Fintype.equivFin _).symm

def tauE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Fin (nfE D) ≃ InfinitePlace X.B.I.F :=
  (plE D).trans (e.trans X.pl.symm)

def embE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) : D.host.E →+* ℂ :=
  (X.B.I.φ (tauE X e j)).comp X.ιE.symm.toRingHom

def PlaceTie (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Prop :=
  ∀ x : InfinitePlace D.host.E, InfinitePlace.mk ((X.B.I.φ (X.pl.symm (e x))).comp X.ιE.symm.toRingHom) = x

theorem hembE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (h : PlaceTie X e) (j : Fin (nfE D)) :
    InfinitePlace.mk (embE X e j) = plE D j := h (plE D j)

def castLoc (u : D.what₂.Word) {v w : InfinitePlace X.B.I.F} (h : v = w) : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u w := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

theorem tauE_symm (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (v : InfinitePlace X.B.I.F) :
    X.pl.symm (e (plE D ((tauE X e).symm v))) = v := by
  simp [tauE]

def carrierInOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    CarrierIn X u u' where
  Wp := fun x => X.Vloc u (X.pl.symm (e x))
  Wq := fun x => X.Vloc u' (X.pl.symm (e x))
  nf := nfE D
  pl := plE D
  emb := embE X e
  hemb := hembE X e he
  G := Formalism.L2.SG.SpectralTiesReal.gOf D e
  CA := CA
  de := de
  de' := de'
  l := l
  grid := grid
  grid1 := grid1
  hv := hv
  T := T
  hT := hT
  fc := fc
  χ := χ
  sg := sg
  ν' := ν'
  m₀ := m₀
  top := top
  A₀ := A₀
  τ := tauE X e
  Q := fun v => Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  Qi := fun v => Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  eP := fun v => castLoc X u (tauE_symm X e v)
  eQ := fun v => castLoc X u' (tauE_symm X e v)

end Formalism.L2.SG.Pf.Carrier
