import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

noncomputable section

namespace GlobalTheory.PendOf

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct Formalism.MainNotions.PairedCharacterCondition

structure TameOm (D : D7) where
  om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ
  om_one : ∀ k w x, x ≠ 0 → om k w x 1 = 1
  om_mul : ∀ k w x, x ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ∀ σ' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x (σ * σ') = om k w x σ * om k w x σ'
  tameInertiaChar_mul_root : ∀ k w x y, x ≠ 0 → y ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    om k w (x * y) σ = om k w x σ * om k w y σ
  om_wild : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), om k w x σ = 1
  om_open : ∀ k w x, x ≠ 0 → ∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
    ∀ σ ∈ U, σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → om k w x σ = 1
  om_inj : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x y, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x σ ≠ om k w y σ
  om_tg : ∀ k (v : D.nd.PlG k) x, x ≠ 0 →
    om k (D.naut.plGw k v) x (D.ntypes.tg k v) = D.ntypes.teichC k x

def LabIne {D : D7} (Ω : TameOm D) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol L σ =
      ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (Ω.om k w x σ)).prod

def LabChar (D : D7) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ (L χ : D.naut.LP w)
    (u : (ZMod (D.host.g k))ˣ), (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    D.naut.lpDim χ = 1 → D.naut.items₂ k w χ = X - C (u : ZMod (D.host.g k)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.lpChar L χ)) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map
        (· * algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IneRep (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    ∃ ρ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin (D.naut.lpDim L)) ℂ,
      (∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
        ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), (σ : GE D.nd) ∈ U → ρ σ = 1) ∧
      ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), D.naut.inePol L (σ : GE D.nd) =
        ((ρ σ : GL (Fin (D.naut.lpDim L)) ℂ) : Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly

def TameLP (D : D7) {w : PlE D.host} (L : D.naut.LP w) : Prop :=
  ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) →
    D.naut.inePol L σ = (X - 1) ^ D.naut.lpDim L

def LabDepth (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).Monic ∧ ((D.naut.items₂ k w L).natDegree = D.naut.lpDim L ↔ TameLP D L)

def GenFam (D : D7) (γ : Fin 2 → PlE D.host → GE D.nd) : Prop :=
  (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), TameGenAt (D.nd.plOm.1 w) (γ k w)

def LabGen (D : D7) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, GenFam D γ ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
      (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.inePol L (γ k w) =
        ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (D.ntypes.teichC k x)).prod

def DepthZ (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    TameLP D (D.naut.locV i PI w)

structure CenO (D : D7) where
  zO : ∀ i : D.nd.Loc,
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (D.nd.Mt i)
  zO_comm : ∀ i z (f : D.nd.T i), zO i z * D.nd.act i f = D.nd.act i f * zO i z
  zO_act : ∀ i (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x) →
    D.nd.prMt i y = (zO i z).baseChange (KK D.nd i) (D.nd.prMt i x)

def ZLStable (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra D.what₂.LL (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i), ∃ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef D.what₂.embLL z) (D.what₂.jMt _ _ x)

def CenInt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x ∈ GlobalTheory.EtaJoin.genSet D (D.nd.mu i) (D.nd.j i), ∃ y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) z) (D.what₂.jMt _ _ x)

def OnMtPreservesTypeV (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (z : MonoidAlgebra ℂ (G0g D.nd)), ∀ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z F ∈ D.naut.typeV i PI

def typeSum (D : D7) (i : D.nd.Loc) (o : Option (D.nd.X i)) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ P ∈ {P | D.naut.ptV i P = o}, D.naut.typeV i P

structure Sec (D : D7) (i : D.nd.Loc) where

  Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i)
  inj : Function.Injective Φ
  semi : ∀ (k : KK D.nd i) v, Φ (k • v) = (D.naut.iotaQC i (D.naut.iotaQ i k)) • Φ v
  eig : ∀ x, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, Φ u ∈ typeSum D i (some x)
  split : ∀ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i), D.what₂.jMt _ _ y - Φ (D.nd.prMt i y) ∈ typeSum D i none

def PrType (D : D7) : Prop :=
  ∀ i (PI : D.naut.AV i) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ x ∈ D.naut.typeV i PI →
    (∀ p, D.naut.ptV i PI = some p → D.nd.prMt i x ∈ heckeEig (D.nd.T i) (D.nd.act i) p) ∧
    (D.naut.ptV i PI = none → D.nd.prMt i x = 0)

def ParSurj (D : D7) : Prop :=
  ∀ i x Sig, HasParamX D.nd D.naut i x Sig →
    ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w

def SerLL (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]) (h : GL (Fin D.R.r) (ZMod (D.host.g k))),
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.ntypes.eSer k f).coeff h

def CoeffRingsHaveRootsOfUnity (D : D7) : Prop := ∀ i : D.nd.Loc, ∃ ζ : D.nd.O i, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

open Classical in

def SerEq (D : D7) (lz : ∀ k : Fin 2, LzData (D.host.g k)) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]),
    D.ntypes.eSer k f = ∑ τ : (lz k).Irr D.R.r, if (lz k).lab τ = f then (lz k).idem τ else 0

def mk {D : D7} (lz : ∀ k : Fin 2, LzData (D.host.g k)) (h1 : SerEq D lz) (h2 : SerLL D) (h3 : CoeffRingsHaveRootsOfUnity D)
    (Ω : TameOm D) (h4 : LabIne Ω) (h5 : LabChar D) (Z : CenO D) (h6 : ZLStable D) (h7 : PrType D)
    (h8 : ParSurj D) : Pend D where
  lz := lz
  eSer_eq := h1
  eSer_LL := h2
  zetaPrimitiveRoot := h3
  om := Ω.om
  om_one := Ω.om_one
  om_mul := Ω.om_mul
  tameInertiaChar_mul_root := Ω.tameInertiaChar_mul_root
  om_wild := Ω.om_wild
  om_open := Ω.om_open
  om_inj := Ω.om_inj
  om_tg := Ω.om_tg
  inertiaCharpoly_eigenvalues := h4
  inertiaCharpoly_character := h5
  zO := Z.zO
  zO_comm := Z.zO_comm
  zL_stable := h6
  zO_act := Z.zO_act
  prMt_type := h7
  Par_surj := h8
  kty i PI k v := {τ | ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((lz k).idem τ)) F ≠ 0}
  kty_spec _ _ _ _ _ := Iff.rfl

end GlobalTheory.PendOf

end
