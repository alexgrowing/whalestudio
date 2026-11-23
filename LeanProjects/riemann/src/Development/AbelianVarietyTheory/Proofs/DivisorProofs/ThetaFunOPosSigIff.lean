import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω where
  std := h.std
  hecS := h.hecS
  hecT := h.hecT
  resS := h.resS
  resT := h.resT
  om_pres p f hf := (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
  om_heis g k w f hf := h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_aut γ hγ γ' hγ' f hf := h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_cont f hf := h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_unit μ 𝓕 h1 h2 p f hf := h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_split e he g k h1 h2 x y h3 h4 :=
    (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
      hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) where
  rank := hX.rank
  rank' := hX.rank'
  std := hX.std
  std' := hX.std'
  stdW := hX.stdW
  is :=
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
