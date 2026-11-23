import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

instance isOpenImmersion_cellFl (w : ι → Equiv.Perm (Fin N)) :
    IsOpenImmersion (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) :=
  GlobalTheory.isOpenImmersion_cell _ _ _ _ _ w

abbrev R (ι : Type) [Fintype ι] (N : ℕ) : Type := CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd

def cellU (w : ι → Equiv.Perm (Fin N)) : (Fl ι N).Opens := cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w ''ᵁ ⊤

def cellHom (w : ι → Equiv.Perm (Fin N)) : R ι N →+* Γ(Fl ι N, cellU w) :=
  ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (R ι N))).inv.hom

def cellMat (w : ι → Equiv.Perm (Fin N)) (τ : ι) : GL (Fin N) Γ(Fl ι N, cellU w) :=
  Matrix.GeneralLinearGroup.map (cellHom w) (cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w τ)

def colOn {X : Scheme.{0}} {U : X.Opens} (M : Matrix (Fin N) (Fin N) Γ(X, U)) (j : Fin N) : Γ(freeModule X (Fin N), U) :=
  ∑ i, M i j • resM (freeModule X (Fin N)) le_top (VB.freeFrame X (Fin N) i)

def colU (w : ι → Equiv.Perm (Fin N)) (τ : ι) (j : Fin N) : Γ(freeModule (Fl ι N) (Fin N), cellU w) :=
  colOn (cellMat w τ).1 j

end GlobalTheory.FlagZ.TautCell
