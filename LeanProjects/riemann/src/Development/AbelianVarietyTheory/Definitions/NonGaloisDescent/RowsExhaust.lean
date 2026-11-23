import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.EtaJoin

variable (D : D7)

def ratSub (μ : D.what₂.Tup) (j : ℕ) (U : Submodule ℂ (D.what₂.Mt μ j)) : Submodule D.what₂.LL (D.what₂.MtL μ j) :=
  U.comap (D.what₂.jMt μ j)

def genSet (μ : D.what₂.Tup) (j : ℕ) : Set (D.what₂.MtL μ j) :=
  {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}

def lat (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) (genSet D μ j)

def up (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL) ⊓
    (lat D μ j ⊔ (ratSub D μ j (Idx.Z0 D μ j)ᗮ).restrictScalars (𝓞 D.what₂.LL))

def low (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  lat D μ j ⊓ (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL)

def etaRat (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℚ :=
  Formalism.L2.Col.lenUW (D.plEq w) (up D μ j) (low D μ j)

def ZRat (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ratSub D μ j (Idx.Z0 D μ j) ⊔ ratSub D μ j (Idx.Z0 D μ j)ᗮ = ⊤

def SpecPr (i : D.nd.Loc) : Prop :=
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)),
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))) ∧
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ,
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)

def ZSpec (i : D.nd.Loc) : Prop :=
  ∀ P : D.naut.AV i,
    (D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i) ∨ D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ) ∧
    ∀ x, D.naut.ptV i P = some x →
      (x ∈ D.nd.Zgood i → D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ∧
      (x ∉ D.nd.Zgood i → D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ)

def TypeTie (i : D.nd.Loc) : Prop :=
  ∀ (S : Set (D.naut.AV i)) (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt (D.nd.mu i) (D.nd.j i) y ∈ (⨆ P ∈ S, D.naut.typeV i P) →
    D.nd.prMt i y ∈ D.nd.eigSum i {x | ∃ P ∈ S, D.naut.ptV i P = some x}

def TypeOrth (i : D.nd.Loc) : Prop :=
  ∀ P P' : D.naut.AV i, P ≠ P' → D.naut.typeV i P ⟂ D.naut.typeV i P'

def ThetaCut (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  D.what₂.Zj μ j ≤ LinearMap.range (D.what₂.eMt μ j)

def RowsExhaust (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i ∈ D.nd.locs j w, Formalism.MainNotions.N.AtM D.nd D.naut i σ

def SplitUnif : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

variable {D}

def HeckeScalar (M : MtFam D) (i : D.nd.Loc) : Prop :=
  ∀ (P : D.naut.AV i) (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ D.naut.typeV i P,
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = c • (M.loc i).real y

def latLoc {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Submodule (B.Oc j w) (B.V j w) :=
  Submodule.span (B.Oc j w) (B.iV j w '' genSet D (D.what₂.muTw w) j)

def LatStable {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  ∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ x ∈ latLoc B j w, B.hK j w v k x ∈ latLoc B j w

end GlobalTheory.EtaJoin
