import Formalism.AdmissibleDesigns.NonemptyPl

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Places
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def Vo : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.E) // v ∉ placesOver D.host.E (D.nd.l i) ∧ v ∉ D.nd.S i ∧ v ∉ D.nd.Q i}

def VS : Type := {v : HeightOneSpectrum (𝓞 D.host.E) // v ∈ D.nd.S i}

def Io (v : Vo i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def IS (v : VS i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def I (w : ℕ) : Subgroup (decs D.host.E (Aw i dc) w) :=
  (Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w)

def γQ (w : ℕ) : decs D.host.E (Aw i dc) w :=
  ⟨D.nd.gam0 i (plOf i dc w), Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i (plOf i dc w))⟩

def ζO (w : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc w)

def nQ (w : ℕ) (g : decs D.host.E (Aw i dc) w) : ℕ :=
  if h : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n then Nat.find h else 0

def QPow : Prop :=
  ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

end Places

section Ring
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def ζ (w : ℕ) : Dd.T' := ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T')

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev resU (c : Fin (D.R.t + 1)) (w : ℕ) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc) w)

def Fpos (c : Fin (D.R.t + 1)) (w : ℕ) : Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  if w ∈ qsN i dc then unrH1 (resU i dc Dd c w) (I i dc w)
  else if w ∈ rowsN i dc then
    (if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥)
  else if (c : ℕ) = 1 then unrH1 (resU i dc Dd c w) (I i dc w) else ⊥

def Fall (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (w : ℕ) :
    Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  Fin.cases (motive := fun c => Submodule (D.nd.O i) (H1z (resU i dc Dd c w))) (F0 w)
    (fun c' => Fpos i dc Dd c'.succ w) c

def c1 : Fin (D.R.t + 1) := ⟨1, by have := RepresentationBoundsCohomology.one_le_letterBlockLength D.R; omega⟩

def InertiaActsTrivially : Prop := ∀ v, ∀ g ∈ Io i v, Dd.r g = 1 ∧ Dd.χ g = 1

def LocClause (c : Fin (D.R.t + 1)) : Prop :=
  InChiLoc (Mc i Dd c) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc) (Fpos i dc Dd c) (Io i) (IS i)
    (I i dc) (γQ i dc) (ζ i dc Dd) (ζO i dc) (nQ i dc)

def CoverClause : Prop :=
  ∀ v, (∃ a, Ine (F := D.host.E) (Av v) ≤ Io i a) ∨ (∃ a, Ine (F := D.host.E) (Av v) ≤ IS i a) ∨
    ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup (decs D.host.E (Aw i dc) w),
      Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) J ∧
      Ine (F := D.host.E) (Av v) ≤ J.map (decs D.host.E (Aw i dc) w).subtype

def NoFixedVectorOffZ : Prop :=
  ∀ x', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) →
    ∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing (D.nd.O i))
        (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.E), η ≠ 0 →
      ∃ g : GE D.nd, ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η ≠ η

end Ring

end Formalism.MainNotions.N.K.QS

end
