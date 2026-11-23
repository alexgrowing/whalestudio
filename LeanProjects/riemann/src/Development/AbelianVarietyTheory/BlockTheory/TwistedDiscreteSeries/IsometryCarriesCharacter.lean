import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev mmul {A : Type} [CommRing A] {l m n : ℕ} (x : Matrix (Fin l) (Fin m) A) (y : Matrix (Fin m) (Fin n) A) :
    Matrix (Fin l) (Fin n) A := x * y

def IsIsom (V V' : HSp D) (R : Type) [CommRing R] [Algebra D.host.F R]
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] R)) : Prop :=
  Function.Bijective j.mulVec ∧
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig R) j * V'.gram.map (Formalism.UG.inclE (F := D.host.F) R) * j =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) R)

def IsLocLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) : Prop :=
  IsIsom V V' (v.adicCompletion D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _)

def IsLatIsom (V V' : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  IsIsom V V' (Formalism.L2.Herm.Af D.host.F) j ∧
    j.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) = (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _)

def OnePlaceOver (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∀ PP ∈ T, ∀ PP' ∈ T, ¬ IsConjPl PP PP'

def MatchesAt (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D))
    (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) : Prop :=
  ∃ u : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    mmul β'.val (u.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = mmul j β.val ∧
      ∀ PP ∈ T, ∀ a b, Formalism.L2.DIV.resS D.host.F PP (u a b) = if a.val = b.val then 1 else 0

def castDat {n n' : ℕ} (h : n = n') (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Formalism.L2.DIV.LevDat D.host.E ℂ n' where
  r := L.r
  hr := L.hr.trans h.le
  t := L.t
  s := L.s
  Pg := L.Pg
  Q := L.Q
  P := L.P
  cg := L.cg
  xq := L.xq

def IsConjBy (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (φ : GfC V ≃ₜ* GfC V') : Prop :=
  ∀ g : GfC V, mmul (finE V' (φ g : GA D V')).val j = mmul j (finE V (g : GA D V)).val

def inA (V : HSp D) (R : Finset (GfC V)) : Finset (GA D V) := R.map (Function.Embedding.subtype _)

def imA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) : Finset (GA D V') :=
  inA V' (R.map φ.toEquiv.toEmbedding)

def ReadIn {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (T : Set (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∀ PP ∈ L.Pg, PP ∈ T) ∧ ∀ PP ∈ L.Q, PP ∈ T

structure Carries (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (M : ℕ) (T : Set (Formalism.L2.DIV.Pl D.host.E))
    (φ : GfC V ≃ₜ* GfC V') : Prop where

  stabLoc : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V),
    Formalism.UG.bc (Formalism.UG.prV v) (finE V (g : GA D V)) ∈ Formalism.UG.levelVL D.sp.cm.sig V.gram v Λ ↔
      Formalism.UG.bc (Formalism.UG.prV v) (finE V' (φ g : GA D V')) ∈ Formalism.UG.levelVL D.sp.cm.sig V'.gram v Λ'

  supp : ∀ (f : Formalism.L2.Theta.AE D) (g : GfC V), SuppF V f (g : GA D V) ↔ SuppF V' f (φ g : GA D V')

  det : ∀ g : GfC V, (Formalism.L2.Theta.mt V' (φ g : GA D V')).det = (Formalism.L2.Theta.mt V (g : GA D V)).det

  lev : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V,
    (g : GA D V) ∈ levG V β L ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L)

  chi : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ g : GfC V, (g : GA D V) ∈ levG V β L →
    levChi V' β' (castDat h L) (φ g : GA D V') = levChi V β L (g : GA D V)

  lift : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T → ∀ (g0 : Formalism.L2.DIV.G0 L.Pg L.r) (g : GfC V),
    IsLevelLift V β L g0 (g : GA D V) ↔ IsLevelLift V' β' (castDat h L) g0 (φ g : GA D V')

  sph : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (M : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) →
    ∀ g : GfC V, (g : GA D V) ∈ KsphC V S ↔ (φ g : GA D V') ∈ KsphC V' S

  heckeElt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → Formalism.L2.NTheta.IsIdemAt e P → ∀ g : GfC V,
    Formalism.L2.NTheta.IsHeckeElt V e ϖ k (g : GA D V) ↔ Formalism.L2.NTheta.IsHeckeElt V' e ϖ k (φ g : GA D V')

  heckeAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ), (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ g : GfC V,
    IsHeckeAt V P k (g : GA D V) ↔ IsHeckeAt V' P k (φ g : GA D V')

  divAt : ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → IsPrimeIdem P e f → ∀ g : GfC V,
    DivAt V e ϖ d (g : GA D V) ↔ DivAt V' e ϖ d (φ g : GA D V')

  opAt : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    IsHeckeOpAt V (levS V β L) (levChi V β L) S P k (inA V R) ↔
      IsHeckeOpAt V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P k (imA φ R)

  opFull : ∀ L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L T →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Formalism.L2.DIV.Pl D.host.E) (d : List ℤ),
    (M : 𝓞 D.host.E) ∉ P.asIdeal → ∀ R : Finset (GfC V),
    Hecke₂ V (levS V β L) (levChi V β L) S P d (inA V R) ↔
      Hecke₂ V' (levS V' β' (castDat h L)) (levChi V' β' (castDat h L)) S P d (imA φ R)

def LocalIsometry (D : D7) : Prop :=
  ∀ (V V' : HSp D), V.rank = V'.rank →
    ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)),
      Formalism.IndefR.Datum.IsSelfDualC V Λ → Formalism.IndefR.Datum.IsSelfDualC V' Λ' →
      ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ j, IsLocLatIsom V V' Λ Λ' v j

def GlobalIsometry (D : D7) : Prop :=
  ∀ (V V' : HSp D), V.rank = V'.rank →
    ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
      (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
      IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
      ∀ T : Set (Formalism.L2.DIV.Pl D.host.E), OnePlaceOver T →
        ∃ j, IsLatIsom V V' Λ Λ' j ∧ MatchesAt V V' β β' T j

def InducedIso (D : D7) : Prop :=
  ∀ (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ),
    IsSDFrame V β Λ N → IsSDFrame V' β' Λ' N' →
    ∀ (T : Set (Formalism.L2.DIV.Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)),
      IsLatIsom V V' Λ Λ' j → MatchesAt V V' β β' T j →
      ∃ φ : GfC V ≃ₜ* GfC V', IsConjBy V V' j φ ∧ Carries V V' h Λ Λ' β β' (N * N') T φ

def FiniteAdelicIdentification (D : D7) : Prop :=
  LocalIsometry D ∧ GlobalIsometry D ∧ InducedIso D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter

end
