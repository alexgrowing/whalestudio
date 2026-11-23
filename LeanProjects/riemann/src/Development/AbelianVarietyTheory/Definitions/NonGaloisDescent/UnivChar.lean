import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure RealSide (D : D7) : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [fin : Fintype Γ]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  char : R.Char3 F
  phs : ∀ j, R.phs j = 1
  guard : FWT.QGuard R.toRealDat
  valKs : GlobalTheory.RealGeo.ValKs R.toRealDat
  idem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)
  unif : R.toRealDat.LUnif
  integral : R.toRealDat.LIntegral
  inGeo : GlobalTheory.RealGeo.InGeo geo
  finT : Finite T
  host : HostHyp D
  std : ∀ j, FWT.VStd D j
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

attribute [instance] RealSide.grp RealSide.fin RealSide.alg

variable {D : D7}

structure FieldOk (X : RealSide D) : Prop where
  galois : IsGalois ℚ ↥D.LL0
  star : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0
  vals : Formalism.L2.Host.ValLL0 D X.R.C
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange
  split : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK

structure SerSide (X : RealSide D) (E : IntegralHeckeForms.XD D) : Type 1 where
  S : NX.RatDat D.ntw
  YS : NX.NExpRealS X.R X.cG S
  sup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
    x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b
  H : NX.NExpRealH X.R X.cG S YS
  reads : GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL
  del : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
      ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  Z : ExportTie YS X.geo.v₀
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  low : ∀ i (P : PlE D.host), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
    𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i
  Sb : ∀ i, ∀ P ∈ X.R.Sb, P ∈ D.ntw.S0 i
  B_range : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
    D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i)
  hk_emb : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → HkIdx i k P →
    D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)
  hk_split : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits
  off : OffRange D
  all : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b

def BaseTup {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) : Prop :=
  ∀ j b, ∃ t : X.T, X.R.xi t = (Y.Z.ρ.B i j b).de.chi ∧ X.R.Q t = (Y.Z.ρ.B i j b).de.Q

structure GalSide (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : GlobalTheory.Triple.IsTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k

section Abstract

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (rd : Rds D.nexp ρ)

structure Laws : Prop where
  faithful : ∀ i j b, Faithful (rd i j b)
  act : ∀ i j b, ActRead (rd i j b)
  hecke : ∀ i j b, HeckeRead (rd i j b)
  rat : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, Rat hρ (rd i j b)

def XiType : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b Q M, InRange D.ntw i Q → ∀ s h P, ρ.IsDatum i j b s h P →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    x ∈ Fm0 D.nexp i ((j : ℕ) + 1) b

def XiBdd : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, ρ.IsDatum i j b s h P → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    ((D.ntw.l i : D.ntw.O i) ^ c) • x ∈ D.nexp.Bsup i ((j : ℕ) + 1) b

def SpanGood (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  rd i j b x ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P}

def SumOnto (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  ∃ F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
    rd i j b x = ρ.sum i j b 0 ∅ 1 F

end Abstract

structure Inputs (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop where
  a1 : BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D)
  a2 : BlochKatoReduction.adm2 D
  a8 : BlochKatoReduction.adm8 D
  good : AllGood D.nexp
  sig : D.nexp.sig_all
  a9 : BlochKatoReduction.adm9 D N0
  a10 : BlochKatoReduction.adm10 D
  univChar : GlobalTheory.UnivChar.IsUnivChar D.nexp
  off : OffRange D
  rel : ThURel D.nexp
  l3 : IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp
  t4 : IntegralHeckeForms.admT4 D.nexp E
  type : TypeKept E
  univ : UnivSup D E
  supG : SupG D
  supFull : SupFull D
  supHk : SupHk D
  commG : CommG D
  comm : HkComm D
  ss : HkSS D
  hyp : ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i

end GlobalTheory.TwInputs

end
