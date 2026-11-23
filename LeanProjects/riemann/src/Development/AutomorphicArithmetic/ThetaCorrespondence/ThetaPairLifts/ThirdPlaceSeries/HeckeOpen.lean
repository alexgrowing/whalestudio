import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField
  IsDedekindDomain Polynomial
open scoped TensorProduct
structure AUSideAlt (D : D7) where
  cls : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AutRep D.host.E D.R.nV → D.nbc.AU j
  surj : ∀ j h1 h2, Function.Surjective (cls j h1 h2)
  iso : ∀ j h1 h2 π π', cls j h1 h2 π = cls j h1 h2 π' ↔ π.Iso π'
  mult : ∀ j h1 h2 π, D.nbc.multAU j (cls j h1 h2 π) = π.mult
  sph : ∀ j h1 h2 π (w : PlE D.host) v, ¬ IsSplitPl D.host w → NG.OverPl w v →
    (D.nbc.sphAU j (cls j h1 h2 π) w ↔ π.SphericalAtPlace v)
  sat : ∀ j h1 h2 π v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.nV v w), (∃ α, NG.SatAt π Dv α) →
    ∃ α, NG.SatAt π Dv α ∧ D.nbc.satAU j (cls j h1 h2 π) w = Finset.univ.val.map α
  clsWt : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AlgWt D.host.E D.R.nV → D.nbc.Wt j
  surjWt : ∀ j h1 h2, Function.Surjective (clsWt j h1 h2)
  isoWt : ∀ j h1 h2 a b, clsWt j h1 h2 a = clsWt j h1 h2 b ↔ a.Iso b
  wt : ∀ j h1 h2 π a, π.toAlgWt.IsDual a → D.nbc.wtAU j (cls j h1 h2 π) = clsWt j h1 h2 a
  infW : ∀ j h1 h2 a (τ : D.host.E →+* ℂ) lam, a.HWAt τ lam → D.nbc.infW j (clsWt j h1 h2 a) τ = NG.infOf lam
  locUnr : ∀ j h1 h2 π (s : SplitPlace D.host.E), π.SphericalAtPlace s.v → D.naut.unr (D.nbc.locAU j (cls j h1 h2 π) s.w)
  locPol : ∀ j h1 h2 π (s : SplitPlace D.host.E) (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) →
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.nbc.locAU j (cls j h1 h2 π) w) ((1 - (D.R.nV : ℝ)) / 2))
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
def AutomorphicSideRealised (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D) : Prop :=
  ∀ j h1 h2 π (s : SplitPlace D.host.E) σ, IsLocS π.S s σ → T.e s.w (D.nbc.locAU j (A.cls j h1 h2 π) s.w) =
    _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ)
def RepresentationParametersHold (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (par : D.what₂.FT → ∀ w : PlE D.host, GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w))
    (sat : D.what₂.FT → PlE D.host → Multiset ℂ) : Prop :=
  (∀ σ (s : SplitPlace D.host.E) τ, IsLocS (rep σ).S s τ →
    par σ s.w = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ)) ∧
  ∀ σ v (w : PlE D.host), NG.OverPl w v → ∀ Dv : InertDatum D.host.E D.R.r v w, (∃ α, NG.SatAtS (rep σ).S Dv α) →
    ∃ α, NG.SatAtS (rep σ).S Dv α ∧ sat σ w = Finset.univ.val.map α
end
structure CharFrameHostEmbedding (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) where
  bare : IsEmpty D.nd.Loc
  wdT : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D wdT
  chr : CharSide D cf
  row : RowSide D
  pl : PlSide D
  iota : IotaOk D pl
  wd : WDSide D wdT
  grp : GrpSide D
  par : ParSide D jE
  au : _root_.GlobalTheory.HeightCounting.AUSideAlt D
  chiT : ChiTOk D cf
section Loc
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000 in
structure AutomorphicSpecialisation {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D)
    (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) {X : LocNd (lay0 D)}
    (iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)) (Y : LocAut X) (Cb : LocBC Y) where
  iotaQ : ∀ i, Y.naut.iotaQ i = iq i
  iotaQC : ∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))
  kFbar : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ A.pl.plB (X.nd.w i),
    fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out
      (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) =
      Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)
  locW : ∀ i σ w, Y.locW i σ w = A.row.locR σ w
  satW : ∀ i σ w, Y.satW i σ w = A.row.satR σ w
  wdOf : ∀ (i : X.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (X.nd.l i))) w,
    Y.wdOf i r w = A.wd.wdOf (X.nd.l i) (Y.naut.iotaQC i) r w ∧
    (Y.IsCrysW i r w ↔ A.wd.IsCrysW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    (Y.IsPotCrysW i r w ↔ A.wd.IsPotCrysW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    (Y.IsdRW i r w ↔ A.wd.IsdRW (X.nd.l i) (Y.naut.iotaQC i) r w) ∧
    ∀ τ, Y.jumpsW i r τ = A.wd.jumpsW (X.nd.l i) (Y.naut.iotaQC i) r τ
  muC : ∀ i (j : Fin D.R.m), j.1 + 1 = X.nd.j i → (A.chr.e1 (Y.muC i)).1 = tup (X.nd.mu i) j
  S : ∀ i, Y.naut.AV i → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)
  irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (S i P)
  inj : ∀ i P P', NG.IsoRep (S i P) (S i P') → P = P'
  surj : ∀ i S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ →
    ∃ P, NG.IsoRep (S i P) S'
  typeV : ∀ i P, Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ (S i P)).comap (mlX M X i).real
  ptV : ∀ i P x, Y.naut.ptV i P = some x ↔ ∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ Y.naut.typeV i P,
    NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = iotaO X.nd Y.naut i ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y
  emb : ∀ i P, Cb.embAV i P = A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := S i P, irrS := irr i P }
end Loc
structure HeckeOpenStatements (D : D7) (mt : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) where
  hecke : HeckeTied D mt
  av : AVTied D mt
  au : _root_.GlobalTheory.HeightCounting.AUSideAlt D
  emb : ∀ i P, D.nbc.embAV i P = au.cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (av.rep i P)
  rational : HeckeRational D mt
  level : LevelTied D mt tup
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D mt
structure NormChoiceConstructed (hLL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) where
  D : D7
  cf : CharFrame D
  jE : D.host.E →+* Qb
  A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hLL D A.wdT
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hLL D A.wdT A.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hLL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  low : Finset ℕ
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  S : RatDat D.ntw
  hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)
  eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0
  θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ
  Bs : SideB D cf A.row low Pq S hL eig θ
  M : MtFam D
  C : NChoice D
  tp : TupTied D cf C
  ch : ChoiceSide D cf M Bs.exp C tp
  mt : MtInput D M tp.tup C.Q
  big : D.what₂.places.Pl → Finset ℂ
  L : LocAll (lay0 D)
  Sp : NdSpec A.pl M C big L.X L.T
  Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C
  ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
  eq : D' = withLoc L
structure NormChoiceRealisation (hLL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (cf' : CharFrame D') (C' : NChoice D') (tp' : TupTied D' cf' C')
    extends toNBuilt : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hLL D' where
  pack : (⟨D', cf', C', tp'⟩ : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁) =
    ⟨withLoc L, cfL L cf, chL L C, tpL L tp⟩
end GlobalTheory.HeightCounting
end
end
