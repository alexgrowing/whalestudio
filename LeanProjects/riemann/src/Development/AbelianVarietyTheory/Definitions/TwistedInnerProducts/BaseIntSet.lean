import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsLevDatHalfLatInd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Tow

variable {D : D7}

abbrev lat (E : ExpSet D) : AddSubgroup (WO E.V E.W) := latO E.V E.W E.ΛV E.ΛW fun _ => True

def VacE (E : ExpSet D) : Prop := VacPair E.ψ E.θ E.V E.W E.χV E.χW E.om E.ΛV E.ΛW E.sW E.f₀

def trSpan (E : ExpSet D) (e : AE D) (M : ℕ) (O : Subring ℂ) : Submodule O (WO E.V E.W → ℂ) :=
  Submodule.span O {f | ∃ y : WO E.V E.W, IsHalf e y ∧ M • y ∈ lat E ∧ f = heisO E.ψ E.V E.W y E.f₀}

def stdFock (E : ExpSet D) (f : WO E.V E.W → ℂ) : MvPolynomial (FVar D E.W.rank E.V.rank) ℂ →ₗ[ℂ] (WO E.V E.W → ℂ) :=
  pureTensorO E.ψ E.θ E.V E.W (fun _ => 1) E.sW (fun _ => 1) E.BW f

def badN (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

def ChiGood (E : ExpSet D) : Prop :=
  ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq E.χW χ ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((modN E 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def CoefRing (E : ExpSet D) (O : Subring ℂ) : Prop :=
  (∀ k : ℕ, Nat.Coprime k E.l → (k : ℂ)⁻¹ ∈ O) ∧
    ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq E.χW χ → ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      ((modN E 1 * E.l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P →
        ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧
          (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O

def PlaceIn (Λ : Subring ℂ) (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : F, la.valuation F x ≤ 1 ↔ (x : ℂ) ∈ Λ

def lamOf {O : Type} [CommRing O] [IsDomain O] (e : FractionRing O →+* ℂ) : Subring ℂ :=
  (e.comp (algebraMap O (FractionRing O))).range

section Core

variable (T : CoreJ D) (j : ℕ) (E : ExpSet D) (hW : T.V j T.σ₀ = E.W) (hr : E.W.rank = D.R.r) (w : WeightFamilies.Wt D j)

def iotaE : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin E.W.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def muE (dd : GA D E.W → ℂ) : GA D E.W → ℂ := fun g => castDict hW (T.mu j T.σ₀) g * dd g

structure Setg (ph : ℂ) (dd : GA D E.W → ℂ) : Prop where
  laws : LawsJ T
  inR : InR D j
  odd : Odd D.R.r
  wn : w.n = E.V.rank
  dom : Dom (wtA w) w.n
  last : w.LastPos
  lastD : LastPos (T.Q.Dw j) (wtA w)
  big : 8 * D.R.f * D.R.r + 4 ≤ w.n
  vac : VacE E
  chi : ChiGood E
  frame : FrameTie (T.U j T.σ₀) E.W hr (T.x₀ j T.σ₀) E.sW E.BW
  lp : E.l.Prime
  good : T.Q.l.GoodAt E.l
  lev : T.Q.l.M = E.gp 0 * E.gp 1
  gp : ∀ a, (E.gp a).Prime
  gne : E.gp 0 ≠ E.gp 1
  pde : ∀ a, (E.pde a).Prime
  cop : Nat.Coprime T.Q.l.M (badN D)
  aux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M (E.pde 0 * E.pde 1)
  pg : ∀ PP ∈ E.Pg, T.Q.l.Mb ≤ PP.asIdeal
  pd : ∀ PP ∈ E.Pd, ((E.pde 0 * E.pde 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  pdHalf : ∀ PP ∈ E.Pd, ∀ PP' ∈ E.Pd, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  ddc : IsCompFn E 1 dd
  ddfin : ∃ m : ℕ, 0 < m ∧ ∀ g, dd g ^ m = 1
  mu : MuVal E.W E.χV (muE T j E hW dd)
  muK : ∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h
  cc : CcIs E.θ E.V E.W hr (T.U j T.σ₀) (castDict hW (T.dict j T.σ₀)) (muE T j E hW dd) (T.x₀ j T.σ₀) E.om E.f₀
    fun k => ph * T.cE j T.σ₀ k
  full : ∀ f ∈ T.cuspA j (wtA w) w.n, ∃ a : ℕ, a ≠ 0 ∧ ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
    GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c la 1 ((a : T.Q.c.F) • f)

structure IsTw (ph : ℂ) (dd : GA D E.W → ℂ) (N : ℕ) (C : Cover T j T.σ₀) : Prop where
  unif : C.IsUnif
  emb : C.σ₂ = inC C.d.c₂
  pd : C.d.pd = E.pde 0 * E.pde 1 * N
  half : ∀ PP ∈ E.Pd, C.d.I ≤ PP.asIdeal
  curve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F C.d.l₂.M
  dict : IsDict C.U₂ E.W hr (castDict hW C.dict₂) (iotaE T j E hr) (T.x₀ j T.σ₀)
  frame : FrameTie C.U₂ E.W hr (T.x₀ j T.σ₀) E.sW E.BW
  cc : CcIs E.θ E.V E.W hr C.U₂ (castDict hW C.dict₂) (muE T j E hW dd) (T.x₀ j T.σ₀) E.om E.f₀ fun k => ph * C.cc₂ k

def ratSet (C : Cover T j T.σ₀) : Set (GA D E.W → ℂ) := castDict hW '' C.ratForms (wtA w) w.n

def intSet (C : Cover T j T.σ₀) (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) : Set (GA D E.W → ℂ) :=
  castDict hW '' C.intForms (wtA w) w.n {la}

def baseSet : Set (GA D E.W → ℂ) :=
  {F | ∃ f ∈ T.cuspA j (wtA w) w.n, F = castDict hW (T.phiJ j T.σ₀ (wtA w) f)}

def baseIntSet : Set (GA D E.W → ℂ) :=
  {F | ∃ f ∈ T.cuspA j (wtA w) w.n, (∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c la 1 f) ∧
    F = castDict hW (T.phiJ j T.σ₀ (wtA w) f)}

abbrev harmSet : Set (MvPolynomial (LtN (T.Q.Dw j) E.V.rank) ℂ) :=
  HHa (T.Q.Dw j).mult E.V.rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) fun τ i => wtA w (τ, i)

variable (lt : LtN (T.Q.Dw j) E.V.rank ≃ FVar D E.W.rank E.V.rank)

def ReadsAs (P : MvPolynomial (FVar D E.W.rank E.V.rank) ℂ) (Q : MvPolynomial (LtN (T.Q.Dw j) E.V.rank) ℂ) : Prop :=
  Q ∈ harmSet T j E w ∧ ∀ f, IsThetaFunO E.ψ E.V E.W f → E.fock f P = stdFock E f (MvPolynomial.rename lt Q)

variable {O : Type} [CommRing O] (C : CoefLat E O)

def CoefRat (ph : ℂ) (L : Subfield ℂ) : Prop :=
  ∀ P : C.Cf, ∃ Q, ReadsAs T j E w lt (C.rd P) Q ∧ ∀ mo, ph * Q.coeff mo ∈ L

def CoefInt (ph : ℂ) (Λ : Subring ℂ) : Prop :=
  ∃ c : ℕ, ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ∃ Q, ReadsAs T j E w lt (C.rd P) Q ∧
    ∀ mo, (E.l : ℂ) ^ c * ph * Q.coeff mo ∈ Λ

def FieldIn (dd : GA D E.W → ℂ) (L : Subfield ℂ) : Prop :=
  NumberField L ∧ (∀ x ∈ T.Q.c.F, x ∈ L) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (modN E 1) L ∧ (∀ g, dd g ∈ L) ∧ CoefRing E L.toSubring

end Core

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure ReadsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (E : ExpSet D) : Prop where
  V : E.V = Vc D i
  W : E.W = Wc D i
  ψ : E.ψ = R.ψ
  θ : E.θ = R.θ
  sW : HEq E.sW (cart (R.MW i (sg0 D A)))
  BW : HEq E.BW (onb (R.MW i (sg0 D A)))
  ΛV : HEq E.ΛV (R.ΛV i)
  ΛW : HEq E.ΛW (R.ΛW i)
  χV : E.χV = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
  χW : E.χW = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2
  om : HEq E.om (R.ωP i t)
  f₀ : HEq E.f₀ (R.vacP i)
  gp : E.gp = D.host.g
  Pg : E.Pg = R.Pg
  Pd : E.Pd = R.Q t
  pde : E.pde = ![D.host.pde, D.host.pde']

def PhaseIs (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
    (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (w : WeightFamilies.Wt D ((i : ℕ) + 1)) (ph : ℂ) : Prop :=
  ‖ph‖ = 1 ∧ ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ,
    CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
      (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc ∧
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA w) w.n, ∀ k x,
      cc k * rdU (T.U ((i : ℕ) + 1) T.σ₀) f k x = ph * T.cE ((i : ℕ) + 1) T.σ₀ k * rdU (T.U ((i : ℕ) + 1) T.σ₀) f k x

end Real

end GlobalTheory.Tow

end
