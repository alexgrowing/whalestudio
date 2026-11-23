import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreSt

noncomputable section

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory.ArcQ GlobalTheory.LamF

structure Known : Prop where
  laws : Out.Laws
  laws2 : Out.Laws2
  ubc : Out.UnifBaseChangeSt
  laws5 : Out.Laws5
  theta : ThetaUnifAV
  n1ab : N1ab
  n1c : N1c
  n5 : ToroidalArchimedeanCondition
  models : PartI
  hom : GlobalTheory.CM.HomExtDvr
  key : KeyFormula
  cm : GlobalTheory.CM.CMExistsSt
  deg : GlobalTheory.CM.DegSt
  ev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c

section Pre

variable {R : Type} [CommRing R] [IsDomain R] (D₀ : Out.DegPre R) (n : ℕ)

def IsSplit (sB : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T) : Prop :=
  (∀ T b, (sB T b).b = b ^ n) ∧ (∀ T b b', Out.GtPt.IsAdd (sB T b) (sB T b') (sB T (b * b'))) ∧
    ∀ (T T' : Over (Sp R)) (h : T' ⟶ T) b, Out.GtPt.IsPull h.left (sB T b) (sB T' (h ≫ b))

def TauCan : Prop := ∃ hc : ∀ y, D₀.c y ^ n = 1, ∀ y y', GlobalTheory.TauTwist.kappa hc y y' = 1

end Pre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def ModelsAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∃ Y : Model Xo c (c.V W).subtype, Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L

section Num

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]

structure CMPart (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (th : a.D₀.P.L.Sec) : Type 1 where
  B : Out.PolAV (Sp (𝓞 K₁))
  oa : letI := H.starRing; B.OAct (𝓞 E)
  AΨ : Out.PolAV (Sp (𝓞 K₁))
  oaΨ : letI := H.starRing; AΨ.OAct (𝓞 E)
  A' : Out.PolAV (Sp (𝓞 K₁))
  oa' : letI := H.starRing; A'.OAct (𝓞 E)
  φΨ : Fin (Dw.p - 1) → (AΨ.A ⟶ B.A)
  φ' : Fin (Dw.q - 1) → (A'.A ⟶ B.A)
  hΨ : Fin (Dw.p - 1) → 𝓞 E
  h' : Fin (Dw.q - 1) → 𝓞 E
  g_pos : 1 ≤ a.D₀.P.g
  th_nz : ThNZ th
  v : Fin a.D₀.P.g → (epsR K₁ ⟶ a.D₀.P.A)
  basis : IsLieBasis v
  xΨ : KeyIn K₁
  x' : KeyIn K₁
  φB : a.D₀.P.A.left ⟶ B.A.left
  φΨg : xΨ.P.A.left ⟶ AΨ.A.left
  φ'g : x'.P.A.left ⟶ A'.A.left
  τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}
  τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}
  ℓΨ : Fin xΨ.P.g → MLine K₁
  ℓ' : Fin x'.P.g → MLine K₁
  Tl : MLine K₁
  LamL : MLine K₁

variable {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)} {th : a.D₀.P.L.Sec}

abbrev CMPart.xB (m : CMPart a th) : KeyIn K₁ :=
  ⟨a.D₀.P, m.g_pos, a.D₀.rig, a.D₀.rig_gen, th, m.th_nz, m.v, m.basis⟩

abbrev CMPart.obj (m : CMPart a th) : letI := H.starRing; LamObj c (Dw.p - 1) (Dw.q - 1) :=
  letI := H.starRing
  LamObj.mk (c := c) K₁ m.B m.oa m.AΨ m.oaΨ m.A' m.oa' m.φΨ m.φ' m.hΨ m.h' m.xB m.xΨ m.x' m.φB m.φΨg m.φ'g m.τΨ m.τ'
    m.ℓΨ m.ℓ' m.Tl m.LamL

structure CMIn (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁))
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ)
    extends CMPart a th where
  good : letI := H.starRing; LamObjGood toCMPart.obj (Module.finrank ℚ E / 2) La
  act : letI := H.starRing; ∀ x, (a.oa.onB.act x).left ≫ φB = φB ≫ (oa.act x).left
  L : letI := H.starRing; LamLetters toCMPart.obj
  L_good : letI := H.starRing; L.IsGood
  n_pos : 0 < n'
  tau : TauCan a.D₀ n'
  sB : ∀ T : Over (Sp K₁), (T ⟶ a.D₀.P.A) → Out.GtPt a.D₀ T
  split : IsSplit a.D₀ n' sB
  rk : Module.finrank (𝓞 E) a.D₀.X = 1
  ξ : Module.Dual ℤ a.D₀.X
  ξ_ne : ξ ≠ 0
  ν₀ : E
  beta : BetaAt ξ l.M' a.be ν₀ jj
  tr : ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁
  kind : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Option (Fin a.D₀.P.g)
  full : letI := H.starRing; ∀ τ, Function.Injective (kind τ) ∧ (∃ k, kind τ k = none) ∧
    ∀ m, (∃ k, kind τ k = some m) ↔ (L.e.symm m).1 = τ
  tan : ∀ τ k, GtTanR (e τ k)
  xi : ∀ τ k, kind τ k = none → (e τ k).b = Out.DegPre.zeroT a.D₀ (epsR K₁) ∧
    ∀ x, DlogTan (e τ k) x (labK c K₁ τ (cc (pairE ξ x)))
  eta : letI := H.starRing; ∀ τ k m, kind τ k = some m → ∃ w : epsR K₁ ⟶ a.D₀.P.A, L.IsLetter m w ∧
    Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) w) (e τ k)

variable {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}

def CMIn.line (s : CMIn a e th jj n' La c₁) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) : MLine K₁ :=
  letI := H.starRing
  (s.kind τ k).elim MLine.one fun m => s.L.ℓ m

def CMIn.valLine (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ) : MLine K₁ :=
  (s.Tl.dual.pow n).tensor (MLine.prodPow (fun v : ArcLt Dw => s.line v.1 v.2.2) mo).dual

def Std (d : ArcDatum Xo c K₁) : Prop := d.OverBase ∧ d.Normal 1 ∧ PushInvertible d.Y.t.G d.Y.t.PP.L

def Fam (n' : ℕ) (La c₁ : ℝ) (d : ArcDatum Xo c K₁) : Prop := Std d ∧ Nonempty (CMIn d.a d.e d.th d.jj n' La c₁)

end Num

def absA (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))

def archP (E : Type) [Field E] [NumberField E] (r : ℕ) (La c₁ : ℝ) : ℝ :=
  Real.log (max 1 c₁) / 2 + Real.log La + Real.log (rdE E) + Real.log r

section Comparison₂

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ]

def TieC (Uw : UnfWit U) {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β))
    (ξ : Module.Dual ℤ a.D₀.X) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (w₁ : ℂ) (s : (U.X k).Ψ → ℂ) (hs : (U.X k).flow ξ' s x ∈ (U.X k).dom)
      (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (t : (Uw.F.Di Ha.i).La) (t' : (Uw.F.Di (Uw.ik k)).La),
      Ha.T < w₁.im ∧ (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k t' : Fin r → E) = ξ' ∧
      Uw.Pm k ⟨_, hs⟩ t' = L (Ha.Pw w₁ t) ∧
      Uw.F.u Ha.i (Ha.Pw w₁) = Uw.F.u (Uw.ik k) (Uw.Pm k ⟨_, hs⟩) ∧
      ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k ⟨_, hs⟩) (L z)).left = (Uw.F.ex Ha.i (Ha.Pw w₁) z).left

def Comparison₂ (Uw : UnfWit U) {K₁ : Type} [Field K₁] [Algebra c.F K₁]
    (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (σ₁ : K₁ →+* ℂ) (ξ : Module.Dual ℤ a.D₀.X)
    (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) : Prop :=
  ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (p : Out.IsPullDeg σ₁ a.D₀ aC.D₀) (ξC : Module.Dual ℤ aC.D₀.X),
    InBC σ₁ a aC p ∧ (∀ y, ξC y = ξ (p.xe y)) ∧
    ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x

def OnOrbit (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) :
    letI := H.starRing
    ∀ (A : AnArc (𝓞 E)) (_ : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (_ : Module.Dual ℤ A.X), Prop :=
  letI := H.starRing
  fun A gam ξ =>
    (∀ v v', A.EF (gam v) (gam v') = (Uw.F.Di (Uw.ik k)).EF v v') ∧
    (∃ t', (Uw.φ k t' : Fin r → E) = ξ' ∧ ∀ v, -(Uw.F.Di (Uw.ik k)).EF t' v = ξ (gam v).y) ∧
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → ∃ (s : (U.X k).Ψ → ℂ) (hs : (U.X k).flow ξ' s x ∈ (U.X k).dom)
      (h : (Fin Uw.g → ℂ) ≃ₗ[ℂ] A.V), ∀ v, h (Uw.Pm k ⟨_, hs⟩ v) = A.Pw w (gam v)

end Comparison₂

def NumGood {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ)
    (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁]
    (φ : V →ₗ[K] K₁) : Prop :=
  ∃ N : MLine K₁, N.Good ∧ N.ndeg ≤ Bdeg ∧ (∀ σ : K₁ →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) ∧
    (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ F ∈ M, φ F ≠ 0 →
      -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤ (ordAt w (φ F) : ℝ) - (FractionalIdeal.count K₁ w N.I : ℝ)) ∧
    ∀ σ : K₁ →+* ℂ, ∀ F ∈ M, φ F ≠ 0 →
      Real.log ‖σ (φ F)‖ + Real.log (N.n σ) ≤ Real.log (S (σ.comp (algebraMap K K₁)) F) + Carch

def nQ (E : Type) [Field E] [NumberField E] (r g NA NC : ℕ) (c₁ w : ℝ) : ℕ :=
  ⌈1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) NA NC (flowEpsilonBound g (dE E) (fdeg E) NA NC c₁ w) / d6rh c₁ w⌉₊ + 1

def LaQ (E : Type) [Field E] [NumberField E] (r p0 g NA NC : ℕ) (c₁ w : ℝ) : ℝ :=
  max 1 (d6La r p0 (fdeg E) (dE E) (flowEpsilonBound g (dE E) (fdeg E) NA NC c₁ w) (d6rh c₁ w))

end GlobalTheory.ArcCM
