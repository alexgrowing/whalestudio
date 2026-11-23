import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import Formalism.LocalToGlobal.ProjectiveLattices.LieArcSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev Wit (Y : Model Xo c β) {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} (a : ArcIn Dw l β A b)
    (χ : Sp (PowerSeries A) ⟶ Y.X) :=
  ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ

section Gt

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

def GtTanR (ν : Out.GtPt D₀ (epsR A)) : Prop :=
  ∃ g₀ : Out.GtPt D₀ (Over.mk (𝟙 (Sp A))), g₀.IsZero ∧
    Out.GtPt.IsPull (spMap (TrivSqZeroExt.fstHom A A A).toRingHom) ν g₀

def GtComb {m : ℕ} (cf : Fin m → A) (e : Fin m → Out.GtPt D₀ (epsR A)) (ν : Out.GtPt D₀ (epsR A)) : Prop :=
  ∃ (u : Fin m → Out.GtPt D₀ (epsR A)) (p : Fin (m + 1) → Out.GtPt D₀ (epsR A)),
    (∀ i, Out.GtPt.IsPull (spMap (epsScaleR (cf i))) (e i) (u i)) ∧ (p 0).IsZero ∧
    (∀ i : Fin m, Out.GtPt.IsAdd (p i.castSucc) (u i) (p i.succ)) ∧ p (Fin.last m) = ν

def ThMul (γ : A) (th th' : D₀.P.L.Sec) : Prop := ∀ j, th'.f j = constFn D₀.P.A.hom _ γ * th.f j

def ThNZ (th : D₀.P.L.Sec) : Prop := ∀ y, ∃ x, D₀.P.A.hom x = y ∧ x ∈ Out.nonzeroLocus th

variable {A' : Type} [CommRing A'] [IsDomain A'] {D₁ : Out.DegPre A'} {f : A →+* A'}

abbrev prj (p : Out.IsPullDeg f D₀ D₁) : D₁.P.A.left ⟶ D₀.P.A.left :=
  p.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf f)

def LetBC (p : Out.IsPullDeg f D₀ D₁) (ν : Out.GtPt D₀ (epsR A)) (ν₁ : Out.GtPt D₁ (epsR A')) : Prop :=
  ν₁.b.left ≫ p.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf f) = spMap (dualMap f) ≫ ν.b.left ∧
    ∀ χ : D₁.X, ∃ hψ : ∀ i : Fin 4,
        Out.DegPre.gtφT D₁ (epsR A') ν₁.b χ i ≫ p.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf f) =
          spMap (dualMap f) ≫ Out.DegPre.gtφT D₀ (epsR A) ν.b (p.xe χ) i,
      LB.Gen.Maps (LB.linCombIso p.w _ Out.DegPre.gtε) (ν₁.s χ)
        (Out.GeneratorPullback.pullAlong D₀.P.L (p.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf f)) (spMap (dualMap f)) _
          Out.DegPre.gtε _ hψ (ν.s (p.xe χ)))

def ThBC (p : Out.IsPullDeg f D₀ D₁) (th : D₀.P.L.Sec) (th₁ : D₁.P.L.Sec) : Prop :=
  ∃ θ₂ : LB.Sec (D₀.P.L.pull (p.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf f))),
    PullSec _ th θ₂ ∧ IsoMaps p.w th₁ θ₂

end Gt

def InBC {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}
    (f : A →+* A') (a : ArcIn Dw l β A b) (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀) : Prop :=
  b' = f.comp b ∧ (∀ (x : 𝓞 E) (y : a'.D₀.X), p.xe (x • y) = x • p.xe y) ∧
    (∀ y z : a'.D₀.X, a'.be y z = a.be (p.xe y) (p.xe z)) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (a.oa.onB.act x).left) ∧
    (∀ v, GlobalTheory.ArcPull.IsPullQk p (a.eta v) (a'.eta v)) ∧ ∀ v, GlobalTheory.ArcPull.IsPullQk p (a.etaA v) (a'.etaA v)

section ThetaShiftProofs

variable {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X}

def LieImg (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
    (κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)))
    (vn : Sp (DualNumber (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))) ⟶
      (Out.thickObj (PowerSeries A) (Ideal.span {PowerSeries.X}) n W.t.G).left),
    (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
    (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
    κ DualNumber.eps = DualNumber.eps →
    vn ≫ (Out.thickObj (PowerSeries A) (Ideal.span {PowerSeries.X}) n W.t.G).hom =
      spMap (algebraMap (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
        (DualNumber (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)))) →
    vn ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ))

def ThetaOf (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) : Prop :=
  ∃ (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ' : LB.Sec W.P.U.LG.L),
    (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)) ∧
    SectionOfLineBundleOne σ θ' ∧ HEq θ θ'

def ArcBasis (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A))
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) : Prop :=
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries A) ⟶ W.t.G),
    (∀ τ k, LieImg W (e τ k) (v τ k)) ∧
    ∀ τ : E →+* ℂ,
      let eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop := fun w => ∀ x : 𝓞 E,
        (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (ρ τ x))) ≫ w.left
      (∀ k, IsTangent (v τ k) ∧ eig (v τ k)) ∧
      ∀ w, IsTangent w → eig w → ∃! cf : Fin (Dw.mult τ) → PowerSeries A, IsLieComb cf (v τ) w

def IsArcFr (W : Wit Y a χ) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec)
    {S : Type} [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y : FrPt Xo c S) : Prop :=
  ∃ (z : Sp S ⟶ Xo.XF c) (t' : SAB H (Sp S)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' W.t (spMap ι))
    (φ : t'.G.left ⟶ Y.oF.t.G.left),
    z ≫ Y.j = spMap ι ≫ χ ∧ z ≫ pullback.fst _ _ = y.x ∧ φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z ∧
    φ ≫ Y.m0.toSABMap.φ = m1.φ ∧ φ ≫ Y.m.φ = m2.φ ≫ W.m.φ ∧
    (∀ τ k, ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (u' : Sp (DualNumber S) ⟶ t'.G.left),
      LieImg W (e τ k) v ∧ u' ≫ m1.φ = y.u τ k ∧ u' ≫ m2.φ = spMap (dualMap ι) ≫ v.left ∧
      u' ≫ t'.G.hom = spMap (algebraMap S (DualNumber S))) ∧
    ∃ (θ : LB.Sec W.t.PP.L) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ))
      (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)),
      ThetaOf W th θ ∧ RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : t'.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))

def WitBC {A' : Type} [CommRing A'] [IsDomain A'] {b' : O →+* A'} {a' : ArcIn Dw l β A' b'} (f : A →+* A')
    (p : Out.IsPullDeg f a.D₀ a'.D₀) (W : Wit Y a χ) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)) : Prop :=
  ∃ (hD₁ : Out.IsPullDeg (PowerSeries.map f) W.P.D.toPre W'.P.D.toPre)
    (bc : W'.t.G ≅ (Over.pullback (Out.specOf (PowerSeries.map f))).obj W.t.G), IsMonHom bc.hom ∧
    Out.IsPullUnif (PowerSeries.map f) hD₁ bc W.P.U W'.P.U ∧
    W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map f))) ≫ W.m.φ ∧
    (∀ y, hD₁.xe (W'.e y) = W.e (p.xe y)) ∧ W'.φ ≫ prj p = prj hD₁ ≫ W.φ ∧
    ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (prj hD₁ ≫ W.φ)))
      (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ prj p))),
      HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri p.w W'.w w₂

end ThetaShiftProofs

def letM (Dw : Datum H) (K : Type) [Field K] (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (ArcS Dw K) := Matrix.of fun i k => arcX Dw K τ i k

def cst (Dw : Datum H) {K : Type} [Field K] (x : K) : ArcS Dw K := arcι Dw K (PowerSeries.C (R := K) x)

structure ArcDatum (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K₁)] where

  Wp : ValuationSubring ℂ

  Y : Model Xo c (c.V Wp).subtype

  a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)

  χ : Sp (PowerSeries K₁) ⟶ Y.X

  W : ArcWit Y (a.restrict (c.V Wp).subtype) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ

  e : ∀ τ, Fin (Dw.mult τ) → Out.GtPt (a.restrict (c.V Wp).subtype).D₀ (epsR K₁)

  yF : FrPt Xo c (ArcS Dw K₁)

  th : (a.restrict (c.V Wp).subtype).D₀.P.L.Sec

  arcDatum_isArc_point_basis : IsArcPointPowerSeries Y (a.restrict (c.V Wp).subtype) χ W e yF

  isArc3 : IsArcPt3At Y (a.restrict (c.V Wp).subtype) χ W yF th

  μ : ArcLt Dw →₀ ℕ

  jj : ℤ

variable {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

def ArcDatum.OverBase (d : ArcDatum Xo c K₁) : Prop :=
  d.χ ≫ d.Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap ((algebraMap c.F K₁).comp (c.V d.Wp).subtype)

theorem ArcDatum.overBase (d : ArcDatum Xo c K₁) : d.OverBase := d.arcDatum_isArc_point_basis.1

def ArcDatum.Normal (d : ArcDatum Xo c K₁) (ζ : K₁) : Prop :=
  ∃ y₀ : FrPt Xo c (ArcS Dw K₁), IsArcFr d.W d.e d.th (arcι Dw K₁) y₀ ∧
    GlobalTheory.Frames.FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF

def ArcDatum.IsPullOf {K' K₁ : Type} [Field K'] [Algebra c.F K'] [Field K₁] [Algebra c.F K₁]
    [Algebra c.F (ArcS Dw K')] [Algebra c.F (ArcS Dw K₁)]
    (f : K' →+* K₁) (d : ArcDatum Xo c K') (d₁ : ArcDatum Xo c K₁) : Prop :=
  algebraMap c.F K₁ = f.comp (algebraMap c.F K') ∧
  ∃ p : Out.IsPullDeg f d.a.D₀ d₁.a.D₀, InBC f d.a d₁.a p ∧
    (∀ ψ : FractionRing K' →+* FractionRing K₁, ψ.comp (algebraMap K' _) = (algebraMap K₁ _).comp f →
      (∀ v, p.xe (d₁.a.eta v).y = (d.a.eta v).y ∧
        (d₁.a.eta v).g.b.left ≫ p.e.hom.left ≫ pullback.fst d.a.D₀.P.A.hom (Out.specOf f) =
          spMap ψ ≫ (d.a.eta v).g.b.left) ∧
      (∀ v, p.xe (d₁.a.etaA v).y = (d.a.etaA v).y ∧
        (d₁.a.etaA v).g.b.left ≫ p.e.hom.left ≫ pullback.fst d.a.D₀.P.A.hom (Out.specOf f) =
          spMap ψ ≫ (d.a.etaA v).g.b.left)) ∧
    HEq d₁.χ (spMap (PowerSeries.map f) ≫ d.χ) ∧ (∀ τ k, LetBC p (d.e τ k) (d₁.e τ k)) ∧ ThBC p d.th d₁.th ∧
    (∀ th, IsArcPt3At d.Y (d.a.restrict (c.V d.Wp).subtype) d.χ d.W d.yF th →
      ∃ th₁ : d₁.a.D₀.P.L.Sec,
        IsArcPt3At d₁.Y (d₁.a.restrict (c.V d₁.Wp).subtype) d₁.χ d₁.W d₁.yF th₁ ∧ ThBC p th th₁) ∧
    ∃ φ : ArcS Dw K' →ₐ[c.F] ArcS Dw K₁,
      (∀ g : LaurentSeries K', ∃ g₁ : LaurentSeries K₁, (∀ m, g₁.coeff m = f (g.coeff m)) ∧
        φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K')) _ (MvPolynomial.C g)) =
          algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g₁)) ∧
      (∀ τ i k, φ (arcX Dw K' τ i k) = arcX Dw K₁ τ i k) ∧ FrMap φ d.yF d₁.yF

section Fld

variable {Y : Model Xo c β} {K : Type} [Field K] {b : O →+* K} {a : ArcIn Dw l β K b} {χ : Sp (PowerSeries K) ⟶ Y.X}

theorem lieImg_iff_isLieImage (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR K)) (v : epsR (PowerSeries K) ⟶ W.t.G) :
    LieImg W ν v ↔ IsLieImage W ν v := Iff.rfl

theorem gtTanR_iff_gtTan (ν : Out.GtPt a.D₀ (epsR K)) : GtTanR ν ↔ GtTan (a := a) ν := Iff.rfl

theorem arcBasis_iff_arcLieBasis [Algebra c.F K] (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* K))
    (hρ : ∀ τ x, ρ τ x = algebraMap c.F K (embK c τ x))
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K)) : ArcBasis W ρ e ↔ ArcLieBasis W e := by
  simp only [ArcBasis, ArcLieBasis, hρ]
  exact Iff.rfl

theorem IsArcFr.isArcPt3At [Algebra c.F K] [Algebra c.F (ArcS Dw K)] {W : Wit Y a χ}
    {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K)} {th : a.D₀.P.L.Sec}
    {y : FrPt Xo c (ArcS Dw K)} (h : IsArcFr W e th (arcι Dw K) y) (hth : ∃ j, th.f j ≠ 0) :
    IsArcPt3At Y a χ W y th := by
  obtain ⟨-, t', m1, m2, φ, -, -, -, hφ0, hφ, -, θ, w1, w2, σ', s1, θ2, hΘ, hr1, hr2, hi1, hi2, hps, hs⟩ := h
  obtain ⟨σ, fam, θ', hexp, hcoh, hσ, hθ⟩ := hΘ
  exact ⟨σ, fam, θ', θ, hth, hexp, hcoh, hσ, hθ, t', m1, m2, w1, w2, σ', s1, θ2, ⟨φ, hφ0, hφ⟩,
    hr1, hr2, hi1, hi2, hps, hs⟩

theorem IsArcFr.isFramedPoint_changed_by_letters [Algebra c.F K] [Algebra c.F (ArcS Dw K)] {W : Wit Y a χ}
    {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K)} {th : a.D₀.P.L.Sec} {ζ : ArcS Dw K}
    {y₀ y : FrPt Xo c (ArcS Dw K)} (h : IsArcFr W e th (arcι Dw K) y₀) (hc : GlobalTheory.Frames.FrChg (letM Dw K) ζ y₀ y)
    (hb : χ ≫ Y.s = spMap (PowerSeries.C (R := K)) ≫ spMap b) :
    IsArcPointPowerSeries Y a χ W e y := by
  obtain ⟨z, _t', m1, m2, φ, hzj, hzx, -, hφ0, hφ, hvec, -⟩ := h
  obtain ⟨hx, hcomb, -⟩ := hc
  choose v u' hL hu1 hu2 _hu3 using hvec
  refine ⟨hb, ⟨z, hzj, hzx.trans hx.symm⟩, v, hL, fun τ i => ⟨y₀.u τ, fun k => ⟨u' τ k ≫ φ, ?_, ?_⟩, ?_⟩⟩
  · rw [Category.assoc, hφ, ← Category.assoc, hu2, Category.assoc]
  · rw [Category.assoc, hφ0, hu1]
  · rw [hx]
    exact hcomb τ i

end Fld

section Dom

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A}

theorem inBC_iff_isBC (f : A →+* A') (a : ArcIn Dw l β A b) (a' : ArcIn Dw l β A' (f.comp b))
    (p : Out.IsPullDeg f a.D₀ a'.D₀) : InBC f a a' p ↔ GlobalTheory.ArcPull.IsBC f a a' p := by
  constructor
  · rintro ⟨-, hs, hb, ha, he, heA⟩
    exact ⟨hs, hb, ha, he, heA⟩
  · rintro ⟨hs, hb, ha, he, heA⟩
    exact ⟨rfl, hs, hb, ha, he, heA⟩

variable {D₀ : Out.DegPre A}

theorem ThMul.refl (th : D₀.P.L.Sec) : ThMul 1 th th := fun j => by
  simp [constFn]

theorem ThMul.trans {γ δ : A} {t₁ t₂ t₃ : D₀.P.L.Sec} (h : ThMul γ t₁ t₂) (h' : ThMul δ t₂ t₃) :
    ThMul (δ * γ) t₁ t₃ := fun j => by
  rw [h' j, h j, ← mul_assoc]
  congr 1
  simp [constFn]

theorem ThNZ.ne_zero {th : D₀.P.L.Sec} (h : ThNZ th) : ∃ j, th.f j ≠ 0 := by
  obtain ⟨x, -, hx⟩ := h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A)
  unfold Out.nonzeroLocus at hx
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨j, fun h0 => ?_⟩
  rw [h0, Scheme.basicOpen_zero] at hj
  simp at hj

example (cf : Fin 0 → A) (e : Fin 0 → Out.GtPt D₀ (epsR A)) (ν : Out.GtPt D₀ (epsR A)) :
    GtComb cf e ν ↔ ν.IsZero :=
  ⟨fun ⟨_, p, _, h0, _, h⟩ => h ▸ h0, fun h => ⟨e, fun _ => ν, fun i => i.elim0, h, fun i => i.elim0, rfl⟩⟩

example (th th' : D₀.P.L.Sec) (h : ThMul 0 th th') : ¬ ThNZ th' := fun hn => by
  obtain ⟨j, hj⟩ := hn.ne_zero
  exact hj (by rw [h j]; simp [constFn])

end Dom

example (Dw : Datum H) {K : Type} [Field K] (x y : K) : cst Dw (x * y) = cst Dw x * cst Dw y := by simp [cst]

end GlobalTheory.ArcQ
