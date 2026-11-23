import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

attribute [local instance] Over.cartesianMonoidalCategory

namespace GCorCut

def famCast {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    (e : k = k') (s : Fam Dp F k) : Fam Dp F k' :=
  e ▸ s

def ThFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Dd : DegData V (maximalIdeal V)) (ϖ : V)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam Dd.toPre F 1) : Prop :=
  ∃ (σ : Dd.toPre.SecB 1 0)
    (σF : LB.Sec (LB.LinComb Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1))),
    GeneratorPullback.SecScal Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1) σF
      (Dd.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB Dd.toPre F).left 1 ∧
    (∀ j, (θ.s 0).f j = σF.f j) ∧
    ¬ ∃ σ' : Dd.toPre.SecB 1 0, ∀ j, σ.f j = constFn Dd.toPre.P.A.hom _ ϖ * σ'.f j

end GCorCut

open GCorCut

variable {D : D7}

def PowPELSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∃ (oA' : A'.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧
    IsQ D'.toPre ϖ (sumQ pD.xe Q) ∧
    (∃ Dw' : Datum T.Q.H, Nonempty (TateIso Dw' F (TFK (R := T'.V) F ⟶ A'.A) (fun a x => x ≫ oA'.act a)
        (fun k x x' z => WeilIs A'.A A'.L k x x' (unitOn z)))) ∧
    ∃ (semi : IsSemiAbelian G') (act : OAct (𝓞 D.host.E) G') (PP : RigLB G') (cub : CubicalStr G' PP)
      (sym : PP.IsSymmetric)
      (adj : ∀ a, LBIso (cubeLB G' ![fst G' G' ≫ act.act a, snd G' G'] PP.L)
        (cubeLB G' ![fst G' G', snd G' G' ≫ act.act (T.Q.H.bar a)] PP.L))
      (prim : LBIso PP.L (cubeLB G' ![𝟙 G', act.act T.Q.H.w0] PP.L)),
      let t' : SAB T.Q.H (Sp T'.V) := ⟨G', semi, act, PP, cub, sym, adj, prim⟩
      ∃ (bundle : U'.LG = t'.PP) (lin : U'.toUnifPre.OLinear (𝓞 D.host.E) oD' oA' t'.act.toRingAct)
        (w0 : TraceFormTwistIso D'.toPre oD' T.Q.H.w0),
        (⟨D', oD', A', oA', U', bundle, lin, w0⟩ : PELUnif (maximalIdeal T'.V) t').TorsionIso

def ThetaFrameAtSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * g')),
    NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' (star π') 1 g' θ θα

def GPairSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T'.V) F ⟶ A'.A),
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
  FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT →
  ∀ Ppol ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA wt) wt.n,
    letI := io.toAlgebra
    ∃ ℓ : Fam D'.toPre F g' →ₗ[F] F,
      (∀ (s : Fam D'.toPre F g') (s₂ t₀ t : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g))
          (h : PS F wt.n (chD C.ch)),
        PullAl D' F oD' (star π) g' g s s₂ → PhiRel D'.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D'.toPre F ζ t₀ t →
        U'.toUnifPre.ExpandsG F (g' * g) σ' t →
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
        nabValN C.ch.B F (MvPowerSeries.map (algebraMap T'.Fr F) C.ch.h) T.Q.H.w0 (g' * g) h
          (fun ℓ : LtN (T.Q.Dw j) wt.n => ℓ.2.2)
          (fun (ℓ : LtN (T.Q.Dw j) wt.n) i => algebraMap T'.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (MvPolynomial.map ((algebraMap T'.Fr F).comp io) Ppol) = ℓ s) ∧
      ∀ s : Fam D'.toPre F g', ∃ (s₂ t₀ t : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g))
          (h : PS F wt.n (chD C.ch)),
        PullAl D' F oD' (star π) g' g s s₂ ∧ PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
        U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

def DescentIdSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (oA' : A'.OAct (𝓞 D.host.E)), (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * g')), PullAl D' F oD' (star π') 1 g' θ θα →
  ∀ (pb : QkPt D'.toPre F (1 * g'))
    (wb : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
    (ζb : F) (xb : TFK (R := T'.V) F ⟶ A'.A) (tb₀ tb : Fam D'.toPre F (1 * g')),
    QkToAkU U'.toUnifPre F (1 * g') pb xb → xb ≫ oA'.act (star (star π')) = 1 →
    wb.IsGen → ζb ≠ 0 → FinOrd D' F (1 * g') pb wb ζb →
    PhiRel D'.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul D'.toPre F ζb tb₀ tb →
  ∀ (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T'.V) F ⟶ A'.A),
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
  ∀ (s₂ t₀ r : Fam D'.toPre F (g' * g)),
    PullAl D' F oD' (star π) g' g (famCast (Dp := D'.toPre) (F := F) (one_mul g') tb) s₂ → PhiRel D'.toPre F (g' * g) p w s₂ t₀ →
    Fam.IsSmul D'.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam D'.toPre F (1 * (g' * g))) (p₂ : QkPt D'.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := T'.V) F ⟶ A'.A) (r₀ r₂ : Fam D'.toPre F (1 * (g' * g))),
      PullAl D' F oD' (star π * star π') 1 (g' * g) θ θα₂ ∧
      QkToAkU U'.toUnifPre F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ oA'.act (star (star π * star π')) = 1 ∧
      w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd D' F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel D'.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul D'.toPre F ζ₂ r₀ r₂ ∧
      r = famCast (Dp := D'.toPre) (F := F) (one_mul (g' * g)) r₂

def AlphaFormSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (oA' : A'.OAct (𝓞 D.host.E)), (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) →
  ∀ θ : Fam D'.toPre F 1, NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
  ∀ (θα₂ : Fam D'.toPre F (1 * (g' * g))), PullAl D' F oD' (star π * star π') 1 (g' * g) θ θα₂ →
  ∀ (p₂ : QkPt D'.toPre F (1 * (g' * g)))
    (w₂ : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
    (ζ₂ : F) (x₂ : TFK (R := T'.V) F ⟶ A'.A) (r₀ r₂ : Fam D'.toPre F (1 * (g' * g))),
    QkToAkU U'.toUnifPre F (1 * (g' * g)) p₂ x₂ → x₂ ≫ oA'.act (star (star π * star π')) = 1 →
    w₂.IsGen → ζ₂ ≠ 0 → FinOrd D' F (1 * (g' * g)) p₂ w₂ ζ₂ →
    PhiRel D'.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ → Fam.IsSmul D'.toPre F ζ₂ r₀ r₂ →
  ∀ (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F wt.n (chD C.ch)),
    U'.toUnifPre.ExpandsG F (g' * g) σ' (famCast (Dp := D'.toPre) (F := F) (one_mul (g' * g)) r₂) →
    IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
  ∀ Ppol ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA wt) wt.n,
    letI := io.toAlgebra
    ∃ (f : T.R j) (e : F), f ∈ T.th j wt ∧ 0 ≤ v e ∧
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T'.Fr F) C.ch.h) T.Q.H.w0 (g' * g) h
          (fun ℓ : LtN (T.Q.Dw j) wt.n => ℓ.2.2)
          (fun (ℓ : LtN (T.Q.Dw j) wt.n) i => algebraMap T'.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (MvPolynomial.map ((algebraMap T'.Fr F).comp io) Ppol) =
        e * (∏ τ : D.host.E →+* ℂ, algebraMap T'.Fr F (io (embK T.Q.c τ (star π * star π'))) ^
        (∑ i : Fin ((T.Q.Dw j).mult τ), wtA wt (τ, i))) * algebraMap T'.Fr F (evI y f)

end Formalism.MainNotions.ModuliIntegralCharts.H1
