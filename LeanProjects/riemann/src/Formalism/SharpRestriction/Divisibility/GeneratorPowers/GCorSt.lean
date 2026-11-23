import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

attribute [local instance] Over.cartesianMonoidalCategory

variable {D : D7}

def GeneratorsSt : Prop :=
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
  ∀ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T'.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F wt.n (chD C.ch)),
    NuGe D' (sumQ pD.xe Q) F v g' s 0 → PullAl D' F oD' (star π) g' g s s₂ →
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
    PhiRel D'.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D'.toPre F ζ t₀ t →
    U'.toUnifPre.ExpandsG F (g' * g) σ' t →
    IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
  FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT →
  ∀ Ppol ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA wt) wt.n,
    letI := io.toAlgebra
    ∃ (k : ℕ) (f : Fin k → T.R j) (a : Fin k → F) (u : F),
      (∀ i, f i ∈ T.th j wt) ∧ (∀ i, 0 ≤ v (a i)) ∧
      v u = v (∏ τ : D.host.E →+* ℂ, algebraMap T'.Fr F (io (embK T.Q.c τ (star π * star π'))) ^
        (∑ i : Fin ((T.Q.Dw j).mult τ), wtA wt (τ, i))) ∧
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T'.Fr F) C.ch.h) T.Q.H.w0 (g' * g) h
          (fun ℓ : LtN (T.Q.Dw j) wt.n => ℓ.2.2)
          (fun (ℓ : LtN (T.Q.Dw j) wt.n) i => algebraMap T'.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (MvPolynomial.map ((algebraMap T'.Fr F).comp io) Ppol) =
        u * ∑ i, a i * algebraMap T'.Fr F (evI y (f i))

def GEndStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (j : ℕ) (hj : InR D j),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (letI := T.Q.H.starRing; ChartSaturated (T.Q.Xo j) T.Q.c) →
    (∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) →
    (∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧
      ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x) →
    WeightAlgebra.H3 L H C2 A2 CR 0 (lR Tp hK j) Tp.TO →
    (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
        (2 * Module.finrank ℚ D.host.E) ≤ WeightFamilies.RRv D CR →
    (2 * D.R.f * D.R.m : ℝ) ^ 4 * Tp.nWn + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2 →
    D.R.f * D.R.r * (D.R.r + 1) ≤ Tp.nWn →
    (∀ i, (WeightAlgebra.DF (lR Tp hK j) : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ)) →
    ∀ la, (resCharOf la = D.host.g 0 ∨ resCharOf la = D.host.g 1) → ∀ (y : (recPJ h j hj).Pt la),
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).S.sW (lR Tp hK j) la y ≤
        (((runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la +
          WeightAlgebra.cc D L C2 A2 CR (lR Tp hK j) * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
