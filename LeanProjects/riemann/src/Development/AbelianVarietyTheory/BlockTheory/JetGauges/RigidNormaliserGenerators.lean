import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt comp1 addOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Ops

variable {S : Scheme.{0}}

def diagEnd {G' G : Over S} [GrpObj G'] [GrpObj G] {n : ℕ} (p : IsPowGrp G' G n) (f : G ⟶ G) : G' ⟶ G' :=
  p.lim.lift (Fan.mk G' fun i => p.pr i ≫ f)

variable (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsRigPull (φ : A ⟶ A) (k N : ℤ) {T : Over S} (s : LB.Sec (LPow A L.L k T)) (s' : LB.Sec (LPow A L.L N T)) :
    Prop :=
  ∃ α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![N, -k]),
    α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α (ptSecT A (1 : T ⟶ A)).left) (rigT A L.L L.rig T (N - k)) ∧
    IsTwistPull A L.L (T ◁ φ) (snd T A ≫ φ) (whiskerLeft_snd _ _) N k α s s'

def HasFinOrder {k : ℤ} {T : Over S} (ga : ThetaGrp A L.L k T) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ga.pt ^ M = 1 ∧
    LB.Gen.Corr L.L _ _ _ _ (ReciprocityTheory.ChartRestriction.G.Out.powGen A L.L k ga M) (LB.oneGen L.L)

end Ops

section Two

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R)))
  (F : Type) [Field F] [Algebra (FractionRing R) F]

def cmp : (UnifPre.GF (R := R) (G := G) F).left ⟶ (TF (R := R) F ⊗ G).left :=
  pullback.lift (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (UnifPre.gFK (R := R) (G := G) F) (by
    have h : (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ jFK (R := R) F =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.snd G.hom (jK R) :=
      pullback.condition
    show _ ≫ jFK (R := R) F ≫ jK R = (_ ≫ pullback.fst G.hom (jK R)) ≫ G.hom
    rw [← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])

theorem cmp_snd : cmp G F ≫ (snd (TF (R := R) F) G).left = UnifPre.gFK (R := R) (G := G) F :=
  pullback.lift_snd _ _ _

variable {G} {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  [GrpObj G] [IsCommMonObj G]

def SameSec (U : UnifPre I D A G) (k : ℕ) (σ : LB.Sec (LPow G U.LG.L (k : ℤ) (TF (R := R) F)))
    (σ' : U.SecGF F k) : Prop :=
  GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (R := R) (G := G) F) (fun _ => (k : ℤ)) σ'
    (fun _ : Fin 1 => (snd (TF (R := R) F) G).left) (fun _ => (k : ℤ)) σ (cmp G F) 1

end Two

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def normaliser (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ ∑ i : Fin (Dw.mult τ), a (τ, i)

example (α : 𝓞 E) : normaliser Dw c 0 α = 1 := by simp [normaliser]

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def nablaAt (C : IntegralChartA3 Xo c T io y) (F : Type) [Field F] [Algebra T.Fr F] [CharZero F] (k : ℕ) {n : ℕ}
    (f : PS F n (chD C.ch)) (P : MvPolynomial (LtN Dw n) F) : F :=
  letI := io.toAlgebra
  nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 k f (fun ℓ => ℓ.2.2)
    (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j)) P

def HasGerm (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) {n : ℕ}
    {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' C.I.G.G n)
    {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (k : ℕ)
    (σ : LB.Sec (LPow G' U'.LG.L (k : ℤ) (TF (R := T.V) F))) (f : PS F n (chD C.ch)) : Prop :=
  ∃ σ' : U'.toUnifPre.SecGF F k, SameSec F U'.toUnifPre k σ σ' ∧
    IsGermN P C.xT C.actT C.eT C.wPT pG PU F k σ' f

variable (Xo c) in

def IsThetaValue (nab : NabV Xo c) (y : IntFr Xo c T io) {n : ℕ} (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (w : T.Fr) : Prop :=
  letI := io.toAlgebra
  ThValAt Xo c nab y.1 x P w ∧ ∀ f : Rul Xo c, IsThRule Xo c nab x P f → evI y f = w

def IsLevelPt (I : letI := io.toAlgebra; IntData Xo c T io y.1) (F : Type) [Field F] [Algebra T.Fr F]
    (t : TF (R := T.V) F ⟶ I.G.G) (x : Dw.La) : Prop :=
  letI := io.toAlgebra
  ∃ p : Sp F ⟶ I.t'.G.left, p ≫ I.m2.φ = t.left ∧
    p ≫ I.m1.φ = spMap (algebraMap T.Fr F) ≫ (levPt Xo y.1.x x).left

end Val

def Oriented {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (g g' : ℕ)
    (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g * g' ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb ≤ Ideal.span {π} ∧ l.Mb ≤ Ideal.span {π'}

def Generators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → (g : T.V) ∈ maximalIdeal T.V →
  ∀ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q →
  ∀ n : ℕ, 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (σ : LB.Sec (LPow G' U'.LG.L (g' : ℤ) (TF (R := T.V) F))) (σ' : U'.toUnifPre.SecGF F g')
    (s : Fam D'.toPre F g'), SameSec F U'.toUnifPre g' σ σ' → U'.toUnifPre.ExpandsG F g' σ' s →
    NuGe D' (sumQ pD.xe Q) F v g' s 0 →
  ∀ (ga : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)),
    ga.pt ≫ diagEnd pG (C.I.G.act.act π) = 1 → HasFinOrder G' U'.LG ga →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π))) (g' : ℤ) (l.M : ℤ) σ σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) ga σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ a : (E →+* ℂ) × ℕ → ℕ,
    ∃ (u : F) (m : ℕ) (cf : Fin m → F) (x : Fin m → Fin n → Dw.La),
      v u = v (algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')))) ∧ (∀ i, 0 ≤ v (cf i)) ∧
      ∀ Pl ∈ harmA (Dw := Dw) c a n, ∃ w : Fin m → T.Fr, (∀ i, IsThetaValue Xo c nab y (x i) Pl (w i)) ∧
        nablaAt C F l.M h (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pl) =
          u * ∑ i, cf i * algebraMap T.Fr F (w i)

def GeneratorsLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → (g : T.V) ∈ maximalIdeal T.V →
  ∀ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q →
  ∀ n : ℕ, 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (σ : LB.Sec (LPow G' U'.LG.L (g' : ℤ) (TF (R := T.V) F))) (σ' : U'.toUnifPre.SecGF F g')
    (s : Fam D'.toPre F g'), SameSec F U'.toUnifPre g' σ σ' → U'.toUnifPre.ExpandsG F g' σ' s →
    NuGe D' (sumQ pD.xe Q) F v g' s 0 →
  ∀ (ga : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)),
    ga.pt ≫ diagEnd pG (C.I.G.act.act π) = 1 → HasFinOrder G' U'.LG ga →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π))) (g' : ℤ) (l.M : ℤ) σ σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) ga σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pl : MvPolynomial (LtN Dw n) F),
    Pl ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
    (∀ e, 0 ≤ v (Pl.coeff e)) →
    ∃ (u : F) (m : ℕ) (cf : Fin m → F) (f : Fin m → Rul Xo c),
      v u = v (algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')))) ∧ (∀ i, 0 ≤ v (cf i)) ∧
      (∀ i, f i ∈ thGen Xo c nab a n) ∧
      nablaAt C F l.M h Pl = u * ∑ i, cf i * algebraMap T.Fr F (evI y (f i))

def AlphaForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
    (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (n : ℕ), 1 ≤ n →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (f₀ : PS T.Fr 1 (chD C.ch)) (s : LB.Sec (LPow G' U'.LG.L ((1 : ℕ) : ℤ) (TF (R := T.V) F))),
    (letI := io.toAlgebra; IsGerm y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP 1 y.1.s f₀) →
    HasGerm C P pG PU.toUnifPowOf F 1 s
      (∏ i : Fin n, ev (n := n) ![pt F (chD C.ch) i] (MvPowerSeries.map (algebraMap T.Fr F) f₀)) →
  ∀ (b : TF (R := T.V) F ⟶ G') (U : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)) (x : Fin n → Dw.La),
    b ≫ diagEnd pG (C.I.G.act.act (π * π')) = 1 → SymLift G' U'.LG.L (l.M : ℤ) l.M b U →
    (∀ i, IsLevelPt C.I F (b ≫ pG.pr i ≫ C.I.G.act.act (H.bar π * H.bar π')) (x i)) →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π * H.bar π'))) ((1 : ℕ) : ℤ) (l.M : ℤ) s σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) U σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ Pl ∈ harmA (Dw := Dw) c a n, ∃ w : T.Fr, IsThetaValue Xo c nab y x Pl w ∧
    nablaAt C F l.M h (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pl) =
      algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')) * w)

structure IsBalancedGauge {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : Germ.FB.toK k B.ph1 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h +
    ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : Germ.FB.toK k B.ph2 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h +
    ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, Germ.FB.toK k (B.ad a) = Germ.FB.expS k
    (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

def FrameIndep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (K : Type) [Field K] [CharZero K] [Algebra c.F K] (y : FrPt Xo c K) (C : ChartAt Xo c y)
    (h' : PS K 2 C.d), IsBalancedGauge C.B K h' →
  ∀ (n N : ℕ) (f : PS K n C.d) (Pl : MvPolynomial (LtN Dw n) K),
    Pl ∈ harmK Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    nabValN C.B K C.h H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) Pl =
      nabValN C.B K h' H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) Pl

end GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators
