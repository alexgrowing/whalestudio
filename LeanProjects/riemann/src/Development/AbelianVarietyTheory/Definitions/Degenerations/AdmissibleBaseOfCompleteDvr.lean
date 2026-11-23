import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex

def HV : Prop := GlobalTheory.UT.LL ∧ DVR.TwistBCSpanStatement ∧ DVR.TWM.VRatioGtStatement ∧ DVR.TWStatement ∧ DVR.UUStatement
section
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def NumOf.rg (ν : NumOf D F N) : F :=
  vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J

def NumOf.FamV (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (f : N.X → N.A → F) : Prop :=
  ∀ α x, f α x * ν.rg ^ k = sF (s.s (ν.eX α)) (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ν.J

def GeoIso (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB) : Prop :=
  ∃ (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left))
    (wv : N.A → F), φ.hom ≫ fst _ _ = fst _ _ ∧ w.IsGen ∧
    (∀ x, lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA (I.φ x))) ∧
    (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
      (w.s (fun _ => ν'.J (ν'.eA (I.φ x)).left, fun _ => ν.J (ν.eA x).left)).val) ∧ ∀ x, (I.h x : F) * wv 1 = wv x
end

def AllU (P : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (_ : Unif I D A G) {C : Type} [NontriviallyNormedField C]
    [Algebra (FractionRing R) C] {N : NumD C}, NumOf D.toPre C N → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), CDV R → I = IsLocalRing.maximalIdeal R → ∀ (D : DegData R I)
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G)
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    [Algebra (FractionRing R) C], CExt R I C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), P U ν

def TXSt : Prop := AllU fun {R} _ _ {_} {D} {A} {_} _ _ U C _ _ N ν => ∀ m, Odd m → ∀ (Ix : Type)
  (p : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)) (x : Ix → (TFK (R := R) C ⟶ A.A)),
  (∀ i, QkToAkU U.toUnifPre C _ (p i) (x i)) → (∀ i, ν.QPt (p i) (q i)) → IsThetaPt A m x fun i => fnOf (N.tx m (q i))

def EVSt : Prop := AllU fun {R} _ _ {_} {D} {A} {_} _ _ U C _ _ N ν => ∀ m, Odd m → ∀ (Ix : Type)
  (p : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)) (x : Ix → (TFK (R := R) C ⟶ A.A)),
  (∀ i, QkToAkU U.toUnifPre C _ (p i) (x i)) → (∀ i, ν.QPt (p i) (q i)) → ∀ j, 4 ≤ j →
  ∀ (p₀ : QkPt D.toPre C j) (q₀ : N.QT j) (z : TFK (R := R) C ⟶ A.A), QkToAkU U.toUnifPre C j p₀ z → ν.QPt p₀ q₀ →
    IsCoordPt A m x z fun i => fnOf (N.ev m (q i) q₀.1.2)

def AllN (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F}, NumOf D F N → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), P ν

def BrGtSt : Prop := AllN fun {_} _ _ {D} {F} _ _ {N} ν => (∀ g, ∃! c, ν.Pt g c) ∧ (∀ c, ∃! g, ν.Pt g c) ∧
  (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) ∧
  (∀ y g c, ν.Pt g c → (GtPtF.IsIota (ν.eX y) g ↔ c = N.io y)) ∧
  ∀ k, (∀ p : QkPt D F k, ∃! q, ν.QPt p q) ∧ (∀ q : N.QT k, ∃ p, ν.QPt p q) ∧
    ∀ (p p' : QkPt D F k) q q', ν.QPt p q → ν.QPt p' q' → (QkPt.Equiv D F p p' ↔ N.QEq q q')

def BrFamSt : Prop := AllN fun {_} _ _ {D} {F} _ _ {N} ν => ∀ k, 1 ≤ k → (∀ s : Fam D F k, ∃! f, ν.FamV s f) ∧
  (∀ (s s' : Fam D F k) f, ν.FamV s f → ν.FamV s' f → s = s') ∧ (∀ (s : Fam D F k) f, ν.FamV s f → N.FE k f) ∧
  (∃ (s : Fam D F k) (f : _), ν.FamV s f ∧ f ≠ 0) ∧ (∀ (s : Fam D F 1) f, ν.FamV s f → ∃ c : F, f = c • N.vth) ∧
  ∀ (p : QkPt D F k) q w (wv : Fˣ) s s' f f', ν.QPt p q → w.IsGen → (wv : F) = vF w (𝟙 (Sp F)) ν.J → ν.FamV s f → ν.FamV s' f' →
    (PhiRel D F k p w s s' ↔ f' = N.phi q wv f)

def BrWpSt : Prop := AllN fun {_} _ _ {D} {F} _ _ {N} ν => ∀ k, 1 ≤ k → ∀ (p p' : QkPt D F k) q q' (z : F),
  ν.QPt p q → ν.QPt p' q' → (WeilQkIs D F k p p' z ↔ z = N.wp q q')

def BrUthSt : Prop := AllN fun {R} _ _ {D} {F} _ _ {N} ν =>
  (∀ k : ℕ, 1 ≤ k → ∀ b b' : N.A, b ^ k = 1 → b' ^ k = 1 → WeilIs D.P.A D.P.L k (ν.eA b) (ν.eA b') (unitOn (N.weil k b b'))) ∧
  ∀ m : ℕ, Odd m → (m : F) ≠ 0 → ∀ (Ix : Type) (b : Ix → N.A), (∀ i, b i ^ m ^ 2 = 1) →
    IsThetaPt D.P m (T := TF (R := R) F) (fun i => ν.eA (b i)) (fun i => fnOf (N.uth m (b i) 1)) ∧
    ∀ x, IsCoordPt D.P m (T := TF (R := R) F) (fun i => ν.eA (b i)) (ν.eA x) fun i => fnOf (N.uth m (b i) x)

def AllG (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {C : Type} [NontriviallyNormedField C]
    [Algebra (FractionRing R) C] {N N' : NumD C} {n : ℕ}, NumOf D C N → NumOf D' C N' → Match N N' n → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [Algebra (FractionRing R) C] (N N' : NumD C) (ν : NumOf D C N) (ν' : NumOf D' C N') (q : QuadraticMap ℤ N.X ℝ)
    (q' : QuadraticMap ℤ N'.X ℝ) (n : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Int q → N'.Int q' → N.Tors n D.P.g →
    N'.Tors n D'.P.g → ∀ mt : Match N N' n, P ν ν' mt

def UrCSt : Prop := AllG fun {_} _ _ {D} {D'} {_} _ _ {_} {_} {_} ν ν' mt => mt.A → D.P.g = D'.P.g → ∀ e, mt.B e → mt.Term e →
  ∃ I, mt.OnB I ∧ (I.lam : _) = mt.c₀ ∧ GeoIso ν ν' I

def URecSt : Prop := AllG fun ν ν' mt => ∃ J : NumD.Iso _ _, mt.OnQ J ∧ GeoIso ν ν' J.toIso
end GlobalTheory.Ex
end
noncomputable section
namespace GlobalTheory.Ex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

structure Lift (a : ArcIn D l β O' b) (F : Type) [Field F] [Algebra (FractionRing O') F] where

  ρ : F
  ρ_sq : ρ ^ 2 = -(H.d : F)
  det : letI := H.starRing; ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct a.oa.onB.toRingAct)
    (spMap ((algebraMap (FractionRing O') F).comp (algebraMap O' _))) τ n ∧
    n + Module.finrank (𝓞 E) a.D₀.X = open Classical in if τ H.rt = ρ then D.p else D.q

  I : TateIsoQ D a.D₀ a.oa F

  N : NumD F

  ν : NumOf a.D₀ F N

  q : ∀ n : ℕ, D.La → N.QT n
  hq : ∀ n v, ν.QPt (I.ev n v) (q n v)

  be : N.Form l.M'
  be_eq : ∀ y z, be.be y z = a.be (ν.eX y) (ν.eX z)
  ρ_eq : ∀ r : O, ((β r : c.F) : ℂ) = H.rt0 → ρ = algebraMap (FractionRing O') F (algebraMap O' _ (b r))
  ζ_eq : ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (I.ζ l.A : F) = algebraMap (FractionRing O') F (algebraMap O' _ (b z))
  levA : ∀ v p, QkExt (algebraMap _ F) (a.etaA v) p → QkPt.Equiv a.D₀ F p (I.ev l.A v)
  levM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ p,
    QkExt (algebraMap _ F) (a.eta v) p → QkPt.Equiv a.D₀ F p (I.ev l.M v)

  closed : IsAlgClosed F

def Lift.arc {a : ArcIn D l β O' b} {F : Type} [Field F] [Algebra (FractionRing O') F] (A : Lift a F) : ArcF D O' F :=
  { D₀ := a.D₀, oa := a.oa, even := a.even, bimult := a.bimult, w0 := a.w0, ρ := A.ρ, ρ_sq := A.ρ_sq, det := A.det,
    I := A.I, N := A.N, ν := A.ν, q := A.q, hq := A.hq, closed := A.closed }

def FullAt (Y : Model Xo c β) {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) : Prop :=
  letI := H.starRing
  ∃ φ : o.P.A.left ⟶ Y.oF.t.G.left, IsGrpPullback o.P.A Y.oF.t.G y φ ∧ LBIso o.P.L (Y.oF.t.PP.L.pull φ) ∧
    (∀ x, (o.oa.act x).left ≫ φ = φ ≫ (Y.oF.t.act.act x).left) ∧
    (∀ v, (o.I.ev l.A v).left ≫ φ = y ≫ (Y.oF.etaA v).left) ∧
    (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (o.I.ev l.M v).left ≫ φ = y ≫ (Y.oF.eta v).left) ∧
    ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f → o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ

def FullExt {K K' : Type} [Field K] [Field K'] (f : K →+* K') (o : Full D K) (o' : Full D K') : Prop :=
  letI := H.starRing
  o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
  ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
    (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
    ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left

def AllC {R₁ : Type} [CommRing R₁] (g : PowerSeries O' →+* R₁) {K : Type} [Field K] (i : R₁ →+* K)
    (P : ∀ {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C], (K →+* C) → Cˣ → Prop) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [Algebra (FractionRing O') C] (gam : K →+* C) (u : Cˣ),
    (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (i (g (PowerSeries.C x)))) →
    (∀ r, ‖gam (i r)‖ ≤ 1) → (u : C) = gam (i (g PowerSeries.X)) → ‖(u : C)‖ < 1 → P gam u

def ArcPt (Y : Model Xo c β) (b : O →+* O') {R₁ : Type} [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁)
    (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  Function.Injective g ∧ g.Finite ∧ y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b

def RealAt (Y : Model Xo c β) (a : ArcIn D l β O' b) {R₁ : Type} [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁)
    (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  ArcPt Y b g y₁ ∧ AllC g (algebraMap R₁ (FractionRing R₁)) fun {C} _ _ gam u => ∃ (A : Lift a C) (r : ℕ → Cˣ) (o : Full D C),
    A.ν.IntN ∧ Roots u r ∧ FullAt Y (spMap gam ≫ y₁) o ∧ Realises o A.arc A.be u r

def IntFam {R₁ : Type} [CommRing R₁] (u : R₁) {K : Type} [Field K] (i : R₁ →+* K) (s : ℕ) (v : D.La → K) : Prop :=
  ∀ S : ValuationSubring K, (∀ r, i r ∈ S) → (∀ x, v x ∈ S) ∧ (∃ x, S.valuation (v x) = 1) ∧
    (S.valuation (i u) = 1 → ∀ x, ∃ h, S.valuation (v (x + s • h)) = 1)

def ThetaInt (Y : Model Xo c β) {R₁ : Type} [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁)
    (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  ∃ o : Full D (AlgebraicClosure (FractionRing R₁)), FullAt Y (spMap (algebraMap _ _) ≫ y₁) o ∧
    ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : O') → 1 ≤ j → ∃ v, o.Theta (n ^ j) v ∧
      IntFam (D := D) (g PowerSeries.X) ((algebraMap (FractionRing R₁) _).comp (algebraMap R₁ _)) (n ^ (j - 1)) v

structure SerBase {K : Type} [Field K] [Algebra (FractionRing O') K] (i : PowerSeries O' →+* K) : Prop where
  closed : IsAlgClosed K
  inj : Function.Injective i
  alg : ∀ x : K, ∃ p : Polynomial (PowerSeries O'), p ≠ 0 ∧ p.eval₂ i x = 0
  const : ∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = i (PowerSeries.C x)

structure Ser (a : ArcIn D l β O' b) (K : Type) [Field K] [Algebra (FractionRing O') K] (i : PowerSeries O' →+* K) where
  base : SerBase i

  A : Lift a K

  r : ℕ → Kˣ
  r_one : (r 1 : K) = i PowerSeries.X
  roots : Roots (r 1) r

  v : ℕ → D.La → K

  w : ℕ → ℕ → D.La → D.La → K
  int : ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : O') → 1 ≤ j → IntFam (D := D) PowerSeries.X i (n ^ (j - 1)) (v (n ^ j))
  val : AllC (RingHom.id _) i fun {C} _ _ gam u => ∃ (A' : Lift a C) (r' : ℕ → Cˣ), A'.ν.IntN ∧ A.arc.Over gam A'.arc ∧
    (∀ n, (r' n : C) = gam (r n)) ∧ ∀ m, Odd m → ∀ p : D.La → (A'.N.twist A'.be u).QT (m ^ 2),
      (∀ x, TwRel A'.be u (r' (m ^ 2)) (A'.q _ x) (p x)) →
      (∃ s : Cˣ, ∀ x, gam (v m x) = s * (A'.N.twist A'.be u).tx m (p x)) ∧
      ∀ j, 0 < j → ∀ z (q : (A'.N.twist A'.be u).QT j), TwRel A'.be u (r' j) (A'.q j z) q →
        ∃ s : Cˣ, ∀ x, gam (w m j z x) = s * (A'.N.twist A'.be u).ev m (p x) q.1.2

def Ser.Has {a : ArcIn D l β O' b} {K : Type} [Field K] [Algebra (FractionRing O') K] {i : PowerSeries O' →+* K}
    (S : Ser a K i) (o : Full D K) : Prop :=
  o.ρ = S.A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = S.A.I.ζ n) ∧
    ∀ m, Odd m → o.Theta m (S.v m) ∧ ∀ j, 0 < j → ∀ z, o.Coord m (o.I.ev j z) (S.w m j z)

structure Mdl {C : Type} [NormedField C] (o : Full D C) where

  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [loc : IsLocalRing W]
  cdv : CDV W
  [alg : Algebra (FractionRing W) C]
  ext : CExt W (IsLocalRing.maximalIdeal W) C

  t : SAB H (Sp W)

  P : PELUnif (IsLocalRing.maximalIdeal W) t

  φ : o.P.A.left ⟶ P.A.A.left
  cart : IsGrpPullback o.P.A P.A.A (jFK (R := W) C) φ
  lb : LBIso o.P.L (P.A.L.pull φ)
  act : letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left
attribute [instance] Mdl.ring Mdl.dom Mdl.loc Mdl.alg

def AllD (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}, Datum H → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), P D

def AllA (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {W₀ : ValuationSubring ℂ} (_ : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O']
    [IsDomain O'] {b : c.V W₀ →+* O'}, ArcIn D l (c.V W₀).subtype O' b → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b : c.V W₀ →+* O') (ϖ : O') (a : ArcIn D l (c.V W₀).subtype O' b), GlobalTheory.LN.ArcBase O' ϖ → P Y a

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem ArcPt.comp {Y : Model Xo c β} {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂]
    {g : PowerSeries O' →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c} (hy : ArcPt Y b g y₁) (h : R₁ →+* R₂)
    (h' : FractionRing R₁ →+* FractionRing R₂) (hf : h.Finite) (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) :
    ArcPt Y b (h.comp g) (spMap h' ≫ y₁) := by
  refine ⟨Function.Injective.comp (g := h) (fun r s e => IsFractionRing.injective R₁ (FractionRing R₁)
    (h'.injective (by rw [hh, hh, e]))) hy.1, hf.comp hy.2.1, ?_⟩
  have e : spMap h' ≫ jK R₁ = jK R₂ ≫ spMap h :=
    (spMap_comp' (algebraMap R₁ _) h').symm.trans ((congrArg spMap (RingHom.ext hh)).trans (spMap_comp' h (algebraMap R₂ _)))
  rw [Category.assoc, hy.2.2, spMap_comp', ← Category.assoc, e]
  simp only [Category.assoc]

theorem RealAt.comp {Y : Model Xo c β} {a : ArcIn D l β O' b} {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁] [CommRing R₂]
    [IsDomain R₂] {g : PowerSeries O' →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c} (hR : RealAt Y a g y₁) (h : R₁ →+* R₂)
    (h' : FractionRing R₁ →+* FractionRing R₂) (hf : h.Finite) (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) :
    RealAt Y a (h.comp g) (spMap h' ≫ y₁) := by
  refine ⟨hR.1.comp h h' hf hh, fun C _ _ _ _ _ gam u h₁ h₂ h₃ h₄ => ?_⟩
  obtain ⟨A, r, o, p₁, p₂, p₃, p₄⟩ := hR.2 C (gam.comp h') u
    (fun x => by rw [h₁, RingHom.comp_apply, RingHom.comp_apply, hh])
    (fun r => by rw [RingHom.comp_apply, hh]; exact h₂ _)
    (by rw [h₃, RingHom.comp_apply, RingHom.comp_apply, hh]) h₄
  refine ⟨A, r, o, p₁, p₂, ?_, p₄⟩
  rwa [spMap_comp', Category.assoc] at p₃

theorem serBase_algebraMap (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K]
    (h : ∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) :
    SerBase (algebraMap (PowerSeries O') K) :=
  ⟨‹_›, FaithfulSMul.algebraMap_injective _ _, fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x, h⟩

theorem Mdl.admissible_base_of_complete_dvr {C : Type} [NormedField C] {o : Full D C} (M : Mdl o) :
    AdmBase M.W (IsLocalRing.maximalIdeal M.W) ∧ CharZero M.W := by
  obtain ⟨h₁, h₂, h₃⟩ := M.cdv
  exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, h₃⟩
end GlobalTheory.Ex
end
