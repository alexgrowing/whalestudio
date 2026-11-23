import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotWeilIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex
section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : F :=
  valF r (LB.wchart L φ fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val

def sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : F :=
  valF r (LB.wchart L φ fun k => J (r ≫ φ k)) (s.f fun k => J (r ≫ φ k))
end Val

abbrev fnOf {F : Type} [Field F] (x : F) : Γ(Sp F, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x
section Num
variable {R : Type} [CommRing R] [IsDomain R]

structure NumOf (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) where

  J : (Sp F ⟶ D.P.A.left) → D.P.L.ι

  good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)

  th : H0 D.P.L 1

  th_gen : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j

  eA : N.A ≃* (TF (R := R) F ⟶ D.P.A)

  eX : N.X ≃+ D.X

  c_eq : ∀ χ, eA (N.c χ) = DegPre.cF D F (eX χ)

  θ_eq : ∀ x y u, (N.θ x y u : F) = vF (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (lift (eA x) (lift (eA y) (eA u))).left J

  σ_eq : ∀ x, (N.σ x : F) = vF D.sym (eA x).left J

  th_eq : ∀ x, N.th x * vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom J =
    sF th (eA x).left J

  ψ_eq : ∀ χ, (N.ψ χ : F) = vF (D.psi (eX χ)) (jFK (R := R) F) J *
    vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom J
variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def NumOf.Pt (ν : NumOf D F N) (g : GtPtF D F) (gv : N.Gt) : Prop :=
  ν.eA gv.b = g.b ∧ ∀ χ, (gv.s χ : F) = vF (g.s (ν.eX χ)) (𝟙 (Sp F)) ν.J

def NumOf.QPt (ν : NumOf D F N) {k : ℕ} (p : QkPt D F k) (q : N.QT k) : Prop :=
  ν.eX q.1.1.toAdd = p.y ∧ ν.Pt p.g q.1.2

def NumOf.Integral (ν : NumOf D F N) (S : ValuationSubring F) : Prop :=
  ∀ x : TF (R := R) F ⟶ D.P.A, ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (ν.J x.left)
end Num

def NumOf.IntN {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
    {N : NumD C} (ν : NumOf D C N) : Prop :=
  ∃ S : ValuationSubring C, (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ ν.Integral S

def CExt (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (C : Type) [NormedField C] [Algebra (FractionRing R) C] : Prop :=
  (∀ r : R, ‖algebraMap (FractionRing R) C (algebraMap R _ r)‖ ≤ 1) ∧
    ∀ r ∈ I, ‖algebraMap (FractionRing R) C (algebraMap R _ r)‖ < 1

def IsCoordPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (z : T ⟶ P.A)
    (v : I → Γ(T.left, ⊤)) : Prop :=
  Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => (k : ℤ) ^ 2)))
    (U : I → ThetaGrp P.A P.L ((k : ℤ) ^ 2) T) (s2 : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T)),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α th s1 ∧
    (∀ i, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) (U i)) ∧
    (∀ i, IsActOf P.A P.L ((k : ℤ) ^ 2) (U i) s1 (s2 i)) ∧
    ∀ i, IsValueAt P.A P.L ((k : ℤ) ^ 2) (s2 i) z τ (v i)

def TwRel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) {j : ℕ} (p : N.QT j)
    (p' : (N.twist β u).QT j) : Prop :=
  p'.1.1 = p.1.1 ∧ p'.1.2.b = p.1.2.b ∧ ∀ z : N.X, p'.1.2.s z = p.1.2.s z * r ^ β.be p.1.1.toAdd z
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Full (D : Datum H) (K : Type) [Field K] where

  P : PolAV (Sp K)

  oa : letI := H.starRing; P.OAct (𝓞 E)

  prim : letI := H.starRing; LBIso P.L (cubeLB P.A ![𝟙 P.A, oa.act H.w0] P.L)

  ρ : K

  ρ_sq : ρ ^ 2 = -(H.d : K)

  det : letI := H.starRing; DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K)) ρ

  I : letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ P.A) (fun a g => g ≫ oa.act a)
    (fun n g g' c => WeilIs P.A P.L n g g' (unitOn c))

  closed : IsAlgClosed K

def Full.Theta {D : Datum H} {K : Type} [Field K] (o : Full D K) (m : ℕ) (v : D.La → K) : Prop :=
  IsThetaPt o.P m (T := baseOver (Sp K)) (o.I.ev (m ^ 2)) fun a => fnOf (v a)

def Full.Coord {D : Datum H} {K : Type} [Field K] (o : Full D K) (m : ℕ) (z : baseOver (Sp K) ⟶ o.P.A) (v : D.La → K) : Prop :=
  IsCoordPt o.P m (T := baseOver (Sp K)) (o.I.ev (m ^ 2)) z fun a => fnOf (v a)

abbrev cf {K : Type} [CommRing K] (ζ ρ : K) : MvPolynomial (Fin 2) ℤ →+* K := MvPolynomial.eval₂Hom (Int.castRingHom K) ![ζ, ρ]

def Compat (H : Host E) (n : ℕ) {K : Type} [CommRing K] (ζ ρ : K) : Prop := ∀ c, cf (zeta n) H.rt0 c = 0 → cf ζ ρ c = 0

def VanishC (D : Datum H) (m : ℕ) (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) : Prop :=
  Odd m ∧ (∃ d, G.IsHomogeneous d) ∧ ∀ o : Full D ℂ, o.ρ = H.rt0 → (o.I.ζ (m ^ 2) : ℂ) = zeta (m ^ 2) →
    ∀ v, o.Theta m v → MvPolynomial.eval₂ (cf (zeta (m ^ 2)) H.rt0) v G = 0

structure ArcF (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] where

  D₀ : DegPre R

  [mod : Module (𝓞 E) D₀.X]

  oa : letI := H.starRing; D₀.OAct (𝓞 E)

  even : D₀.PsiEven

  bimult : D₀.TauBimult

  w0 : letI := H.starRing; TraceFormTwistIso D₀ oa H.w0

  ρ : F

  ρ_sq : ρ ^ 2 = -(H.d : F)

  det : letI := H.starRing; ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct)
    (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
    n + Module.finrank (𝓞 E) D₀.X = open Classical in if τ H.rt = ρ then D.p else D.q

  I : TateIsoQ D D₀ oa F

  N : NumD F

  ν : NumOf D₀ F N

  q : ∀ n : ℕ, D.La → N.QT n

  hq : ∀ n a, ν.QPt (I.ev n a) (q n a)

  closed : IsAlgClosed F
attribute [instance] ArcF.mod
namespace ArcF
variable {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (A : ArcF D R F)

def act (a : 𝓞 E) (y : A.N.X) : A.N.X := A.ν.eX.symm (a • A.ν.eX y)

def Bal {k : ℕ} (β : A.N.Form k) : Prop := ∀ a y z, β.be (A.act a y) z = β.be y (A.act (H.bar a) z)

def Over {R' : Type} [CommRing R'] [IsDomain R'] {F' : Type} [Field F'] [Algebra (FractionRing R') F'] (f : F →+* F')
    (A' : ArcF D R' F') : Prop :=
  ∃ I : NumD.Hom f A.N A'.N, f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧
    (∀ a y, I.e (A.act a y) = A'.act a (I.e y)) ∧
    ∀ n a, 0 < n → ∃ p' : A'.N.QT n, p'.1.1.toAdd = I.e (A.q n a).1.1.toAdd ∧ I.Rel (A.q n a).1.2 p'.1.2 ∧ A'.N.QEq p' (A'.q n a)
end ArcF

def Roots {C : Type} [Field C] (u : Cˣ) (r : ℕ → Cˣ) : Prop := r 1 = u ∧ ∀ n m, 0 < n → 0 < m → r (n * m) ^ m = r n

def Realises {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C] [Algebra (FractionRing R) C]
    (o : Full D C) (A : ArcF D R C) {k : ℕ} (β : A.N.Form k) (u : Cˣ) (r : ℕ → Cˣ) : Prop :=
  Roots u r ∧ o.ρ = A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = A.I.ζ n) ∧
    ∀ m, Odd m → ∀ p : D.La → (A.N.twist β u).QT (m ^ 2), (∀ a, TwRel β u (r (m ^ 2)) (A.q _ a) (p a)) →
      (∀ a, Summable ((A.N.twist β u).txT m (p a))) ∧ o.Theta m (fun a => (A.N.twist β u).tx m (p a)) ∧
      ∀ j, 0 < j → ∀ b (q : (A.N.twist β u).QT j), TwRel β u (r j) (A.q j b) q →
        (∀ a, Summable ((A.N.twist β u).evT m (p a) q.1.2)) ∧
        o.Coord m (o.I.ev j b) fun a => (A.N.twist β u).ev m (p a) q.1.2

abbrev CDV (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] : Prop := GlobalTheory.LN.CDvr W

abbrev SplitAt {W : Type} [CommRing W] [IsLocalRing W] (t : SAB H (Sp W)) : Prop :=
  GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal W)

theorem splitAt_iff {W : Type} [CommRing W] [IsLocalRing W] (t : SAB H (Sp W)) : SplitAt t ↔
    ∃ S : SplitExt (Sp (IsLocalRing.ResidueField W)),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t.G) := Iff.rfl

def IsPol {K : Type} [Field K] (t : SAB H (Sp K)) : Prop := IsProper t.G.hom ∧ RelAmple t.G t.PP.L ∧ KTriv t.G t.PP.L

theorem isPol_iff_polAt {K : Type} [Field K] (t : SAB H (Sp K)) : IsPol t ↔ GlobalTheory.LN.PolAt t (𝟙 _) := by
  have h := isGrpPullback_pullback t.G (𝟙 (Sp K))
  have hL := t.PP.isLB
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨inferInstance, amplePt _ K _ _ _ _ h _ _ hL (pull_isLB hL _) (lbIso_refl (pull_isLB hL _)) h₂ h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    haveI : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
    obtain ⟨e, he, hφ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl t.G)) h
    have h' := isGrpPullback_of_iso e
    refine ⟨MorphismProperty.of_isPullback (P := @IsProper) h'.1 h₁,
      amplePt _ K _ _ _ _ h' _ _ (pull_isLB hL _) hL ?_ h₂ h₃⟩
    exact (lbIso_refl (pull_isLB hL _)).chartPull (chartPullSec _ _ e.hom.left hφ)
      (Geo.Tor.chartPullPull _ _ _ rfl)

theorem NumOf.pt_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {g : GtPtF D F} {v v' : N.Gt} (h : ν.Pt g v) (h' : ν.Pt g v') : v = v' :=
  NumD.Gt.ext (ν.eA.injective (h.1.trans h'.1.symm)) (funext fun χ => Units.ext ((h.2 χ).trans (h'.2 χ).symm))

theorem ArcF.over_refl {D : Datum H} {R : Type} [CommRing R]
    [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (A : ArcF D R F) : A.Over (RingHom.id F) A :=
  ⟨⟨MonoidHom.id _, fun _ => 1, rfl, fun _ _ _ => by simp, fun _ => by simp, 1, fun _ => by simp,
      AddEquiv.refl _, fun _ => rfl, fun _ => by simp⟩, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun n a _ => ⟨A.q n a, rfl, ⟨rfl, fun _ => by simp⟩, (A.N.qEq_equivalence n).refl _⟩⟩

theorem Roots.pow {C : Type} [Field C] {u : Cˣ} {r : ℕ → Cˣ} (h : Roots u r) {j : ℕ} (hj : 0 < j) : r j ^ j = u := by
  have := h.2 1 j one_pos hj
  rwa [_root_.one_mul, h.1] at this

theorem existsUnique_twRel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) {j : ℕ} (h : r ^ j = u)
    (p : N.QT j) : ∃! p' : (N.twist β u).QT j, TwRel β u r p p' := by
  have hp : p.1.2 ^ j = N.io p.1.1.toAdd := p.2
  have h' := N.twG_pow β r p.1.2 (fun z => β.be p.1.1.toAdd z) (fun _ _ => map_add _ _ _) j
  let G : (N.twist β r).Gt := N.twG β r p.1.2 (fun z => β.be p.1.1.toAdd z) (fun _ _ => map_add _ _ _)
  let g : (N.twist β u).Gt := ⟨G.b, G.s, G.mult⟩
  have e : ∀ n : ℕ, (g ^ n).b = (G ^ n).b ∧ (g ^ n).s = (G ^ n).s := fun n => by
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      rw [pow_succ, pow_succ]
      refine ⟨congrArg (· * G.b) ih.1, funext fun z => ?_⟩
      change (g ^ n).s z * G.s z / N.θ (N.c z) (g ^ n).b G.b = (G ^ n).s z * G.s z / N.θ (N.c z) (G ^ n).b G.b
      rw [ih.1, ih.2]
  refine ⟨⟨(p.1.1, g), ?_⟩, ⟨rfl, rfl, fun _ => rfl⟩, fun q hq => Subtype.ext (Prod.ext hq.1
    (NumD.Gt.ext hq.2.1 (funext hq.2.2)))⟩
  refine NumD.Gt.ext ((e j).1.trans (h'.1.trans (by rw [hp]; rfl))) ((e j).2.trans (funext fun (z : N.X) =>
    (h'.2 z).trans ?_))
  rw [hp, mul_comm (β.be _ _), zpow_mul, zpow_natCast, h]
  exact (N.twist_τ β u _ z).symm

open ReciprocityTheory.ChartRestriction.G.Out.InhTate GlobalTheory.ToricData in

theorem isCoordPt_one_iff {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) :
    IsCoordPt P k x 1 v ↔ Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧ IsThetaPtOver P k x v := by
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨th, s1, α, τ, U, s2, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨th, s1, α, τ, U, s2, v, 1, h1, h2, h3, h4, h5, h6, h7, fun i => (_root_.one_mul _).symm⟩
  · rintro ⟨th, s1, α, τ, U, s2, w, u, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨th, s1, α, ⟨fun j => τ.s j * gv u⁻¹ _⟩, U, s2, h1, h2, fun i j => ?_, h4, h5, h6, fun i j => ?_⟩
    · rw [map_mul, map_mul, h3 i j, res_gv, res_gv, _root_.mul_assoc]
    · rw [h7 i j, h8 i, map_mul]
      have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j ≤ ⊤)).op).hom u.val *
          (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j ≤ ⊤)).op).hom
            (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have key : ∀ {A : Type} [CommRing A] (a b c d : A), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
        linear_combination (-(c * d)) * h
      exact key _ _ _ _ e

theorem compat_self (H : Host E) (n : ℕ) : Compat H n (zeta n) H.rt0 := fun _ h => h

theorem charZero_of_isPrimitiveRoot {K : Type} [Field K] {ζ : ℕ → Kˣ} (h : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) :
    CharZero K :=
  charZero_of_inj_zero fun n hn => by
    by_contra h0
    haveI : NeZero n := ⟨h0⟩
    exact (IsPrimitiveRoot.coe_units_iff.2 (h n (Nat.pos_of_ne_zero h0))).neZero'.out hn

theorem Full.charZero {D : Datum H} {K : Type} [Field K] (o : Full D K) : CharZero K :=
  charZero_of_isPrimitiveRoot o.I.ζ_prim

theorem ArcF.charZero {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : ArcF D R F) : CharZero F :=
  charZero_of_isPrimitiveRoot A.I.ζ_prim

theorem isUnit_natCast_sp {K : Type} [Field K] {m : ℕ} (hm : (m : K) ≠ 0) :
    IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) := by
  have := (IsUnit.mk0 (m : K) hm).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  rwa [map_natCast] at this

theorem Full.exists_of_obj {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {K : Type} [Field K]
    [IsAlgClosed K] (β : B →+* K) (o : Obj D l b (spMap β)) :
    ∃ f : Full D K, f.P = objPolAV o ∧ f.ρ = β b.ρ ∧ (f.I.ζ l.A : K) = β b.ζ := by
  letI := H.starRing
  obtain ⟨hdet, I, hζ, -⟩ := o.geom K (𝟙 _) β (Category.id_comp _)
  let oa : (objPolAV o).OAct (𝓞 E) :=
    { o.t.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati o.t.PP.isLB _ _ (o.t.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hu _⟩⟩ }
  exact ⟨⟨objPolAV o, oa, o.t.prim, β b.ρ, by rw [← map_pow, b.ρ_sq, map_neg, map_natCast], hdet, I, ‹_›⟩, rfl, rfl, hζ⟩

theorem Full.exists_of_point {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D l b s) {K : Type} [Field K] [IsAlgClosed K] (β : B →+* K) (x : Sp K ⟶ S)
    (hx : x ≫ s = spMap β) :
    ∃ f : Full D K, f.P.g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ f.ρ = β b.ρ ∧ (f.I.ζ l.A : K) = β b.ζ := by
  obtain ⟨o', -⟩ := obj_pull E H D l B B b b (RingHom.id B) S _ s (spMap β) x rfl rfl
    (hx.trans ((Category.comp_id _).symm.trans (congrArg (spMap β ≫ ·) (Spec.map_id _).symm))) o
  obtain ⟨f, h, h'⟩ := Full.exists_of_obj β o'
  exact ⟨f, by rw [h]; rfl, h'⟩

namespace ValInh
open ReciprocityTheory.ChartRestriction.G.Out.InhTate GlobalTheory.ToricData

theorem vF_const {F : Type} [Field F] {X Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB X) φ ε)} {a : Γ(Y, ⊤)ˣ} (ht : IsConst t a) (r : Sp F ⟶ Y)
    (J : (Sp F ⟶ X) → (Inh.trivLB X).ι) (u : Fˣ) (hu : pullTop r a = unitOn u) : vF t r J = u := by
  have h : ⊤ ≤ r ⁻¹ᵁ LB.wchart (Inh.trivLB X) φ (fun k => J (r ≫ φ k)) := by rw [wchart_triv]; exact le_rfl
  unfold vF valF
  rw [dif_pos h]
  erw [ht]
  have e : (r.appLE _ ⊤ h).hom (gv a (LB.wchart (Inh.trivLB X) φ fun k => J (r ≫ φ k))).val = (pullTop r a).val := by
    simp only [gv, res, pullTop, Units.coe_map, MonoidHom.coe_coe]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  refine (congrArg _ e).trans ?_
  rw [hu]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply _

theorem vF_one {F : Type} [Field F] {X Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (r : Sp F ⟶ Y) (J : (Sp F ⟶ X) → (Inh.trivLB X).ι) : vF (cg φ ε 1) r J = 1 :=
  vF_const (cg_isConst _ _ _) r J 1 ((map_one _).trans unitOn_one.symm)

section Toric
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing K)ˣ) (he : ∀ y, q (-y) = q y) (hb : ∀ a a' b, polar q (a + a') b = polar q a b * polar q a' b)
  (F : Type) [Field F] [Algebra (FractionRing K) F]

def toricNum : NumD F where
  toNumB := NumB.triv PUnit fun _ => 1
  X := X
  c _ := 1
  c_add _ _ := rfl
  ψ y := Units.map (algebraMap (FractionRing K) F).toMonoidHom (q y)
  even y := by
    change _ * 1 = _
    rw [he, _root_.mul_one]
  bimult a a' b := by
    change _ * 1 = _
    have := congrArg (Units.map (algebraMap (FractionRing K) F).toMonoidHom) (hb a a' b)
    simpa only [polar, map_mul, map_inv, _root_.mul_one, div_eq_mul_inv] using this

example {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) F] (x y : TF (R := R) F ⟶ D.P.A) :
    x * y = padd D.P.A x y := rfl

def toricNumOf : NumOf (toricPre K X q) F (toricNum q he hb F) where
  J _ := PUnit.unit
  good _ := le_rfl
  th := ⟨fun _ => 1, fun i j => by
    erw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]; repeat erw [map_one]⟩
  th_gen s := by
    haveI : IsIso (toricPre K X q).P.A.hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
    obtain ⟨r, hr⟩ := Inh.surj_appLE (toricPre K X q).P.A.hom
      (LB.wchart (toricPre K X q).P.L (fun _ : Fin 1 => 𝟙 _) fun _ => PUnit.unit) (wchart_triv _ _) le_top
      (s.f fun _ => PUnit.unit)
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 r
    exact ⟨r, fun j => hr.symm.trans (_root_.mul_one _).symm⟩
  eA := by
    haveI : Unique (TF (R := K) F ⟶ (toricPre K X q).P.A) := ⟨⟨toUnit _⟩, fun _ => toUnit_unique _ _⟩
    haveI : Unique (toricNum q he hb F).A := inferInstanceAs (Unique PUnit)
    exact MulEquiv.ofUnique
  eX := AddEquiv.refl X
  c_eq _ := toUnit_unique _ _
  θ_eq _ _ _ := (vF_one _ _).symm
  σ_eq _ := (vF_one _ _).symm
  th_eq x := by
    refine ((_root_.one_mul _).trans (vF_one _ _)).trans ?_
    unfold sF valF
    rw [dif_pos (by erw [wchart_triv]; exact le_rfl)]
    exact ((congrArg _ (map_one _)).trans (map_one _)).symm
  ψ_eq y := by
    refine Eq.symm ((congrArg₂ (· * ·) (vF_const (psi_isConst q y) _ _ _ (pullTop_unitOn _ _)) (vF_one _ _)).trans ?_)
    exact _root_.mul_one _

theorem pt_toric (t : Multiplicative X →* Fˣ) :
    (toricNumOf q he hb F).Pt (pt q F t) ((toricNum q he hb F).tor t) :=
  ⟨toUnit_unique _ _, fun χ => (vF_const (pt_isConst q F t χ) _ _ _ (by
    ext; simp [pullTop]; rfl)).symm⟩

theorem toric_integral (S : ValuationSubring F) (hS : ∀ r : K, algebraMap (FractionRing K) F (algebraMap K _ r) ∈ S) :
    (toricNumOf q he hb F).Integral S := by
  intro x
  refine ⟨spMap (((algebraMap (FractionRing K) F).comp (algebraMap K _)).codRestrict S.toSubring hS), ?_, le_rfl⟩
  have h : x.left = (TF (R := K) F).hom := (Category.comp_id _).symm.trans (Over.w x)
  rw [h]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]; rfl

example (y : X) : ((toricNum q he hb F).ψ y : F) = algebraMap (FractionRing K) F (q y) := rfl
end Toric

section ThetaShiftProofs
open GlobalTheory.HostModel GlobalTheory.HostModel.ConjDual
variable (H : Host E) (K : Type) [CommRing K] [IsDomain K]
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing K) F] (ρ : F) (hρ : ρ ^ 2 = -(H.d : F)) (ζ : ℕ → Fˣ)
  (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)

abbrev splitNum (F : Type) [Field F] [Algebra (FractionRing K) F] : NumD F :=
  toricNum (K := K) (X := 𝓞 E) (fun _ => 1) (fun _ => rfl) (fun _ _ _ => by simp [polar_one]) F

def splitQ {n : ℕ} (y : 𝓞 E) (t : Multiplicative (𝓞 E) →* Fˣ) (ht : t ^ n = 1) : (splitNum (E := E) K F).QT n :=
  ⟨(Multiplicative.ofAdd y, (splitNum (E := E) K F).tor t), by
    refine ((splitNum (E := E) K F).tor_pow _ n).symm.trans ?_
    refine NumD.Gt.ext rfl (funext fun χ => (DFunLike.congr_fun ht _).trans ?_)
    change 1 = Units.map _ 1 / Units.map _ 1 / Units.map _ 1
    simp⟩

def hypArc : ArcF (hypDatum H) K F where
  D₀ := toricPre K (𝓞 E) fun _ => 1
  oa := arcAct H K
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul K) H.w0 fun _ => polar_one K _ _
  ρ := ρ
  ρ_sq := hρ
  det τ := letI := H.starRing; ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul K) _ τ, by
    rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
    exact Module.finrank_self (𝓞 E)⟩
  I := tateIsoQ H K ζ hp hc
  N := splitNum (E := E) K F
  ν := toricNumOf _ _ _ F
  q n a := splitQ K a.1 (rootChar (ζ n) (toDual H a.2)) (rootChar_pow_eq_one (pow_eq_one_of_prim hp n) _)
  hq _ _ := ⟨rfl, pt_toric _ _ _ F _⟩
  closed := ‹_›

theorem hypArc_wp (n : ℕ) (a b : HypLattice H) :
    (hypArc H K ρ hρ ζ hp hc).N.wp ((hypArc H K ρ hρ ζ hp hc).q n a) ((hypArc H K ρ hρ ζ hp hc).q n b) =
      ζ n ^ hypForm H a b := by
  rw [hypForm_apply, zpow_sub]
  change ζ n ^ toDual H a.2 b.1 * (∏ _i ∈ Finset.range n, 1) / (ζ n ^ toDual H b.2 a.1 * ∏ _i ∈ Finset.range n, 1) = _
  simp [div_eq_mul_inv]

def hypBe (k : ℕ) (hk : 0 < k) : (hypArc H K ρ hρ ζ hp hc).N.Form k where
  be := (2 * k : ℤ) • trForm H
  symm (y z : 𝓞 E) := congrArg ((2 * k : ℤ) * ·) (trForm_symm H y z)
  pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 hk)) (trForm_pos H hy)
  dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩

theorem hypBe_bal (k : ℕ) (hk : 0 < k) : (hypArc H K ρ hρ ζ hp hc).Bal (hypBe H K ρ hρ ζ hp hc k hk) :=
  fun a (y z : 𝓞 E) => congrArg ((2 * k : ℤ) * ·) (trForm_adj H a y z)
end ThetaShiftProofs

theorem lbIso_of_g_one {X : Scheme.{0}} {L M : LB X} (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have e : (LB.div M L).g i j = 1 := by simp only [LB.div, hL, hM, map_one, inv_one, _root_.mul_one]; rfl
  rw [e, map_one, map_one, _root_.mul_one]

def zeroFull (H : Host E) {K : Type} [Field K] [IsAlgClosed K] (ρ : K) (hρ : ρ ^ 2 = -(H.d : K)) (ζ : ℕ → Kˣ)
    (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) :
    Full (Test.zeroDatum H) K :=
  letI := H.starRing
  have hL : ∀ τ, LieMult (ofRingAct (Inh.zeroOAct (𝓞 E) (Sp K)).toRingAct) (𝟙 (Sp K)) τ 0 := fun _ =>
    ⟨Fin.elim0, fun i => i.elim0, fun _ _ =>
      ⟨Fin.elim0, ⟨Fin.elim0, fun i => i.elim0, toUnit_unique _ _⟩, fun _ _ => Subsingleton.elim _ _⟩⟩
  { P := Inh.zeroPolAV _
    oa := Inh.zeroOAct _ _
    prim := lbIso_of_g_one (fun _ _ => rfl) (Inh.linComb_triv_g _ _)
    ρ := ρ
    ρ_sq := hρ
    det := fun τ => ⟨fun _ => hL τ, fun _ => hL τ⟩
    I :=
      { ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun _ _ => 1
        add := fun _ _ _ => toUnit_unique _ _
        lin := fun _ _ _ => toUnit_unique _ _
        ker := fun _ _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
        onto := fun _ _ _ => ⟨fun _ => ⟨0, toUnit_unique _ _⟩, fun _ => toUnit_unique _ _⟩
        tower := fun _ _ _ _ _ => toUnit_unique _ _
        isom := fun n _ a b => by
          have e : unitOn (ζ n ^ (Test.zeroDatum H).EF a b) = 1 := (congrArg unitOn (zpow_zero _)).trans unitOn_one
          rw [e]
          haveI : IsIso (baseOver (Sp K)).hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
          exact GlobalTheory.WeilPullNoncomm.weilIs_oneChart (fun u => ⟨u, by ext; simp [pullU]; rfl⟩) _ _ _ }
    closed := ‹_› }

def zetaU (n : ℕ) : ℂˣ := Units.mk0 (zeta n) (Complex.exp_ne_zero _)

theorem zetaU_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (zetaU n) n :=
  IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')

theorem zetaU_pow (n m : ℕ) (hn : 0 < n) (hm : 0 < m) : zetaU (n * m) ^ m = zetaU n := by
  ext
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [zetaU, Units.val_pow_eq_pow_val, Units.val_mk0, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem not_vanishC_X (H : Host E) (m : ℕ) : ¬ VanishC (Test.zeroDatum H) m (MvPolynomial.X 0) := by
  intro h
  have hm := h.1
  have hu := isUnit_natCast_sp (K := ℂ) (Nat.cast_ne_zero.2 hm.pos.ne')
  have := h.2.2 (zeroFull H H.rt0 H.sqrt_neg_disc_sq zetaU zetaU_prim zetaU_pow) rfl rfl (fun _ => 1) (by
    have e : (fun _ : (Test.zeroDatum H).La => fnOf (1 : ℂ)) = fun _ => 1 := funext fun _ => map_one _
    unfold Full.Theta
    rw [e]
    exact GlobalTheory.ThetaPtDet.isThetaPt_zero _ m hm hu _)
  simp at this

theorem vanishC_zero (D : Datum H) {m : ℕ} (hm : Odd m) : VanishC D m 0 :=
  ⟨hm, ⟨0, MvPolynomial.isHomogeneous_zero _ _ _⟩, fun _ _ _ _ _ => MvPolynomial.eval₂_zero _ _⟩

theorem exists_arcF : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H)
    (_ : Algebra (FractionRing ℤ) ℂ) (A : ArcF D ℤ ℂ) (β : A.N.Form 1), D.p = 1 ∧ D.q = 1 ∧ Nontrivial A.N.X ∧ A.Bal β ∧
      A.ρ = H.rt0 := by
  letI : Algebra (FractionRing ℤ) ℂ :=
    (IsFractionRing.lift (A := ℤ) (K := FractionRing ℤ) (g := Int.castRingHom ℂ) Int.cast_injective).toAlgebra
  exact ⟨_, _, _, _, GlobalTheory.HostModel.host, _, _, hypArc _ ℤ _ (Host.sqrt_neg_disc_sq _) zetaU zetaU_prim zetaU_pow,
    hypBe _ _ _ _ _ _ _ 1 one_pos, rfl, rfl, inferInstanceAs (Nontrivial (𝓞 _)), hypBe_bal _ _ _ _ _ _ _ _ _, rfl⟩

section RankZero
open GlobalTheory.HostModel
variable (H : Host E) (K : Type) [CommRing K] [IsDomain K] [Algebra (FractionRing K) ℂ]

def zeroArc : ArcF (Test.zeroDatum H) K ℂ :=
  letI := H.starRing
  have hs : ∀ (n : ℕ) (p : QkPt (splitPre K PUnit) ℂ n), p = splitPt K ℂ 0 1 (one_pow n) := fun n p => by
    obtain ⟨y, t, ht, rfl⟩ := exists_eq_splitPt K ℂ p
    obtain rfl : t = 1 := MonoidHom.ext fun _ => map_one t
    rfl
  { D₀ := toricPre K PUnit fun _ => 1
    oa := splitOAct K PUnit (𝓞 E)
    even := psiEven _ fun _ => rfl
    bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
    w0 := psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul K) H.w0 fun _ => polar_one K _ _
    ρ := H.rt0
    ρ_sq := H.sqrt_neg_disc_sq
    det := fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul K) _ τ, by
      change 0 + Module.finrank (𝓞 E) PUnit = if _ then 0 else 0
      rw [ite_self, zero_add]; exact Module.finrank_zero_of_subsingleton⟩
    I :=
      { ζ := zetaU, ζ_prim := zetaU_prim, ζ_pow := zetaU_pow
        ev := fun n _ => splitPt K ℂ 0 1 (one_pow n)
        add := fun n _ _ _ => ⟨splitPt K ℂ 0 1 (one_pow n), rfl, (isAdd_pt _ ℂ _ _ _).2 (_root_.mul_one _).symm, equiv_refl_split K ℂ _⟩
        lin := fun n _ x _ => ⟨splitPt K ℂ 0 1 (one_pow n), rfl, (gtAct_pt _ ℂ (𝓞 E) (polar_one_smul K) x 1 1).2 fun _ => rfl,
          equiv_refl_split K ℂ _⟩
        ker := fun _ _ _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => equiv_refl_split K ℂ _⟩
        onto := fun n _ p => ⟨0, hs n p ▸ equiv_refl_split K ℂ _⟩
        tower := fun n m _ _ _ => ⟨splitPt K ℂ 0 1 (one_pow n), rfl, (isNsmul_pt _ ℂ m _ _).2 (one_pow m).symm, equiv_refl_split K ℂ _⟩
        isom := fun n _ a b => by
          have e : zetaU n ^ (Test.zeroDatum H).EF a b = 1 * 1⁻¹ := (zpow_zero _).trans (by simp)
          rw [e]
          exact weilQkIs_pt _ ℂ (splitPt K ℂ 0 1 (one_pow _)) (splitPt K ℂ 0 1 (one_pow _)) 1 1 rfl rfl }
    N := toricNum (K := K) (X := PUnit) (fun _ => 1) (fun _ => rfl) (fun _ _ _ => by simp [polar_one]) ℂ
    ν := toricNumOf _ _ _ ℂ
    q := fun n _ => ⟨(1, NumD.tor _ 1), by rw [NumD.tor_one]; exact one_mem _⟩
    hq := fun _ _ => ⟨rfl, pt_toric _ _ _ ℂ _⟩
    closed := inferInstance }

theorem realises_zero {k : ℕ} (β : (zeroArc H K).N.Form k) (u : ℂˣ) (r : ℕ → ℂˣ) (hr : Roots u r) :
    Realises (zeroFull H H.rt0 H.sqrt_neg_disc_sq zetaU zetaU_prim zetaU_pow) (zeroArc H K) β u r := by
  haveI : Unique ((zeroArc H K).N.twist β u).X := inferInstanceAs (Unique PUnit)
  haveI : Finite ((zeroArc H K).N.twist β u).X := inferInstance
  have hs : ∀ (g : ((zeroArc H K).N.twist β u).Gt) χ, g.s χ = 1 := fun g χ => by
    rw [Subsingleton.elim χ 0, NumD.Gt.s_zero]
  have hψ : ∀ χ, ((zeroArc H K).N.twist β u).ψ χ = 1 := fun χ => by rw [Subsingleton.elim χ 0, NumD.ψ_zero]
  have hθ : ((zeroArc H K).N.twist β u).θ = fun _ _ _ => 1 := rfl
  have hσ : ((zeroArc H K).N.twist β u).σ = fun _ => 1 := rfl
  have ht : ((zeroArc H K).N.twist β u).th = fun _ => 1 := rfl
  have e : (fun _ : (Test.zeroDatum H).La => fnOf (1 : ℂ)) = fun _ => 1 := funext fun _ => map_one _
  refine ⟨hr, rfl, fun _ _ => rfl, fun m hm p _ => ⟨fun _ => .of_finite, ?_, fun j _ b q _ => ⟨fun _ => .of_finite, ?_⟩⟩⟩
  · have hu := isUnit_natCast_sp (K := ℂ) (Nat.cast_ne_zero.2 hm.pos.ne')
    have : ∀ a, ((zeroArc H K).N.twist β u).tx m (p a) = 1 := fun a => by
      simp [NumD.tx, NumD.txT, NumD.vt, NumD.wQ, NumB.wS, mulq, dbl, cubN, hs, hψ, hθ, hσ, ht]
    unfold Full.Theta
    simp only [this]
    rw [e]
    exact GlobalTheory.ThetaPtDet.isThetaPt_zero _ m hm hu _
  · have : ∀ a, ((zeroArc H K).N.twist β u).ev m (p a) q.1.2 = 1 := fun a => by
      simp [NumD.ev, NumD.evT, NumD.vt, NumD.wQ, NumB.wS, mulq, dbl, cubN, hs, hψ, hθ, hσ, ht]
    unfold Full.Coord
    simp only [this]
    rw [e]
    exact (isCoordPt_one_iff _ _ _ _).2 ⟨hm, isUnit_natCast_sp (Nat.cast_ne_zero.2 hm.pos.ne'),
      GlobalTheory.ThetaDeform.zero_isThetaPtOver _ _ _ _⟩
end RankZero

end ValInh
end GlobalTheory.Ex
end
