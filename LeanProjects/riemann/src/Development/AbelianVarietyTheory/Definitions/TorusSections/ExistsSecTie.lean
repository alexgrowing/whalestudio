import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

structure IntSec (Xo : Moduli Dw l) (V : Type) [CommRing V] [IsDomain V] (x : Sp (FractionRing V) ⟶ Xo.X)
    (s : LB.Sec (PPx x)) (G : SAB H (Sp V)) where
  t' : SAB H (Sp (FractionRing V))
  m1 : SABMap t' Xo.univ.t x
  m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))
  θ : LB.Sec G.PP.L
  w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)
  w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)
  σ : LB.Sec t'.PP.L
  s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)
  θ2 : LB.Sec (G.PP.L.pull m2.φ)
  rig1 : RigIso m1 w1
  rig2 : RigIso m2 w2
  maps1 : IsoMaps w1 σ s1
  maps2 : IsoMaps w2 σ θ2
  pull : PullSec m2.φ θ θ2
  gen1 : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
    ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
      s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

def IntSec.ofIntData {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    letI := io.toAlgebra; IntSec Xo T.V y.x y.s I.G :=
  letI := io.toAlgebra
  ⟨I.t', I.m1, I.m2, I.θ, I.w1, I.w2, I.σ, I.s1, I.θ2, I.rig1, I.rig2, I.maps1, I.maps2, I.pull, I.gen1⟩

theorem IntSec.ofIntData_θ {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    letI := io.toAlgebra; (IntSec.ofIntData I).θ = I.θ := rfl

private lemma eSec_comp_eq_comp_eSec_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  unfold eSec

  let T : Over S' := 𝟙_ (Over S')
  let x : T ⟶ G' := 1
  have hx : x.left = Over.Hom.left (η : 𝟙_ (Over S') ⟶ G') := by
    change (1 : T ⟶ G').left = _
    rw [Hom.one_def, CartesianMonoidalCategory.toUnit_unique (toUnit T) (𝟙 T), Category.id_comp]
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ φ) (by
    change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])

  have hsq : x₀ * x₀ = x₀ := by
    ext
    rw [h.2 T x x x₀ x₀ rfl rfl]
    change (x * x).left ≫ φ = x.left ≫ φ
    rw [show x * x = x from _root_.mul_one (1 : T ⟶ G')]
  have h1 : x₀ = 1 := mul_left_cancel (hsq.trans (_root_.mul_one x₀).symm)
  have h2 : x₀.left = f ≫ Over.Hom.left (η : 𝟙_ (Over S) ⟶ G) := by
    rw [h1, Hom.one_def, Over.comp_left]
    congr 1
  rw [← hx]
  exact h2

structure Fib (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of K))) where
  φ : A.A.left ⟶ Xo.univ.t.G.left
  cart : IsGrpPullback A.A Xo.univ.t.G x φ
  ω : LB.Iso A.L (Xo.univ.t.PP.L.pull φ)
  ωgen : ω.IsGen
  ρ : LB.Gen (A.L.pull (eSec A.A))
  ρgen : ρ.IsGen
  rig : ∀ (z : Spec (CommRingCat.of K)) (JA) (J), Good A.L z JA → Good Xo.univ.t.PP.L z J →
    gw ω (eSec A.A) z (J (x ≫ eSec Xo.univ.t.G)) (JA (eSec A.A)) *
        val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _) z JA =
      val (L := Xo.univ.t.PP.L) (φ := fun _ : PUnit => eSec Xo.univ.t.G) (ε := fun _ => 1) Xo.univ.t.PP.rig x z J

theorem exists_fib (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) :
    ∃ A : PolAV (Spec (CommRingCat.of K)), Nonempty (Fib Xo x A) := by
  obtain ⟨P, φ, act, hc, ⟨ω, hω⟩, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H Xo.X Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv K x

  have he : eSec P.A ≫ φ = x ≫ eSec Xo.univ.t.G := eSec_comp_eq_comp_eSec_of_isGrpPullback hc

  obtain ⟨ρ, hρ, hv⟩ := GlobalTheory.ConstFam.exists_gen_through (φ' := fun _ : PUnit => eSec P.A)
    (φ := fun _ : PUnit => eSec Xo.univ.t.G) (ε := fun _ => 1) (h := x) hω Xo.univ.t.PP.isLB P.isLB (fun _ => he)
    Xo.univ.t.PP.rig Xo.univ.t.PP.rigGen
  refine ⟨P, ⟨⟨φ, hc, ω, hω, ρ, hρ, ?_⟩⟩⟩
  intro z JA J hJA hJ
  have key := hv _ (𝟙 _) z J JA hJ hJA
  rw [Category.id_comp] at key
  rw [key]
  simp only [GlobalTheory.ConstFam.wVal, Fintype.prod_unique, zpow_one, Category.id_comp, he]

section

variable {Xo : Moduli Dw l} {R : Type} [CommRing R] [IsDomain R] {x : Sp (FractionRing R) ⟶ Xo.X}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {F : Type} [Field F] [Algebra (FractionRing R) F]

def Fib.SecTie (Φ : Fib Xo x A) (xF : Sp F ⟶ Xo.X) (s : LB.Sec (PPx xF)) (th : GlobalTheory.UT.SecA A F 1) : Prop :=
  xF = jFK (R := R) F ≫ x ∧
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (r' : Z ⟶ Gx xF),
    r' ≫ (snd (Over.mk xF) Xo.univ.t.G).left = r ≫ (snd (TFK (R := R) F) A.A).left ≫ Φ.φ →
    r' ≫ (fst (Over.mk xF) Xo.univ.t.G).left = r ≫ (fst (TFK (R := R) F) A.A).left →
    ∀ (z : Z) (JA) (J), Good A.L z JA → Good Xo.univ.t.PP.L z J →
      sval (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk xF) Xo.univ.t.G).left) (ε := fun _ => 1) s r' z J =
        (gw Φ.ω (r ≫ (snd (TFK (R := R) F) A.A).left) z (J (r' ≫ (snd (Over.mk xF) Xo.univ.t.G).left))
          (JA (r ≫ (snd (TFK (R := R) F) A.A).left))).val * GlobalTheory.UT.sA th r z JA

theorem Fib.SecTie.pt_eq {Φ : Fib Xo x A} {xF : Sp F ⟶ Xo.X} {s : LB.Sec (PPx xF)} {th : GlobalTheory.UT.SecA A F 1}
    (h : Φ.SecTie xF s th) : xF = jFK (R := R) F ≫ x := h.1

theorem Fib.SecTie.unique {Φ : Fib Xo x A} {xF : Sp F ⟶ Xo.X} {s s' : LB.Sec (PPx xF)}
    {th : GlobalTheory.UT.SecA A F 1} (h : Φ.SecTie xF s th) (h' : Φ.SecTie xF s' th) (i) : s.f i = s'.f i := by
  obtain ⟨hx, h2⟩ := h
  obtain ⟨-, h2'⟩ := h'
  subst hx

  let a := Φ.cart.1.lift (pullback.snd (jFK (R := R) F ≫ x) Xo.univ.t.G.hom)
    (pullback.fst (jFK (R := R) F ≫ x) Xo.univ.t.G.hom ≫ jFK (R := R) F)
    (by rw [← pullback.condition, Category.assoc])
  let r : (Over.mk (jFK (R := R) F ≫ x) ⊗ Xo.univ.t.G).left ⟶ (TFK (R := R) F ⊗ A.A).left :=
    pullback.lift (pullback.fst (jFK (R := R) F ≫ x) Xo.univ.t.G.hom) a (Φ.cart.1.lift_snd _ _ _).symm
  have e1 : 𝟙 _ ≫ (snd (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left =
      r ≫ (snd (TFK (R := R) F) A.A).left ≫ Φ.φ := by
    change 𝟙 _ ≫ pullback.snd _ _ = r ≫ pullback.snd _ _ ≫ Φ.φ
    rw [Category.id_comp, ← Category.assoc, pullback.lift_snd, IsPullback.lift_fst]
    rfl
  have e2 : 𝟙 _ ≫ (fst (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left = r ≫ (fst (TFK (R := R) F) A.A).left := by
    change 𝟙 _ ≫ pullback.fst _ _ = r ≫ pullback.fst _ _
    rw [Category.id_comp, pullback.lift_fst]
    rfl
  have hss : s = s' := by
    refine GlobalTheory.FieldBaseChange.sec_ext' Xo.univ.t.PP.isLB fun y J hJ => ?_
    obtain ⟨JA, hJA⟩ := GlobalTheory.ConstFam.exists_good' A.isLB y
    rw [h2 _ r (𝟙 _) e1 e2 y JA J hJA hJ, h2' _ r (𝟙 _) e1 e2 y JA J hJA hJ]
  rw [hss]

theorem Fib.exists_secTie (Φ : Fib Xo x A) {xF : Sp F ⟶ Xo.X} (hx : xF = jFK (R := R) F ≫ x) (s : LB.Sec (PPx xF)) :
    ∃ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie xF s th := by
  subst hx

  let hm : (TFK (R := R) F ⊗ A.A).left ⟶ (Over.mk (jFK (R := R) F ≫ x) ⊗ Xo.univ.t.G).left :=
    pullback.lift (pullback.fst (TFK (R := R) F).hom A.A.hom) (pullback.snd (TFK (R := R) F).hom A.A.hom ≫ Φ.φ)
      (by simp only [Category.assoc, Φ.cart.1.w]; exact pullback.condition_assoc x)
  have hψ : ∀ _k : Fin 1, (snd (TFK (R := R) F) A.A).left ≫ Φ.φ =
      hm ≫ (snd (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left := fun _ => (pullback.lift_snd _ _ _).symm
  obtain ⟨th, hth⟩ := GlobalTheory.ConstFam.exists_secThrough (w := Φ.ω) (ε := fun _ => 1) Φ.ωgen Xo.univ.t.PP.isLB A.isLB hψ s
  refine ⟨th, rfl, ?_⟩
  intro Z r r' h1 h2 z JA J hJA hJ
  have hr : r' = r ≫ hm := by
    refine pullback.hom_ext ?_ ?_
    · change r' ≫ (fst (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left = _
      rw [h2, Category.assoc]
      exact (congrArg (r ≫ ·) (pullback.lift_fst _ _ _)).symm
    · change r' ≫ (snd (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left = _
      rw [h1, Category.assoc]
      exact (congrArg (r ≫ ·) (pullback.lift_snd _ _ _)).symm
  subst hr
  refine (GlobalTheory.ConstFam.SecThrough.sval hψ hth r hJ hJA).trans ?_
  rw [Fin.prod_univ_one, zpow_one, h1]
  simp only [GlobalTheory.ConstFam.wVal, Category.assoc]
  rfl

end

def IntTh {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (w : GlobalTheory.UT.W0 U)
    (th : GlobalTheory.UT.SecA A F 1) : Prop :=
  w.IsGen ∧ ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ (Over.pullback (jK R)).obj G).left) (z : Z) (JA) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      sval σ (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)) z JG =
        (gw w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z
          (JG ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 _))
          (fun _ => JA ((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left))).val *
          GlobalTheory.UT.sA th (r ≫ (U.genF F).left) z JA

theorem IntTh.isGen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} {F : Type} [Field F] [Algebra (FractionRing R) F] {w : GlobalTheory.UT.W0 U}
    {th : GlobalTheory.UT.SecA A F 1} (h : IntTh U w th) : w.IsGen := h.1

example {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (w : GlobalTheory.UT.W0 U) (hw : w.IsGen) :
    IntTh U (F := F) w ⟨fun _ => 0, fun _ _ => by simp⟩ := by
  refine ⟨hw, ⟨fun _ => 0, fun _ _ => by simp⟩, fun Z r z JA JG hA hG => ?_⟩
  have g0 : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (V : X.Opens), gs f y V 0 = 0 := fun f y V => by
    unfold gs
    split_ifs
    · rw [map_zero, map_zero]
    · rfl
  exact (g0 _ _ _).trans ((congrArg (_ * ·) (g0 _ _ _)).trans (mul_zero _)).symm

end GlobalTheory.EtaVal
