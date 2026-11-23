import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

def TruncatedIntegralChartExists : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
      ∃ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
        Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT

def SecTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) (k : ℕ)
    (F : letI := io.toAlgebra; LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yI.1.x)))
    (σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => (k : ℤ)))) : Prop :=
  letI := io.toAlgebra
  ∃ σt : LB.Sec (LB.LinComb I.t'.PP.L (K := Fin 1) (fun _ => 𝟙 I.t'.G.left) (fun _ => (k : ℤ))),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zp : Z ⟶ Gx yI.1.x),
      zp ≫ (snd (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.m1.φ →
      zp ≫ (fst (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.t'.G.hom →
      ∀ (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
        (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good Xo.univ.t.PP.L z J → Good I.t'.PP.L z J' →
        sval (show LB.Sec (LB.LinComb Xo.univ.t.PP.L (K := Fin 1)
            (fun _ => (snd (ptO Xo yI.1.x) Xo.univ.t.G).left) (fun _ => (k : ℤ))) from F) zp z J =
          ((gv I.w1 r z (fun _ => J (r ≫ I.m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J') ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (z : Z) (J : (Z ⟶ I.G.G.left) → I.G.PP.L.ι)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.G.PP.L z J → Good I.t'.PP.L z J' →
      sval σ (r ≫ I.m2.φ) z J =
        ((gv I.w2 r z (fun _ => J (r ≫ I.m2.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J'

def FrameTieSt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] : Prop :=
  ∀ (Tc : CDVR) (io : c.F →+* Tc.Fr) (yI : IntFr Xo c Tc io) (C : IntegralChartA3 Xo c Tc io yI),
    letI := io.toAlgebra
    ∃ x' : ∀ m, jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1 ⟶ C.I.t'.G,
      (∀ m, (x' m).left ≫ C.I.m1.φ = (C.ch.x m).left) ∧
      (∀ m, (x' m).left ≫ C.I.m2.φ =
        spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m) ≫ (C.xT m).left) ∧
      ∃ eL' : ∀ m, LB.Gen (LB.LinComb C.I.t'.PP.L (K := Fin 1) (fun _ => (x' m).left) (fun _ => (1 : ℤ))),
        ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1).left) (z : Z)
          (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J' : (Z ⟶ C.I.t'.G.left) → C.I.t'.PP.L.ι)
          (J'' : (Z ⟶ C.I.G.G.left) → C.I.G.PP.L.ι),
          Good Xo.univ.t.PP.L z J → Good C.I.t'.PP.L z J' → Good C.I.G.PP.L z J'' →
          val (eL yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m) r z J =
            gv C.I.w1 (r ≫ (x' m).left) z (fun _ => J ((r ≫ (x' m).left) ≫ C.I.m1.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J' ∧
          val (eLG C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.actT C.eT C.wPT m)
              (r ≫ spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m)) z J'' =
            gv C.I.w2 (r ≫ (x' m).left) z (fun _ => J'' ((r ≫ (x' m).left) ≫ C.I.m2.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J'

def zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) : LB.Sec (LPow A L k₂ T) := h ▸ F

theorem natCast_sq (M : ℕ) : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := (Nat.cast_pow M 2).symm

def SplitModel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)

def RegTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ (I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1), SplitModel I → ∀ (x : (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x x) F →
      ∃ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left)
          (fun _ => ((T.Q.l.M ^ 2 : ℕ) : ℤ))),
        SecTie I (T.Q.l.M ^ 2) (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) F) σ

def GermTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io)
      (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI),
      Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT →
    ∀ (k : ℕ),
      letI := io.toAlgebra
      ∀ (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L (k : ℤ) (ptO (T.Q.Xo j) yI.1.x)))
        (σ : LB.Sec (LB.LinComb C.I.G.PP.L (K := Fin 1) (fun _ => 𝟙 C.I.G.G.left) (fun _ => (k : ℤ)))),
        SecTie C.I k F σ →
        ∃ g : Germ.PS Tc.Fr 1 (chD C.ch),
          IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP k F g ∧ IsIntPS Tc g

def GermChartSplitFibre : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      (∀ I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1, SplitModel I) → ∀ {n : ℕ} (x : Fin n → (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x (x b)) (F b)) →
      ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (g : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)),
        (∀ b, IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
          (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧ ∀ b, IsIntPS Tc (g b)

theorem germ_chart_split_fibre_exists (hT : TruncatedIntegralChartExists) (hR : RegTieSt) (hG : GermTieSt) : GermChartSplitFibre := by
  intro D T h j hj _ hstar Tc io yI e la ho hy hM hsplit n x F hV
  obtain ⟨C, hC⟩ := hT D T h j hj hstar Tc io yI hy
  letI := io.toAlgebra
  choose σ hσ using fun b => hR D T h j hj hstar Tc io yI e la ho hy hM C.I (hsplit C.I) (x b) (F b) (hV b)
  choose g hg hgI using fun b => hG D T h j hj hstar Tc io yI C hC (T.Q.l.M ^ 2)
    (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (σ b) (hσ b)
  exact ⟨C, g, hg, hgI⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
