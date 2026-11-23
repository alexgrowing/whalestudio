import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Mixed

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endT (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ φ)

def IsNormEnd (φ : A ⟶ A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) : Prop :=
  LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
    (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))

def IsMixedOver (φ : A ⟶ A) (n k : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    IsVtOver A L n ok s t₁ F₁ ∧ α₀.IsGen ∧ IsNormEnd A L φ (k : ℤ) ((n : ℤ) ^ 2) α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

end Mixed

abbrev kMix (D : D7) (i : Fin 2) : ℕ := D.host.g i * D.host.g (1 - i) ^ 2

def MixRootSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (n : ℕ) (x : Fin n → (T.Q.Dw j).La)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E), πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} →
    ∃ (Tc' : CDVR) (iT : Tc.Fr →+* Tc'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV Tc'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c Tc' (iT.comp io)), yI'.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        ∃ (φ : Tc.Fr →ₐ[T.Q.c.F] Tc'.Fr)
          (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x)))
          (t₁ bb : Fin n → (ptO (T.Q.Xo j) yI'.1.x ⟶ (T.Q.Xo j).univ.t.G))
          (hh : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((kMix D i : ℕ) : ℤ)
            (ptO (T.Q.Xo j) yI'.1.x))),
          φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1 ∧
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          (∀ b, KilledBy (T.Q.Xo j) (Ideal.span {T.Q.H.bar πE}) (bb b)) ∧
          (∀ b, IsMixedOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP ((T.Q.Xo j).univ.t.act.act πE)
            (D.host.g (1 - i)) (kMix D i) (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI'.1.s (t₁ b) (bb b) (hh b)) ∧
          (∀ b, levPt (T.Q.Xo j) yI'.1.x (x b) = (bb b ≫ (T.Q.Xo j).univ.t.act.act πE) ^ D.host.g (1 - i) * t₁ b) ∧
          ∀ I : IntData (T.Q.Xo j) T.Q.c Tc' (iT.comp io) yI'.1, ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc'.V)),
            S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc'.V))).obj I.G.G)

def GermIntCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E), πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI),
      Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj C.I.G.G)) →
      letI := io.toAlgebra
      ∀ (t₁ bb : ptO (T.Q.Xo j) yI.1.x ⟶ (T.Q.Xo j).univ.t.G)
        (hh : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((kMix D i : ℕ) : ℤ) (ptO (T.Q.Xo j) yI.1.x))),
      IsMixedOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP ((T.Q.Xo j).univ.t.act.act πE)
        (D.host.g (1 - i)) (kMix D i) (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s t₁ bb hh →
      ∃ g : Germ.PS Tc.Fr 1 (chD C.ch),
        IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (kMix D i) hh g ∧ IsIntPS Tc g

end ReciprocityTheory.ChartRestriction.G.PullbackSections
