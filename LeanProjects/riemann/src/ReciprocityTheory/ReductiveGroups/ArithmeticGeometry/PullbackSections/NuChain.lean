import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

def iotaK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V)) :
    tK.G.left ⟶ pullback t.G.hom (Out.jK V) :=
  pullback.lift m.φ tK.G.hom m.cart.1.w

def secU {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (s : P.U.SecK k) :
    LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (Out.jK V)) (fun _ => (k : ℤ))) :=
  P.bundle ▸ s

def SecTieGK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) (s : P.U.SecK k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval (secU P s) (r ≫ iotaK m) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

def NuK {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t)
    (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)) {tK : SAB H (Sp (FractionRing V))}
    (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) : Prop :=
  ∃ (s : P.U.SecK k) (Ex : Fam P.D.toPre (FractionRing V) k),
    SecTieGK m w P k F s ∧ P.U.Expands k s Ex ∧ NuGe P.D Q (FractionRing V) vK k Ex 0

end Defs

def NuDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t),
    ∃ (ϖ : V) (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
      Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ ValOver ϖ (FractionRing V) vK

def ThetaNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))))
      (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ → NuK P Q vK m w 1 θK

def MulNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (N : ℕ), 1 ≤ N → ∀ (s : LB.Sec (LPow tK.G tK.PP.L 1 (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (mulA tK.G N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N).left] ![(N : ℤ) ^ 2, -1]))
      (s₁ : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm s) → α₀.IsGen → IsNormMul tK.G tK.PP.L tK.PP.rig N α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (mulT tK.G (𝟙_ (Over (Sp (FractionRing V)))) N) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ →
      NuK P Q vK m w (N ^ 2) (zCast tK.G (natCast_sq N) s₁)

def EndNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (π : 𝓞 E) (n k : ℕ), 0 < k → ∀ (F₁ : LB.Sec (LPow tK.G tK.PP.L ((n : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (h₁ : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w (n ^ 2) (zCast tK.G (natCast_sq n) F₁) → α₀.IsGen →
      IsNormEnd tK.G tK.PP (tK.act.act π) (k : ℤ) ((n : ℤ) ^ 2) α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π)
        (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ →
      NuK P Q vK m w k h₁

def FinNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (a : ℤ) (k : ℕ) (ha : a = k), 0 < k → ∀ (h hh : LB.Sec (LPow tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))))
      (b : (𝟙_ (Over (Sp (FractionRing V)))) ⟶ tK.G) (U : ThetaGrp tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))),
      NuK P Q vK m w k (zCast tK.G ha h) → b ^ k = 1 → SymLift tK.G tK.PP.L a k b U → IsActOf tK.G tK.PP.L a U h hh →
      NuK P Q vK m w k (zCast tK.G ha hh)

def NuRegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (k : ℕ), 0 < k → ∀ F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))), NuK P Q vK m w k F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))), SecTieK m w k F σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
