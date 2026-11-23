import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def RZ.rt (H : Host E) (S A : ℕ) : RZ H S A :=
  2 * ⟨(1 + H.rt0) / 2, Subring.subset_closure (Or.inl rfl)⟩ - 1

def RZ.ze (H : Host E) (S A : ℕ) : RZ H S A := ⟨zeta A, Subring.subset_closure (Or.inr (Or.inr rfl))⟩

structure FullObj (D : Datum H) {n N : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) (t : SAB H S)
    (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  add : ∀ a c, lev (a + c) = lev a * lev c
  ker : ∀ a, lev (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : RZ H n N →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

structure FamCore (D : Datum H) {n N : ℕ} {MM : Scheme.{0}} (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM)
    (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) : Prop where
  red : IsReduced MM
  flat : Flat sM
  qproj : IsQProjOver sM
  gen : Smooth (pullback.snd sM (spMap (algebraMap (RZ H n N) (FractionRing (RZ H n N)))))
  obj : FullObj D sM tM lev
  rep : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)),
    IsReduced S → IsLocallyNoetherian S → Flat s → FullObj D s t lv →
    ∃! f : S ⟶ MM, f ≫ sM = s ∧ ∃ ν : SABMap t tM f, ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ MM) (t : SAB H (Sp (DualNumber k)))
    (lv : D.La → (𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G)) (ν : SABMap t tM x) (ν' : SABMap t tM (constPt x)),
    x ≫ sM = constPt x ≫ sM → (∀ a, (lv a).left ≫ ν.φ = x ≫ (lev a).left) →
    (∀ a, (lv a).left ≫ ν'.φ = constPt x ≫ (lev a).left) → x = constPt x

def SiegClause (D : Datum H) {n N : ℕ} {MM : Scheme.{0}} (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM)
    (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ n → ∃ (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N)
    (bas : (Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) ⊕ Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤ) ≃ₗ[ℤ] D.La),
    (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
    ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p N →+* O) (b : RZ H n N →+* O), Function.Injective i →
      IsInc (ZP p N).subtype i z → IsInc (RZ H n N).subtype i b →
      ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ MM) (tT : SAB H T) (ν : SABMap tT tM f)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT sM (spMap b) →
        (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w

def SiegRep {h p N : ℕ} (Ag : SiegelFamily h p N) : Prop :=
  IsQProjOver Ag.s ∧ ∀ (S : Scheme.{0}) (s : S ⟶ Sp (ZP p N)) (o : SiegPre h N (zetaZP p N) s),
    IsReduced S → IsLocallyNoetherian S → Flat s → o.Principal → ∃! f : S ⟶ Ag.X, f ≫ Ag.s = s ∧ SiegPB o Ag.univ f

structure ZOn {O : Type} [CommRing O] {MM : Scheme.{0}} (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ) where
  Z : Scheme.{0}
  s : Z ⟶ Sp O
  normal : IsNormalScheme Z
  proj : IsProjOver s
  flat : Flat s
  t : SAB H Z
  qproj : IsQProjOver (t.G.hom ≫ s)
  good : Good t
  W : MM.Opens
  dense : Dense (W : Set MM)
  j : W.toScheme ⟶ Z
  j_open : IsOpenImmersion j
  j_dom : IsDominant j
  j_over : j ≫ s = W.ι ≫ sM
  tW : SAB H W.toScheme
  m₁ : SABMap tW tM W.ι
  m₂ : SABMap tW t j
  amp : GlobalTheory.LN.AmpFrames t.G t.PP.L (m ^ 2)

def TopAmpExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (n : ℕ), AuxiliaryInertOddPrime H n →
      ∃ (J k : ℕ) (T : Top Xo n (n ^ J)), 1 ≤ J ∧ Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2))

end GlobalTheory.Models

end
