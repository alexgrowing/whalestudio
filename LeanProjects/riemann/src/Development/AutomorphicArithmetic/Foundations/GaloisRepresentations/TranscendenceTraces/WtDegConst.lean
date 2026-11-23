import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsWtZero

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def LocNml (S : Scheme.{0}) : Prop :=
  ∀ s : S, ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ IsDomain Γ(S, U) ∧ IsIntegrallyClosed Γ(S, U)

def GenPt {S : Scheme.{0}} (s : S) : Prop := ∀ t : S, t ⤳ s → t = s

def IsNwt {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) : Prop :=
  IsWt p w ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), GenPt (pt (z ≫ p)) → w Ω z = mult p Ω z

def nwt {Z S : Scheme.{0}} (p : Z ⟶ S) : Wt Z := by
  classical
  exact if h : ∃ w, IsNwt p w then h.choose else Wt.const Z 0

def WtBC : Prop := ∀ {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S) (w : Wt Z),
  IsPullback v p' p g → IsWt p w → IsWt p' (w.comap v)

def WtComp : Prop := ∀ {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S) [IsFinite r] [IsFinite p] (w' : Wt W) (w : Wt Z),
  IsWt r w' → IsWt p w → IsWt (r ≫ p) (Wt.mul r w' w)

def WtLin : Prop :=
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w w' : Wt Z), IsWt p w → IsWt p w' → IsWt p (w.add w')) ∧
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (d : ℤ) (w : Wt Z), IsWt p w → IsWt p (w.smul d)) ∧
  ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsIso p] (d : ℤ), IsWt p (Wt.const Z d)

def WtPush : Prop := ∀ {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h] [IsFinite p] (w : Wt Z),
  IsWt (h ≫ p) w → IsWt p (w.push h)

def WtPt : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  ∀ (Ω Ω' : Type) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (z : gp Ω ⟶ Z) (z' : gp Ω' ⟶ Z),
    pt z = pt z' → w Ω z = w Ω' z'

def WtUnique : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w w' : Wt Z), IsWt p w → IsWt p w' →
  ∀ D : Set S, Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), pt (z ≫ p) ∈ D → w Ω z = w' Ω z) → w = w'

def WtDegConst : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [PreconnectedSpace S] (w : Wt Z), IsWt p w →
  ∃ d : ℤ, w.push p = Wt.const S d

def MultBasic : Prop :=
  (∀ {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S), IsPullback v p' p g →
    mult p' = (mult p).comap v) ∧
  (∀ {W Z S : Scheme.{0}} (j : W ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S), mult (j ≫ p) = (mult p).comap j) ∧
  ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [Etale p], mult p = Wt.const Z 1

def MultSum : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Flat p] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (x : gp Ω ⟶ S), (mult p).push p Ω x = (p.finrank (pt x) : ℤ)

def WtFlat : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p], IsWt p (mult p)

def WtNormal : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p], LocNml S → IsNwt p (nwt p)

def NmlLoc : Prop := ∀ S : Scheme.{0}, Nml S → (IsIntegral S ∨ IsLocallyNoetherian S) → LocNml S

def NwtFlat : Prop := ∀ {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S) [IsFinite p] [Flat p']
  [LocallyOfFinitePresentation p'], IsPullback v p' p g → IsNwt p (nwt p) → Dense {s : S' | GenPt (g s)} →
  (nwt p).comap v = mult p'

def NwtOfFlat : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p],
  nwt p = mult p

def NwtDeg : Prop := ∀ {Z' Z S : Scheme.{0}} (K : Type) [Field K] (v : Z' ⟶ Z) (p' : Z' ⟶ gp K) (p : Z ⟶ S) (g : gp K ⟶ S)
  [IsFinite p] [IsIntegral S], IsPullback v p' p g → LocNml S → pt g = genericPoint S →
  (nwt p).push p = Wt.const S (p'.finrank (IsLocalRing.closedPoint K))

def TrSum : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  IsUnit (q : Γ(S, ⊤)) → ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a ((tr0 p w q i).app A a)

def TrBC : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S)
  [IsFinite p] (w : Wt Z), IsPullback v p' p g → IsWt p w → IsUnit (q : Γ(S, ⊤)) → ∀ x : Ht q (sch.obj Z) n i,
  pull _ (sch.map g) _ n (tr p w q n i x) = tr p' (w.comap v) q n i (pull _ (sch.map v) _ n x)

def TrComp : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S) [IsFinite r] [IsFinite p]
  (w' : Wt W) (w : Wt Z), IsWt r w' → IsWt p w → IsUnit (q : Γ(S, ⊤)) → ∀ x : Ht q (sch.obj W) n i,
  tr (r ≫ p) (Wt.mul r w' w) q n i x = tr p w q n i (tr r w' q n i x)

def TrLin : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ),
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w w' : Wt Z), IsWt p w → IsWt p w' → IsUnit (q : Γ(S, ⊤)) →
    ∀ x, tr p (w.add w') q n i x = tr p w q n i x + tr p w' q n i x) ∧
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (d : ℤ) (w : Wt Z), IsWt p w → IsUnit (q : Γ(S, ⊤)) →
    ∀ x, tr p (w.smul d) q n i x = d • tr p w q n i x) ∧
  ∀ (S : Scheme.{0}) (d : ℤ), IsUnit (q : Γ(S, ⊤)) → ∀ x, tr (𝟙 S) (Wt.const S d) q n i x = d • x

def TrPush : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h] [IsFinite p]
  (w : Wt Z), IsWt (h ≫ p) w → IsUnit (q : Γ(S, ⊤)) → ∀ x : Ht q (sch.obj Z') n i,
  tr (h ≫ p) w q n i (pull _ (sch.map h) _ n x) = tr p (w.push h) q n i x

def TrRed : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z),
  IsWt p w → IsUnit (Q : Γ(S, ⊤)) → ∀ x : Ht Q (sch.obj Z) n i,
  red Q q _ n i (tr p w Q n i x) = tr p w q n i (red Q q _ n i x)

def TrDeg : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z) (d : ℤ), IsWt p w →
  IsUnit (q : Γ(S, ⊤)) → w.push p = Wt.const S d → ∀ x : Ht q (sch.obj S) n i,
  tr p w q n i (pull _ (sch.map p) _ n x) = d • x

def CorrEq : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B) [IsSeparated bY]
  [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ), (∀ a, (c a).f ≫ bY = (c a).p ≫ bS) →
  IsUnit (q : Γ(S, ⊤)) → ∀ D : Set S, Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D → ∑ a, m a * (c a).cyc Ω x y = 0) →
  ∀ y : Ht q (sch.obj Y) n i, ∑ a, m a • (c a).op q n i y = 0

def TrHl : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  IsUnit (l : Γ(S, ⊤)) → ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (trHl l p w n i x).1 k = tr p w (l ^ k) n i (x.1 k)

def TrBCQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S)
  (g : S' ⟶ S) [IsFinite p] (w : Wt Z), IsPullback v p' p g → IsWt p w → IsUnit (l : Γ(S, ⊤)) →
  pullHQ l (sch.map g) n i ∘ₗ trHQ l p w n i = trHQ l p' (w.comap v) n i ∘ₗ pullHQ l (sch.map v) n i

def TrCompQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S) [IsFinite r] [IsFinite p]
  (w' : Wt W) (w : Wt Z), IsWt r w' → IsWt p w → IsUnit (l : Γ(S, ⊤)) →
  trHQ l (r ≫ p) (Wt.mul r w' w) n i = trHQ l p w n i ∘ₗ trHQ l r w' n i

def TrDegQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z) (d : ℤ), IsWt p w →
  IsUnit (l : Γ(S, ⊤)) → w.push p = Wt.const S d →
  trHQ l p w n i ∘ₗ pullHQ l (sch.map p) n i = (d : ℚ_[l]) • LinearMap.id

def CorrEqQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B) [IsSeparated bY]
  [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ), (∀ a, (c a).f ≫ bY = (c a).p ≫ bS) →
  IsUnit (l : Γ(S, ⊤)) → ∀ D : Set S, Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D → ∑ a, m a * (c a).cyc Ω x y = 0) →
  ∑ a, (m a : ℚ_[l]) • (c a).opQ l n i = 0

def CorrBCQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {S' Y' S Y : Scheme.{0}} (c' : Corr S' Y') (c : Corr S Y) (g : S' ⟶ S)
  (g' : Y' ⟶ Y) (v : c'.Z ⟶ c.Z), IsPullback v c'.p c.p g → c'.f ≫ g' = v ≫ c.f → c'.w = c.w.comap v → IsUnit (l : Γ(S, ⊤)) →
  pullHQ l (sch.map g) n i ∘ₗ c.opQ l n i = c'.opQ l n i ∘ₗ pullHQ l (sch.map g') n i

def CorrCompQ : Prop := ∀ {S Y X : Scheme.{0}} (c : Corr S Y) (d : Corr Y X), ∃ (e : Corr S X) (a : e.Z ⟶ d.Z) (b : e.Z ⟶ c.Z),
  IsPullback a b d.p c.f ∧ e.p = b ≫ c.p ∧ e.f = a ≫ d.f ∧ e.w = Wt.mul b (d.w.comap a) c.w ∧
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ X),
    e.cyc Ω x y = ∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) ∧
  ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ), IsUnit (l : Γ(S, ⊤)) → IsUnit (l : Γ(Y, ⊤)) → e.opQ l n i = c.opQ l n i ∘ₗ d.opQ l n i

def CorrGraphQ : Prop := ∀ {S Y : Scheme.{0}} (f : S ⟶ Y) (d : ℤ), ∃ c : Corr S Y, (∀ {B : Scheme.{0}} (bY : Y ⟶ B),
    c.f ≫ bY = c.p ≫ f ≫ bY) ∧
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y),
    (x ≫ f = y → c.cyc Ω x y = d) ∧ (x ≫ f ≠ y → c.cyc Ω x y = 0)) ∧
  ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ), IsUnit (l : Γ(S, ⊤)) → c.opQ l n i = (d : ℚ_[l]) • pullHQ l (sch.map f) n i

def TrSplitQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  IsUnit (l : Γ(S, ⊤)) → ∀ (U : Scheme.{0}) (x : U ⟶ S) (m : ℕ) (s : Fin m → (U ⟶ Z)) (hs : ∀ j, s j ≫ p = x),
  IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 U) (by rw [hs j, Category.id_comp])) :
    ∐ (fun _ : Fin m => U) ⟶ pullback p x) →
  pullHQ l (sch.map x) n i ∘ₗ trHQ l p (Wt.const Z 1) n i = ∑ j, pullHQ l (sch.map (s j)) n i

def Weights : Prop := WtBC ∧ WtComp ∧ WtLin ∧ WtPush ∧ WtPt ∧ WtUnique ∧ WtDegConst ∧ MultBasic ∧ MultSum ∧ WtFlat ∧ WtNormal ∧
  NmlLoc ∧ NwtFlat ∧ NwtOfFlat ∧ NwtDeg

def Torsion : Prop := TrSum ∧ TrBC ∧ TrComp ∧ TrLin ∧ TrPush ∧ TrDeg ∧ CorrEq

def Adic : Prop := TrRed ∧ TrHl ∧ TrBCQ ∧ TrCompQ ∧ TrDegQ ∧ CorrEqQ ∧ CorrBCQ ∧ CorrCompQ ∧ CorrGraphQ ∧ TrSplitQ

end UpperTheory.Gal.TranscendenceTraces

end
