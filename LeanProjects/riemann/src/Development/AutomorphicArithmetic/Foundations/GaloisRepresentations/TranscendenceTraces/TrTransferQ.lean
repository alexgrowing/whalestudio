import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.WeilBound.CoreStatements.PadicHodgeComparison.NormalSchemeSpectra.IsNormalSch
import Development.EtaleCohomology.EtaleTrace.LTransferCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC PositivityTheory.AutomorphicGaloisHodgeTate

namespace UpperTheory.Gal.TranscendenceTraces

def trN (l : ℕ) [Fact l.Prime] {Z S : Scheme.{0}} (p : Z ⟶ S) (n : ℤ) : HQ l (sch.obj Z) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj S) n 0 :=
  trHQ l p (nwt p) n 0

def Good (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) : Prop := IsFinite p ∧ IsLocallyNoetherian S ∧ Nml S ∧ IsUnit (l : Γ(S, ⊤))

def FinLfp : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [IsLocallyNoetherian S], LocallyOfFinitePresentation p

def HasDegRank : Prop := ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (d : ℕ), NormalSchemeSpectra.HasDeg f d → Flat f ∧ ∀ s, f.finrank s = d

def RankMul : Prop := ∀ {Y Z : Scheme.{0}} (Ω : Type) [Field Ω] (p : Y ⟶ Z) (q : Z ⟶ gp Ω) [IsFinite p] [Flat p] [IsFinite q]
  [Subsingleton Z] (y : Z), (p ≫ q).finrank (IsLocalRing.closedPoint Ω) = p.finrank y * q.finrank (IsLocalRing.closedPoint Ω)

def FinDisc : Prop := ∀ {V : Scheme.{0}} (Ω : Type) [Field Ω] (r : V ⟶ gp Ω) [IsFinite r], DiscreteTopology V

def MultCompOne : Prop := ∀ {Y Z : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Y ⟶ Z) (q : Z ⟶ gp Ω) [IsFinite p]
  [Flat p] [IsFinite q] [Subsingleton Y] [Subsingleton Z] (z : gp Ω ⟶ Y), z ≫ p ≫ q = 𝟙 _ →
  mult (p ≫ q) Ω z = mult p Ω z * mult q Ω (z ≫ p)

def MultCompPt : Prop := ∀ {Y Z : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Y ⟶ Z) (q : Z ⟶ gp Ω) [IsFinite p]
  [Flat p] [IsFinite q] (z : gp Ω ⟶ Y), z ≫ p ≫ q = 𝟙 _ → mult (p ≫ q) Ω z = mult p Ω z * mult q Ω (z ≫ p)

def MultComp : Prop := ∀ {Y Z S : Scheme.{0}} (p : Y ⟶ Z) (q : Z ⟶ S) [IsFinite p] [Flat p] [IsFinite q],
  mult (p ≫ q) = Wt.mul p (mult p) (mult q)

def GenField : Prop := ∀ (S : Scheme.{0}) (s : S), GenPt s → IsDomain (S.presheaf.stalk s) → IsField (S.presheaf.stalk s)

def GenUp : Prop := ∀ {Z S : Scheme.{0}} (q : Z ⟶ S) [IsFinite q] (y : Z), GenPt (q y) → GenPt y

def FlatOfField : Prop := ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), (∀ y : Y, IsField (Z.presheaf.stalk (f y))) → Flat f

def FieldUp : Prop := ∀ {Y Z : Scheme.{0}} (v : Y ⟶ Z) [SurjectiveOnStalks v] (y : Y),
  IsField (Z.presheaf.stalk (v y)) → IsField (Y.presheaf.stalk y)

def MultCompGen : Prop := ∀ {Y Z S : Scheme.{0}} (p : Y ⟶ Z) (q : Z ⟶ S) [IsFinite p] [IsFinite q],
  (∀ y : Z, IsDomain (Z.presheaf.stalk y)) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Y), GenPt (pt (z ≫ p ≫ q)) →
  mult (p ≫ q) Ω z = mult p Ω z * mult q Ω (z ≫ p)

def GenIso {T W C S : Scheme.{0}} (j : T ⟶ W) (π : W ⟶ C) (p : C ⟶ S) : Prop :=
  IsOpenImmersion j ∧ IsOpenImmersion (j ≫ π) ∧ (∀ w : W, GenPt (p (π w)) → w ∈ Set.range j) ∧
    ∀ c : C, GenPt (p c) → c ∈ Set.range (j ≫ π)

def GenMem : Prop := ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (U : Set S), IsOpen U → Dense U → ∀ s, GenPt s → s ∈ U

def ModEx : Prop := ∀ {T C C' S : Scheme.{0}} (c₁ : C ⟶ S) (c₁' : C' ⟶ S) [IsFinite c₁] [IsFinite c₁'] (a : T ⟶ C) (a' : T ⟶ C')
  [IsOpenImmersion a] [QuasiCompact a], a ≫ c₁ = a' ≫ c₁' →
  ∃ (W : Scheme.{0}) (j : T ⟶ W) (π : W ⟶ C) (π' : W ⟶ C'), IsFinite π ∧ IsFinite π' ∧ QuasiCompact j ∧
    IsSchemeTheoreticallyDominant j ∧ j ≫ π = a ∧ j ≫ π' = a' ∧ π ≫ c₁ = π' ≫ c₁'

def ZmtAff : Prop := ∀ {T W C : Scheme.{0}} [IsAffine C] (j : T ⟶ W) (π : W ⟶ C) [IsFinite π] [QuasiCompact j]
  [IsSchemeTheoreticallyDominant j] [IsOpenImmersion (j ≫ π)] [Nonempty T], IsDomain Γ(C, ⊤) → IsIntegrallyClosed Γ(C, ⊤) →
  IsIso π

def Zmt : Prop := ∀ {T W C : Scheme.{0}} (j : T ⟶ W) (π : W ⟶ C) [IsFinite π] [QuasiCompact j]
  [IsSchemeTheoreticallyDominant j] [IsOpenImmersion (j ≫ π)] [IsDominant (j ≫ π)], LocNml C → IsIso π

def ExtIso : Prop := ∀ {T C C' S : Scheme.{0}} (c₁ : C ⟶ S) (c₁' : C' ⟶ S) [IsFinite c₁] [IsFinite c₁'] [IsLocallyNoetherian S]
  (a : T ⟶ C) (a' : T ⟶ C') [IsOpenImmersion a] [IsOpenImmersion a'] [IsDominant a] [IsDominant a'], Nml C → Nml C' →
  a ≫ c₁ = a' ≫ c₁' → ∃ φ : C ≅ C', a ≫ φ.hom = a' ∧ φ.hom ≫ c₁' = c₁

def NwtGood : Prop := ∀ (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S), Good l p → IsNwt p (nwt p) ∧
  ∀ w : Wt Z, IsWt p w → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), GenPt (pt (z ≫ p)) → w Ω z = mult p Ω z) →
    nwt p = w

def NwtComp : Prop := ∀ (l : ℕ) {Y Z S : Scheme.{0}} (p : Y ⟶ Z) (q : Z ⟶ S), Good l p → Good l q →
  nwt (p ≫ q) = Wt.mul p (nwt p) (nwt q)

def NwtOnFlat : Prop := ∀ (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (U : S.Opens), Good l p → Flat (p ∣_ U) →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), pt (z ≫ p) ∈ U → nwt p Ω z = mult p Ω z

def NwtBC : Prop := ∀ (l : ℕ) {Z S Z' S' : Scheme.{0}} (p : Z ⟶ S) (g : S' ⟶ S) (p' : Z' ⟶ S') (v : Z' ⟶ Z), Good l p →
  Good l p' → IsPullback v p' p g → ∀ U : S.Opens, Flat (p ∣_ U) → Dense ((g ⁻¹ᵁ U : S'.Opens) : Set S') →
  nwt p' = (nwt p).comap v

def NwtRes : Prop := ∀ (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (U : S.Opens), Good l p → Good l (p ∣_ U) →
  nwt (p ∣_ U) = (nwt p).comap (p ⁻¹ᵁ U).ι

def PushDense : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (d : ℤ) (D : Set S), IsWt p w → Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S), pt x ∈ D → w.push p Ω x = d) → w.push p = Wt.const S d

def NwtDenseDeg : Prop := ∀ (l : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (U : S.Opens) (d : ℕ), Good l p → Dense (U : Set S) →
  NormalSchemeSpectra.HasDeg (p ∣_ U) d → (nwt p).push p = Wt.const S d

def MultGenIso : Prop := ∀ {T W C S : Scheme.{0}} (j : T ⟶ W) (π : W ⟶ C) (p : C ⟶ S), GenIso j π p →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : gp Ω ⟶ C), GenPt (pt (y ≫ p)) →
    ∃ z : gp Ω ⟶ W, fib π y = {z} ∧ mult (π ≫ p) Ω z = mult p Ω y

def NwtPush : Prop := ∀ (l : ℕ) {T W C S : Scheme.{0}} (j : T ⟶ W) (π : W ⟶ C) (p : C ⟶ S) [IsFinite π], Good l p →
  GenIso j π p → nwt p = (nwt (π ≫ p)).push π

def TrPushQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h]
  [IsFinite p] (w : Wt Z), IsWt (h ≫ p) w → IsUnit (l : Γ(S, ⊤)) →
  trHQ l (h ≫ p) w n i ∘ₗ pullHQ l (sch.map h) n i = trHQ l p (w.push h) n i

def TrCoprod : Prop := ∀ (l : ℕ) [Fact l.Prime] {Z₁ Z₂ S : Scheme.{0}} (p₁ : Z₁ ⟶ S) (p₂ : Z₂ ⟶ S), Good l p₁ → Good l p₂ →
  Good l (coprod.desc p₁ p₂) → ∀ n, trN l (coprod.desc p₁ p₂) n =
    trN l p₁ n ∘ₗ pullHQ l (sch.map coprod.inl) n 0 + trN l p₂ n ∘ₗ pullHQ l (sch.map coprod.inr) n 0

def CoprodPt : Prop := ∀ (Z₁ Z₂ : Scheme.{0}) (Ω : Type) [Field Ω] (y : gp Ω ⟶ Z₁ ⨿ Z₂),
  (∃ z, fib coprod.inl y = {z} ∧ fib coprod.inr y = ∅) ∨ ∃ z, fib coprod.inl y = ∅ ∧ fib coprod.inr y = {z}

def TrMod : Prop := ∀ (l : ℕ) [Fact l.Prime] {T W C S : Scheme.{0}} (j : T ⟶ W) (π : W ⟶ C) (p : C ⟶ S) [IsFinite π],
  Good l p → GenIso j π p → ∀ n, trN l (π ≫ p) n ∘ₗ pullHQ l (sch.map π) n 0 = trN l p n

def GenIsoOf : Prop := ∀ {Z' Z S : Scheme.{0}} (π : Z' ⟶ Z) (p : Z ⟶ S) [IsLocallyNoetherian S] (U : S.Opens),
  Dense (U : Set S) → IsIso (π ∣_ (p ⁻¹ᵁ U)) → GenIso (π ⁻¹ᵁ (p ⁻¹ᵁ U)).ι π p

def TrEmpty : Prop := ∀ (l : ℕ) [Fact l.Prime] {Z S : Scheme.{0}} (p : Z ⟶ S), Good l p → IsEmpty Z → ∀ n, trN l p n = 0

open LateralTheory.EtaleTrace.Tr (Splits LSpl LLoc LTau)

def IsTrans {R : Type} [CommRing R] {G : Shv R} {V U : Scheme.{0}} (r : V ⟶ U) (a : Sec G V) (b : Sec G U) : Prop :=
  ∀ (U' : Scheme.{0}) (g : U' ⟶ U) (m : ℕ) (s : Fin m → (U' ⟶ V)), Splits r g m s → Sec.res g b = ∑ j, Sec.res (s j) a

def SplitPt : Prop := ∀ {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] [Etale r] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (x : gp Ω ⟶ U), ∃ (m : ℕ) (s : Fin m → (gp Ω ⟶ V)), Splits r x m s ∧ Function.Injective s ∧ Set.range s = fib r x

def EtSec : Prop := ∀ {U : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : U ⟶ gp Ω) [Etale g] [Nonempty U],
  ∃ σ : gp Ω ⟶ U, σ ≫ g = 𝟙 _

def SplitsBC : Prop := ∀ {V' U' V U T : Scheme.{0}} (k : V' ⟶ V) (r' : V' ⟶ U') (r : V ⟶ U) (g : U' ⟶ U), IsPullback k r' r g →
  ∀ (x : T ⟶ U') (m : ℕ) (s : Fin m → (T ⟶ V')), Splits r' x m s → Splits r (x ≫ g) m fun j => s j ≫ k

def TransSec : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] [Etale r]
  (a : Sec G V), ∃! b, IsTrans r a b

def TransFam : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  ∃ τ : Fam p I I, ∀ n A a, IsTrans A.r a ((τ.deg n).app A a)

def TransFam0 : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  ∃ t : Fam0 p G G, ∀ A a, IsTrans A.r a (t.app A a)

def TransSums : Prop := ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p]
  (τ : Fam p (res _ (tw q i)) (res _ (tw q i))), (∀ n A a, IsTrans A.r a ((τ.deg n).app A a)) → τ.Sums (Wt.const Z 1)

def TransEx : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  ∃ t, Tr.IsTransferC R p t

def TransRp : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {Z S : Scheme.{0}} (p : Z ⟶ S)
  (t : (free R).obj (yoneda.obj S) ⟶ (free R).obj (yoneda.obj Z)), Tr.IsTransferC R p t → ∀ (n : ℤ)
  (x : H R (sch.obj Z) F n) (a : Sec ((res R F).X n) Z), Rp x a → ∃ b, Rp (Tr.pushH R t F n x) b ∧ IsTrans p a b

def TrTransfer : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  IsUnit (q : Γ(S, ⊤)) → tr p (Wt.const Z 1) q n i = Tr.pushHt q p n i

def TrTransferQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p],
  IsUnit (l : Γ(S, ⊤)) → trHQ l p (Wt.const Z 1) n i = Tr.pushHQ l p n i

end UpperTheory.Gal.TranscendenceTraces

end
