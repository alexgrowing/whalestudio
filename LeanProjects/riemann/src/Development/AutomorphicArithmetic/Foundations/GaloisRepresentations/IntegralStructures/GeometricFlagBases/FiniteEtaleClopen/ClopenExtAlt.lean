import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Gal.Int.Geo.Cut

structure Part {Y' Y : Scheme.{0}} (j : Y' ⟶ Y) : Prop where
  op : IsOpenImmersion j
  cl : IsClosed (Set.range j)

structure Res {Y' Y T' T : Scheme.{0}} (j : Y' ⟶ Y) (s t : T ⟶ Y) (i : T' ⟶ T) (s' t' : T' ⟶ Y') : Prop where
  op : IsOpenImmersion i
  rng : Set.range i = s ⁻¹' Set.range j ∩ t ⁻¹' Set.range j
  es : s' ≫ j = i ≫ s
  et : t' ≫ j = i ≫ t

def StalkDom : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Y : Scheme.{0}) (p : Y ⟶ Spec (CommRingCat.of O)), Smooth p →
    ∀ y : Y, IsDomain (Y.presheaf.stalk y)

def GenDense : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Y : Scheme.{0}) (p : Y ⟶ Spec (CommRingCat.of O)), Flat p →
    Dense {y : Y | (p y).asIdeal = ⊥}

def GenRange : Prop :=
  ∀ (O k : Type) [CommRing O] [IsDomain O] [Field k] [Algebra O k] [IsFractionRing O k] (Y : Scheme.{0})
    (p : Y ⟶ Spec (CommRingCat.of O)), Set.range (pullback.fst p (gen O k)) = {y : Y | (p y).asIdeal = ⊥} ∧
      Topology.IsEmbedding (pullback.fst p (gen O k))

def ClopenExt : Prop :=
  ∀ (O k : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field k] [Algebra O k] [IsFractionRing O k] (Y : Scheme.{0})
    (p : Y ⟶ Spec (CommRingCat.of O)), Smooth p → ∀ U : Set ↥(pullback p (gen O k)), IsClopen U →
    ∃ V : Y.Opens, IsClosed (V : Set Y) ∧ pullback.fst p (gen O k) ⁻¹' V = U

def CoverCut : Prop :=
  ∀ (k L O : Type) [Field k] [Field L] [CommRing O] [Algebra O k] (H : HTower k) (θ : H.Γ → L) (C : Cover H θ O) (V : C.Y.Opens),
    IsClosed (V : Set C.Y) → pullback.fst C.p (gen O k) ⁻¹' V = Set.range (pullback.lift C.π H.q C.ov) →
    ∃ (C' : Cover H θ O) (j : C'.Y ⟶ C.Y), Part j ∧ Set.range j = V ∧ C'.p = j ≫ C.p ∧ C'.π ≫ j = C.π ∧ C'.Onto

def ResEx : Prop :=
  ∀ (Y' Y T : Scheme.{0}) (j : Y' ⟶ Y) (s t : T ⟶ Y), Part j → ∃ (T' : Scheme.{0}) (i : T' ⟶ T) (s' t' : T' ⟶ Y'), Res j s t i s' t'

def LiesCut : Prop :=
  ∀ (k L O : Type) [Field k] [Field L] [CommRing O] [Algebra O k] (H : HTower k) (θ : H.Γ → L) (C C' : Cover H θ O) (j : C'.Y ⟶ C.Y),
    Part j → C'.π ≫ j = C.π → ∀ (g : H.Γ) (T : Scheme.{0}) (s t : T ⟶ C.Y) (m : ℕ), C.Lies g s t m →
    (∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π) ∧
      ∀ (T' : Scheme.{0}) (i : T' ⟶ T) (s' t' : T' ⟶ C'.Y), Res j s t i s' t' → C'.Lies g s' t' m

def FEtCut : Prop :=
  ∀ (Y' Y T' T : Scheme.{0}) (j : Y' ⟶ Y) (s t : T ⟶ Y) (i : T' ⟶ T) (s' t' : T' ⟶ Y') (d : ℕ), Part j → Res j s t i s' t' →
    (∀ x : T, s x ∈ Set.range j → t x ∈ Set.range j) → FEt s d → FEt s' d

def CorrCut : Prop :=
  ∀ (l : ℕ) (Y' Y T' : Scheme.{0}) (j : Y' ⟶ Y) (T : crystallineComparison.Corr l Y) (i : T' ⟶ T.Z) (s' t' : T' ⟶ Y'), Part j → Res j T.p T.r i s' t' →
    (∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j) →
    IsFinite s' ∧ Etale (s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ Y',
        Nat.card {z : Spec (CommRingCat.of K) ⟶ T' // z ≫ s' = y} = T.d

def PtIdCut : Prop :=
  ∀ (l q n : ℕ) (Y' Y : Scheme.{0}) (j : Y' ⟶ Y) (π : Γ(Y, ⊤)) (T : Fin (n + 1) → crystallineComparison.Corr l Y) (T' : Fin (n + 1) → crystallineComparison.Corr l Y')
    (i : ∀ a, (T' a).Z ⟶ (T a).Z), Part j → (∀ a, Res j (T a).p (T a).r (i a) (T' a).p (T' a).r) →
    (∀ a (x : (T a).Z), (T a).p x ∈ Set.range j → (T a).p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → (T a).r x ∈ Set.range j) →
    crystallineComparison.PtId l q n π T → crystallineComparison.PtId l q n (j.appTop π) T'

end UpperTheory.Gal.Int.Geo.Cut
