import Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev PCx (R : Type) [CommRing R] := ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ

def Cyc {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∀ m, ((K.d n m).app T).hom x = 0

def Bdy {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∃ y, ((K.d (n + 1) n).app T).hom y = x

def InjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T), Cyc K n T x → Bdy L n T ((φ.f n).app T |>.hom x) →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f → Bdy K n (op U) (((K.X n).map f.op).hom x)

def SurjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (L.X n).obj T), Cyc L n T x →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f →
      ∃ x', Cyc K n (op U) x' ∧ Bdy L n (op U) (((φ.f n).app (op U)).hom x' - ((L.X n).map f.op).hom x)

def LeafHomLoc : Prop := ∀ (R : Type) [CommRing R] (K L : PCx R) (φ : K ⟶ L) (n : ℕ), InjC φ n → SurjC φ n →
  Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n) ∧
  Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n)

def LeafAugSurj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    SurjC ((chainsP R).map (aug _ hc)) n

def LeafAugInj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    InjC ((chainsP R).map (aug _ hc)) n

theorem LeafAugLocal_of (h1 : LeafHomLoc) (hs : LeafAugSurj) (hi : LeafAugInj) : LeafAugLocal := by
  intro J _ D X c ho hcov hdir hc R _ n
  exact h1 R _ _ _ n (hi J D X c ho hcov hdir hc R n) (hs J D X c ho hcov hc R n)

end LateralTheory.CohomologicalPurity.TubeCut
