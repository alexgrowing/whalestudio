import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pullIdentity_move {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} {r r' : W ⟶ B} (e : r = r') (c : W ⟶ Z) {J : Type} [Fintype J]
    (t : J → (W ⟶ Z')) (y : T.H p) (x : T.H p') (h : c ≫ p = r) (h' : c ≫ p = r')
    (k : ∀ j, t j ≫ p' = r) (k' : ∀ j, t j ≫ p' = r')
    (H : T.pull c h y = ∑ j, T.pull (t j) (k j) x) :
    T.pull c h' y = ∑ j, T.pull (t j) (k' j) x := by
  subst e
  exact H

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e
  rfl

private theorem bcMap_comp' {B B' X Y V : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : V ⟶ B'}
    (f : Y ⟶ X) (f' : V ⟶ Y) (h : f ≫ p = q) (h' : f' ≫ q = r) (h'' : (f' ≫ f) ≫ p = r) :
    bcMap g (f' ≫ f) h'' = bcMap g f' h' ≫ bcMap g f h := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g f' h'), bcMap_fst,
      Category.assoc]
  · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]

theorem UpperTheory.Gal.G3.pOpBc :
    BcSplits → BcGal → OpBc.{u} := by
  intro hS hG B B' R _ T g Z Y Z' p q p' s _ _ t hs ht A hA
  obtain ⟨W, c, G, _, _, a, J, _, σ, hh, hgal, hspl, hsum⟩ := hA
  have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
    rw [← hs, ← Category.assoc, hspl.1 j]
  have ha : ∀ x, a x ≫ (c ≫ p) = c ≫ p := fun x => by
    rw [← Category.assoc, hgal.2.2.2.2.2.1 x]
  refine ⟨pullback (c ≫ p) g, bcMap g c rfl, G, inferInstance, inferInstance,
    fun x => bcMap g (a x) (ha x), J, inferInstance, fun j => bcMap g (σ j) (hσ j), ?_,
    hG g p (c ≫ p) c rfl G a ha hgal, (hS g p q (c ≫ p) s hs c rfl J σ hσ).2.2 hspl, ?_⟩
  · intro j
    rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  · intro x
    have e : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j ≫ t) (hh j)) (bcMap_snd g _ (hh j)) x := hsum x
    have e2 : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j) (hσ j) ≫ bcMap g t ht)
          (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x := by
      rw [e]
      exact Finset.sum_congr rfl fun j _ =>
        pull_congr T (bcMap_comp' g t (σ j) ht (hσ j) _) _ _ x
    exact pullIdentity_move T (bcMap_snd g c rfl).symm _ _ _ _ _ _ _ _ e2
