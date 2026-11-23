import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactProd

theorem exactAt_of_prod {ι : Type} {c : ComplexShape ℕ} {K : HomologicalComplex AddCommGrpCat.{1} c}
    {L : ι → HomologicalComplex AddCommGrpCat.{1} c} (φ : ∀ i, K ⟶ L i)
    (hφ : ∀ n, Function.Bijective (fun (x : K.X n) (i : ι) => (φ i).f n x)) (p : ℕ)
    (hL : ∀ i, (L i).ExactAt p) : K.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  suffices key : ∀ z : K.X p, K.d p (c.next p) z = 0 → ∃ v : K.X (c.prev p), K.d (c.prev p) p v = z from key
  intro z hz
  have hcomm : ∀ i {q r : ℕ} (x : K.X q), (L i).d q r ((φ i).f q x) = (φ i).f r (K.d q r x) := by
    intro i q r x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ i).comm]
  have hw : ∀ i, ∃ w : (L i).X (c.prev p), (L i).d (c.prev p) p w = (φ i).f p z := by
    intro i
    have hex := hL i
    rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
    refine hex ((φ i).f p z) ?_
    change (L i).d p (c.next p) ((φ i).f p z) = 0
    rw [hcomm, hz, map_zero]
  choose w hw using hw
  obtain ⟨v, hv⟩ := (hφ (c.prev p)).2 w
  refine ⟨v, ?_⟩
  apply (hφ p).1
  funext i
  change (φ i).f p (K.d (c.prev p) p v) = (φ i).f p z
  rw [← hcomm, ← hw i]
  exact congrArg _ (congrFun hv i)

theorem wexact_of_prod (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (ι : Type) (M : ι → T ⥤ AddCommGrpCat.{1})
    (N : T ⥤ AddCommGrpCat.{1}) (π : ∀ i, N ⟶ M i)
    (hπ : ∀ V, Function.Bijective (fun (x : N.obj V) (i : ι) => (π i).app V x))
    (hM : ∀ i, WExact (M i) a) : WExact N a := by
  have nat : ∀ i {P Q : T} (f : P ⟶ Q) (x : N.obj P), (π i).app Q (N.map f x) = (M i).map f ((π i).app P x) := by
    intro i P Q f x
    exact ConcreteCategory.congr_hom ((π i).naturality f) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (hπ U).1
    funext i
    apply (hM i).1
    have h := congrArg ((π i).app _) hxy
    rw [nat, nat] at h
    exact h
  · intro y hy
    have hx : ∀ i, ∃ x : (M i).obj U, (M i).map (a.app (SimplexCategory.mk 0)) x = (π i).app _ y := by
      intro i
      refine (hM i).2.1 ((π i).app _ y) ?_
      rw [← nat, ← nat, hy]
    choose x hx using hx
    obtain ⟨x', hx'⟩ := (hπ U).2 x
    refine ⟨x', ?_⟩
    apply (hπ _).1
    funext i
    change (π i).app _ (N.map (a.app (SimplexCategory.mk 0)) x') = (π i).app _ y
    rw [nat, ← hx i]
    exact congrArg _ (congrFun hx' i)
  · intro n
    refine exactAt_of_prod (fun i => (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map
      (Functor.whiskerLeft X (π i))) (fun k => ?_) (n + 1) (fun i => (hM i).2.2 n)
    exact hπ (X.obj (SimplexCategory.mk k))

end GlobalTheory.EtC.WExactProd

end
