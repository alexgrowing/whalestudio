import Development.EtaleCohomology.EtaleSheaves.TruncKerPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.RelDescPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨y, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (a ≫ b)).comp y.1 (zero_add n) =
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp y.1 (zero_add n)) (zero_add n)
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
  simp only [rmap, Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' comm comm' comm'']
  exact hkpull_comp R _ _ F n y

def RelEqvInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f), Eqv R u F → Eqv R e F → ∀ n : ℤ, Function.Injective (rpull R f f' u e comm F n)

def CechEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E)
  (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''), Et e → SpS e → IsPushout φ' e u φ'' →
  Eqv (ZMod q) (cechAug (Spec.map e)) (tw q i) ∧ Eqv (ZMod q) (cechAug (Spec.map u)) (tw q i)

def LevelInj : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∃ (g : cech (Spec.map u) ⟶ cech (Spec.map e)) (_hA : g ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ'))
    (i0 : sch.obj (Spec E) ⟶ cech (Spec.map e)) (j0 : sch.obj (Spec Y'') ⟶ cech (Spec.map u))
    (h0 : sch.map (Spec.map φ'') ≫ i0 = j0 ≫ g),
    i0 ≫ cechAug (Spec.map e) = sch.map (Spec.map e) ∧ j0 ≫ cechAug (Spec.map u) = sch.map (Spec.map u) ∧
    Function.Injective (rpull (ZMod q) g (sch.map (Spec.map φ'')) j0 i0 h0 (tw q i) n)

theorem relDesc_of (hEq : RelEqvInj) (hC : CechEqv) (hL : LevelInj) : LateralTheory.E.TruncationKernel.RelDesc := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨g, hA, i0, j0, h0, hi, hj, hinj⟩ := hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨hCe, hCu⟩ := hC hH q i φ' e u φ'' he hs hpo'
  have h1 := hEq (ZMod q) (tw q i) (sch.map (Spec.map φ')) g (cechAug (Spec.map u)) (cechAug (Spec.map e)) hA hCu hCe n
  have key : ∀ (a : sch.obj (Spec Y'') ⟶ sch.obj (Spec Y')) (b : sch.obj (Spec E) ⟶ sch.obj (Spec D))
      (ha : j0 ≫ cechAug (Spec.map u) = a) (hb : i0 ≫ cechAug (Spec.map e) = b)
      (c : sch.map (Spec.map φ'') ≫ b = a ≫ sch.map (Spec.map φ')),
      Function.Injective (rpull (ZMod q) (sch.map (Spec.map φ')) (sch.map (Spec.map φ'')) a b c (tw q i) n) := by
    intro a b ha hb c
    subst ha hb
    intro x y hxy
    rw [rpull_comp _ _ g _ _ _ _ _ hA h0 c, rpull_comp _ _ g _ _ _ _ _ hA h0 c] at hxy
    exact h1 (hinj hxy)
  exact key _ _ hj hi _

theorem etale_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (he : Et e) : Etale (Spec.map e) :=
  HasRingHomProperty.Spec_iff.mpr he

theorem surj_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (hs : SpS e) : Surjective (Spec.map e) := by
  constructor
  intro x
  obtain ⟨Q, hQ, hQr⟩ := hs x.asIdeal x.isPrime
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQr⟩

theorem cechEqv : CechEqv := by
  intro hH q _ i D Y' E Y'' φ' e u φ'' he hs hpo
  have hpb := isPullback_SpecMap_of_isPushout φ' e u φ'' hpo
  have hE : Etale (Spec.map e) := etale_spec e he
  have hS : Surjective (Spec.map e) := surj_spec e hs
  have hEu : Etale (Spec.map u) := MorphismProperty.of_isPullback (P := @Etale) hpb.flip hE
  have hSu : Surjective (Spec.map u) := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  exact ⟨hH.2.1 (ZMod q) (Spec.map e) (tw q i), hH.2.1 (ZMod q) (Spec.map u) (tw q i)⟩

end LateralTheory.E.RelDescPf
