import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling.Comp
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut CochainComplex.HomComplex

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm = rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' := by
  simp only [rmap]
  convert (CochainComplex.mappingCone.map_comp (φ₁ := (chains R).map f'') (φ₂ := (chains R).map f')
    (φ₃ := (chains R).map f) (a := (chains R).map u') (b := (chains R).map e') (a' := (chains R).map u)
    (b' := (chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm'])
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm])).symm using 2 <;> simp [Functor.map_comp]

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) = rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y := by
  simp only [rpull]
  rw [← hkpull_comp, rmap_comp]

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y : Hrel (ZMod q) (sch.map f) (tw q i) n) :
    rpl q i f' f'' u' e' comm' n (rpl q i f f' u e comm n y) = rpl q i f f'' (u' ≫ u) (e' ≫ e) comm'' n y := by
  simp only [rpl]
  rw [rpull_comp (ZMod q) _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp]; rw [comm''])]
  simp only [Functor.map_comp]
