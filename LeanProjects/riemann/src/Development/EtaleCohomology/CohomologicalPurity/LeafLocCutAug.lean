import Development.EtaleCohomology.CohomologicalPurity.LeafLocCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def chainsP (R : Type) [CommRing R] : Spc ⥤ ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ :=
  (SimplicialObject.whiskering _ _).obj (freeP R) ⋙ AlgebraicTopology.alternatingFaceMapComplex _

def LeafQisLocal : Prop := ∀ (R : Type) [CommRing R] (E E' : Spc) (f : E ⟶ E'),
  (∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  (∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  QuasiIso ((chains R).map f)

def LeafAugLocal : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n) ∧
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n)

theorem LeafLocCutAug.goal_of (hq : LeafQisLocal) (hl : LeafAugLocal) : EtaleLocAug := by
  intro J _ D X c ho hcov hdir hc R _
  exact hq R _ _ (aug _ hc) (fun n => (hl J D X c ho hcov hdir hc R n).1) (fun n => (hl J D X c ho hcov hdir hc R n).2)

theorem LeafLocCutAll.goal_of (hb : EtaleLocBase) (hq : LeafQisLocal) (hl : LeafAugLocal) : LeafLoc :=
  LeafLocCut.goal_of hb (LeafLocCutAug.goal_of hq hl)

end LateralTheory.CohomologicalPurity.TubeCut
