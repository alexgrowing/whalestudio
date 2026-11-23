import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOnUnitLocusPieceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisObjectsUnitLociCoverAboveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem twoCocycle_coboundary_of_basisFunctor_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T z hz
  classical
  obtain ⟨n, d, hd, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (d i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (d i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt
  obtain ⟨f, hf⟩ := GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt F G H hcov hdir T n d hd z hz
    fun i ↦ GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece F G H hdir T (d i) (p i) (v i) (hp i) z hz
  have hup : ∀ t (u : T ⟶ G.obj t) t' t'' (a : t ⟶ t') (b : t' ⟶ t''),
      (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) → ∃ i, IsUnit (mp F (u ≫ G.map (a ≫ b)) (d i)) := by
    rintro t u t' t'' a b ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [G.map_comp, ← Category.assoc, mp_comp]
    exact hi.map _
  obtain ⟨h, hh⟩ := Desc.coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t)
    (fun u a ↦ u ≫ G.map a) (fun u a b ↦ by simp only [Functor.map_comp, Category.assoc])
    (fun _ _ ↦ True) (fun t u ↦ ∃ i, IsUnit (mp F u (d i))) (fun _ _ _ _ _ ↦ trivial)
    (fun t u _ ↦ GlobalTheory.T.eq_zero_of_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c) f
    (fun t t' t'' u a b hi ↦ hf t t' t'' u a b hi)
  exact ⟨h, fun t t' t'' u a b ↦ hh t t' t'' u a b trivial⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
