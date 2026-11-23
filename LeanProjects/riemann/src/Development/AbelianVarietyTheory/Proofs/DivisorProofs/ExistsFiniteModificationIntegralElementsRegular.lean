import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finSub_of_isIntegralElem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens)
    (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) →
    (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) →
    ∃ F : ∀ V : M.S.Opens, Subring Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ V), IsFinSub M.gp F ∧ ∀ m, b m ∈ F (U m) := by
  classical
  intro R _ _ _ M n U b hU hb
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : M.S.IsSeparated := ⟨by rw [← terminal.comp_from M.π]; infer_instance⟩

  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : M.S.affineOpens => (V.1 : Set M.S))
    (fun V => V.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := M.S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  let r := s.card
  let Vc : Fin r → M.S.Opens := fun i => (s.equivFin.symm i).1.1
  have hVa : ∀ i, IsAffineOpen (Vc i) := fun i => (s.equivFin.symm i).1.2
  have hcov : (⨆ i, Vc i) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨s.equivFin ⟨V, hV⟩, by simpa [Vc] using hx⟩
  have hloc : ∀ (i : Fin r) (m : Fin n), ∃ t : Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i),
      (∀ y ∈ t, (M.gp.app (Vc i)).hom.IsIntegralElem y) ∧
      resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m) (b m) ∈ Subring.closure (Set.range (M.gp.app (U m ⊓ Vc i)).hom ∪
        resK M.gp (inf_le_right : U m ⊓ Vc i ≤ Vc i) '' (t : Set _)) := by
    intro i m
    refine GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le M.gp (Vc i) (U m ⊓ Vc i) inf_le_right (hVa i) ((hU m).inf (hVa i)) _ ?_
    obtain ⟨p, hp, hpe⟩ := hb m
    refine ⟨p.map (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (M.gp.app (U m ⊓ Vc i)).hom.comp (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom =
        (resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m)).comp (M.gp.app (U m)).hom := by
      ext a; exact (resK_app M.gp _ a).symm
    rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero]
  choose t ht hbt using hloc
  let T : ∀ i, Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i) := fun i => Finset.univ.biUnion (t i)
  refine ⟨finFam M.gp Vc T, ⟨fun V _ a => finFam_range _ _ _ _ a, fun V V' hle _ _ x hx => finFam_res _ _ _ V V' hle x hx,
    fun V hV f x hx => GlobalTheory.T.finiteGeneratedSubring_localised_basicOpen M.gp Vc T V hV f x hx, fun V hV => GlobalTheory.T.finite_generation_integral_family_sections M.gp Vc T hcov ?_ V hV⟩, ?_⟩
  · intro i y hy
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 (show y ∈ Finset.univ.biUnion (t i) from hy)
    exact ht i m y hm
  · intro m
    rw [mem_finFam]
    intro i
    refine Subring.closure_mono ?_ (hbt i m)
    rintro _ (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, show z ∈ Finset.univ.biUnion (t i) from Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hz⟩, rfl⟩

theorem finiteModif_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  intro R _ _ _ M n U b hU hb
  obtain ⟨F, hF, hbF⟩ := exists_finSub_of_isIntegralElem R M n U b hU hb
  haveI : IsIntegral M.S := M.integral
  haveI : IsDominant M.gp := M.dominant
  obtain ⟨S', h, gp', hgp, hfin, hint, hdom, hsec⟩ := GlobalTheory.T.exists_finite_normalization_integral_sections M.gp F hF
  haveI := M.proper
  let M' : Modif R :=
    { S := S', π := h ≫ M.π, proper := inferInstance, integral := hint, gp := gp',
      gp_π := by rw [← Category.assoc, hgp, M.gp_π], dominant := hdom }
  exact ⟨M', h, hgp, hfin, rfl, fun m => hsec (U m) (hU m) (b m) (hbF m)⟩

end GlobalTheory.Mum
