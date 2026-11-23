import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem isolated_in_fibre_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : W.Opens), Etale (f ∣_ U) → ∀ z : M, f z ∈ U →
      ∃ V : M.Opens, z ∈ V ∧ ∀ y ∈ V, f y = f z → y = z := by
  intro M W f U hE z hz
  haveI : LocallyQuasiFinite (f ∣_ U) := by
    refine ⟨fun {U'} hU {V} hV e => ?_⟩
    have h := Scheme.Hom.etale_appLE (f ∣_ U) hU hV e
    algebraize [((f ∣_ U).appLE U' V e).hom]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  let z' : (f ⁻¹ᵁ U : M.Opens) := ⟨z, hz⟩
  obtain ⟨u, hu, huz⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    ((f ∣_ U).isDiscrete_preimage_singleton ((f ∣_ U) z')) z' rfl
  refine ⟨⟨Subtype.val '' u, (f ⁻¹ᵁ U).isOpen.isOpenMap_subtype_val u hu⟩, ⟨z', ?_, rfl⟩, ?_⟩
  · have : z' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by rw [huz]; rfl
    exact this.1
  · rintro y ⟨y', hy'u, rfl⟩ hy
    have hmem : y' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by
      refine ⟨hy'u, ?_⟩
      have h1 := morphismRestrict_base_coe f U y'
      have h2 := morphismRestrict_base_coe f U z'
      exact Subtype.ext (h1.trans (hy.trans h2.symm))
    rw [huz] at hmem
    exact congrArg Subtype.val hmem

end GlobalTheory
