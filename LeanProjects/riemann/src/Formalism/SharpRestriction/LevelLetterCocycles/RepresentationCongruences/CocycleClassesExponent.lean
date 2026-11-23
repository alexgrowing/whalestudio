import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {PD : PeriodData G Qp K₀ K B BdR}

theorem cocycle_classes_exponent {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    (Zc : Finset (LatticeCohomology T₂.L))
    (hZc : ∀ z ∈ Zc, z ∈ latticeFiniteCohomology PD T₂.L)
    (h : ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ e) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O (Zc : Set (LatticeCohomology T₂.L))) :
    ∃ Z : Finset (G → T₂.V), Z.card ≤ Zc.card ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD F Z e := by
  classical
  have hrep : ∀ z ∈ Zc, ∃ a : ↥(latticeCocycles T₂.L), (a : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ a = z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hZc z hz)
    exact ⟨a, ha, rfl⟩
  choose! r hr1 hr2 using hrep
  refine ⟨Zc.image (fun z => (r z : G → T₂.V)), Finset.card_image_le, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hr1 z hz
  · intro c hc
    have hc' : c ∈ latticeCocycles T₂.L ⊓ _ := hc
    have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.mp hc').1
    have hx : Submodule.mkQ _ (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) ∈ latticeFiniteCohomology PD T₂.L :=
      Submodule.mem_map_of_mem (p := (latticeFiniteCocycles PD T₂.L).comap (latticeCocycles T₂.L).subtype) hc
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (h _ hx)
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy0
    have ha' : (a : G → T₁.V) ∈ latticeFiniteCocycles PD T₁.L := ha
    have hspan : Submodule.span O (Zc : Set (LatticeCohomology T₂.L)) =
        (Submodule.span O (r '' (Zc : Set (LatticeCohomology T₂.L)))).map (Submodule.mkQ _) := by
      rw [Submodule.map_span, Set.image_image, Set.image_congr (g := fun z => z) (fun z hz => hr2 z hz),
        Set.image_id']
    rw [hspan] at hw
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hw
    have e1 : F.H1map (Submodule.mkQ _ a) =
        Submodule.mkQ _ (⟨F.post a, F.post_Z1T _ a.2⟩ : ↥(latticeCocycles T₂.L)) := rfl
    have hker : ((PD.p : ℕ) : O) ^ e • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) -
        ⟨F.post a, F.post_Z1T _ a.2⟩ - s ∈ (latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype := by
      rw [← Submodule.ker_mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype), LinearMap.mem_ker, map_sub, map_sub,
        map_smul, ← hyw, e1]
      abel
    have hb : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ latticeCoboundaries T₂.L := hker
    have hs' : (s : G → T₂.V) ∈
        Submodule.span O ((Zc.image fun z => (r z : G → T₂.V) : Finset (G → T₂.V)) : Set (G → T₂.V)) := by
      have hm := Submodule.mem_map_of_mem (f := (latticeCocycles T₂.L).subtype) hs
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)
    have hpa : F.post a ∈ F.ImF PD := Submodule.mem_sup_left (Submodule.mem_map_of_mem ha')
    have hbI : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ F.ImF PD := Submodule.mem_sup_right hb
    have key : ((PD.p : ℕ) : O) ^ e • c =
        (F.post a + (((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V))) + s := by abel
    rw [key]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ hpa hbI)) (Submodule.mem_sup_right hs')

end Core

end Formalism.MainNotions.N.Ln17
