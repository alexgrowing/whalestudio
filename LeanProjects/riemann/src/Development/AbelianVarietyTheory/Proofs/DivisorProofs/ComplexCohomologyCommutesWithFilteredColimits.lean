import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContFin

theorem term_preserves (N : CommRingCat.{0} ⥤ AbCx) (hN : PreservesFilteredColimitsOfSize.{0, 0} N) (n : ℤ) :
    PreservesFilteredColimitsOfSize.{0, 0} (term N n) := by
  constructor
  intro J _ _
  unfold term
  have : PreservesColimitsOfShape J N := hN.preserves_filtered_colimits J
  infer_instance

theorem cohomology_filteredColimit : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  intro N hN
  refine ⟨term_preserves N hN, ?_⟩
  intro J _ _ D c hc n
  have E : ∀ m : ℤ, (∀ x : ((N).obj c.pt).X m, ∃ j y, ((N).map (c.ι.app j)).f m y = x) ∧
      ∀ j (y : ((N).obj (D.obj j)).X m), ((N).map (c.ι.app j)).f m y = 0 → ∃ (k : J) (f : j ⟶ k), ((N).map (D.map f)).f m y = 0 :=
    fun m => ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N m)).mp (term_preserves N hN m)) J D c hc

  have nat : ∀ {a b : CommRingCat.{0}} (g : a ⟶ b) (p q : ℤ) (x : ((N).obj a).X p),
      ((N).map g).f q (((N).obj a).d p q x) = ((N).obj b).d p q (((N).map g).f p x) := by
    intro a b g p q x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ((N).map g).comm]
  have mapf : ∀ {j k : J} (f : j ⟶ k) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (c.ι.app k)).f m (((N).map (D.map f)).f m x) = ((N).map (c.ι.app j)).f m x := by
    intro j k f m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, c.w f]
  have mapcomp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (D.map (f ≫ g))).f m x = ((N).map (D.map g)).f m (((N).map (D.map f)).f m x) := by
    intro j k l f g m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← D.map_comp]
  constructor
  · intro z hz
    obtain ⟨j, w, hw⟩ := (E n).1 z
    have h1 : ((N).map (c.ι.app j)).f (n + 1) (((N).obj (D.obj j)).d n (n + 1) w) = 0 := by
      rw [nat, hw]
      exact hz
    obtain ⟨k, f, hf⟩ := (E (n + 1)).2 j _ h1
    refine ⟨k, ((N).map (D.map f)).f n w, 0, ?_, ?_⟩
    · rw [← nat, hf]
    · rw [mapf, hw, map_zero, add_zero]
  · intro j w _ ⟨y, hy⟩
    obtain ⟨j', y', rfl⟩ := (E (n - 1)).1 y
    let k := IsFiltered.max j j'
    let fa : j ⟶ k := IsFiltered.leftToMax j j'
    let fb : j' ⟶ k := IsFiltered.rightToMax j j'
    set u := ((N).map (D.map fa)).f n w - ((N).obj (D.obj k)).d (n - 1) n (((N).map (D.map fb)).f (n - 1) y') with hu
    have h0 : ((N).map (c.ι.app k)).f n u = 0 := by
      rw [hu, map_sub, mapf, ← nat, mapf, hy, nat]
      exact sub_self _
    obtain ⟨l, g, hg⟩ := (E n).2 k u h0
    refine ⟨l, fa ≫ g, ((N).map (D.map g)).f (n - 1) (((N).map (D.map fb)).f (n - 1) y'), ?_⟩
    rw [hu, map_sub, sub_eq_zero] at hg
    rw [mapcomp, hg, nat]

end GlobalTheory.EtC.ContFin
