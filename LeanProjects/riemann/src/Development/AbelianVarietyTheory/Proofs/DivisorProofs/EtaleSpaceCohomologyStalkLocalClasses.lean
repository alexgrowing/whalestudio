import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ₂ : Over S ⥤ Spc) (α : Θ ⟶ Θ₂), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ.mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ₂.mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ₂.obj V) F n), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ₂.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (Θ₂.map h) F n y = 0 := by
  intro R _ F S Θ Θ' α hΘ hΘ' O _ s hs hα U hU g n
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' S O s hs
  haveI : IsConnected I := IsCofiltered.isConnected I
  have hcF : IsLimit ((Over.forget S).mapCone (Cone.mk _ π)) := isLimitOfPreserves (Over.forget S) hl
  haveI : ∀ i, IsAffine ((G ⋙ Over.forget S).obj i) := fun i => (hG i).1
  haveI : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((G ⋙ Over.forget S).map f) := fun _ => inferInstance
  haveI : LocallyOfFinitePresentation U.hom := inferInstance
  let t0 : G ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app := fun i => (G.obj i).hom, naturality := fun i j f => by simp }
  obtain ⟨j, u0, hu0, hu1⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (G ⋙ Over.forget S) t0 U.hom _ hcF g.left (by
      ext i
      exact (Over.w (π.app i)).trans (Over.w g).symm)
  let u : G.obj j ⟶ U := Over.homMk u0 hu1
  have hu : π.app j ≫ u = g := Over.OverMorphism.ext hu0
  have hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i := fun f => by
    simpa using (π.naturality f).symm
  have hnat : ∀ {A B : Over S} (f : A ⟶ B) (y : H R (Θ'.obj B) F n),
      pull R (Θ.map f) F n (pull R (α.app B) F n y) = pull R (α.app A) F n (pull R (Θ'.map f) F n y) := by
    intro A B f y
    rw [← pull_comp, ← pull_comp, α.naturality]
  have cΘ := hΘ I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  have cΘ' := hΘ' I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  simp only [Functor.mapCone_π_app, Functor.comp_obj, Functor.comp_map] at cΘ cΘ'
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (hα n).2 (pull R (Θ.map g) F n x)
    obtain ⟨i, y0, hy0⟩ := cΘ'.1 w
    let k := IsCofiltered.min i j
    let fi : k ⟶ i := IsCofiltered.minToLeft i j
    let fj : k ⟶ j := IsCofiltered.minToRight i j
    let y1 := pull R (Θ'.map (G.map fi)) F n y0
    have hgh : π.app k ≫ (G.map fj ≫ u) = g := by rw [← Category.assoc, hπ, hu]
    have hd : pull R (Θ.map (π.app k)) F n
        (pull R (α.app (G.obj k)) F n y1 - pull R (Θ.map (G.map fj ≫ u)) F n x) = 0 := by
      have e1 : pull R (Θ.map (π.app k)) F n (pull R (α.app (G.obj k)) F n y1) = pull R (Θ.map g) F n x := by
        rw [hnat]
        show pull R (α.app (Over.mk s)) F n (pull R (Θ'.map (π.app k)) F n (pull R (Θ'.map (G.map fi)) F n y0)) = _
        rw [← pull_comp R (Θ'.map (π.app k)), ← Functor.map_comp, hπ, hy0]
        exact hw
      have e2 : pull R (Θ.map (π.app k)) F n (pull R (Θ.map (G.map fj ≫ u)) F n x) = pull R (Θ.map g) F n x := by
        rw [← pull_comp, ← Functor.map_comp, hgh]
      rw [map_sub, e1, e2, sub_self]
    obtain ⟨k', f', hf'⟩ := cΘ.2 k _ hd
    refine ⟨G.obj k', π.app k', G.map f' ≫ G.map fj ≫ u, pull R (Θ'.map (G.map f')) F n y1, (hG k').2, ?_, ?_⟩
    · rw [← Category.assoc, hπ, hgh]
    · rw [map_sub, sub_eq_zero, hnat] at hf'
      rw [hf', ← pull_comp, ← Functor.map_comp]
  · have h0 : pull R (Θ'.map g) F n y = 0 := (hα n).1 (by rw [map_zero, ← hnat, hy, map_zero])
    rw [← hu, Functor.map_comp, pull_comp] at h0
    obtain ⟨k, f, hf⟩ := cΘ'.2 j _ h0
    exact ⟨G.obj k, π.app k, G.map f ≫ u, (hG k).2, by rw [← Category.assoc, hπ, hu],
      by rw [Functor.map_comp, pull_comp, hf]⟩

end GlobalTheory.EtC
