import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemIdentityComponentOfRationalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.IdCompMul

theorem mul_mem_of_field {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : Smooth G.hom) (k : Type) [Field k]
    (p : Spec (CommRingCat.of k) ⟶ S) (a b : Over.mk p ⟶ G)
    (ha : a.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))})
    (hb : b.left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (a * b).left (IsLocalRing.closedPoint k) ∈
      {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  let F := Over.pullback p
  let G' : Over (Spec (CommRingCat.of k)) := F.obj G
  have hpt : ∀ z : (Spec (CommRingCat.of k) : Scheme), z = IsLocalRing.closedPoint k :=
    fun z => Subsingleton.elim _ _
  have hsec : η[G'].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
    have hc : pullback.fst (𝟙 S) p = pullback.snd (𝟙 S) p ≫ p := by
      simpa using pullback.condition (f := 𝟙 S) (g := p)
    simp [G', F, hc]
    exact pullback.lift_fst _ _ _
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback G.left S G'.left (Spec (CommRingCat.of k)) G.hom G'.hom p
    (pullback.fst G.hom p) η[G].left η[G'].left hG (IsPullback.of_hasPullback G.hom p)
    (Over.w η[G]) (Over.w η[G']) hsec
  have huniv : ∀ t : (Spec (CommRingCat.of k) : Scheme), G'.hom ⁻¹' {t} = Set.univ :=
    fun t => Set.eq_univ_of_forall fun y => Set.mem_singleton_iff.mpr ((hpt _).trans (hpt t).symm)
  have hq : ∀ z : G'.left,
      pullback.fst G.hom p z ∈
        {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} ↔
      z ∈ connectedComponent ((η[G']).left (IsLocalRing.closedPoint k)) := by
    intro z
    rw [← Set.mem_preimage, key]
    show z ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom z}) ((η[G']).left (G'.hom z)) ↔ _
    rw [huniv, connectedComponentIn_univ, hpt (G'.hom z)]
  let u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ F.obj (Over.mk p) :=
    Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp)) (by simp [F]; exact pullback.lift_snd _ _ _)
  have hgen : ∀ c : Over.mk p ⟶ G, (u ≫ F.map c).left ≫ pullback.fst G.hom p = c.left := by
    intro c
    simp [u, F]
    erw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp]
  have hpoint : ∀ (c : Over.mk p ⟶ G) (t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G'),
      t.left ≫ pullback.fst G.hom p = c.left →
        pullback.fst G.hom p (t.left (IsLocalRing.closedPoint k)) = c.left (IsLocalRing.closedPoint k) := by
    intro c t h
    rw [← h]
    rfl
  have ha' := (hq _).1 (by rw [hpoint a _ (hgen a)]; exact ha)
  have hb' := (hq _).1 (by rw [hpoint b _ (hgen b)]; exact hb)
  have hm := GlobalTheory.T.mul_mem_identityComponent_of_rational' k G' (u ≫ F.map a) (u ≫ F.map b) ha' hb'
  have e1 := hgen (a * b)
  rw [Functor.map_mul, MonObj.comp_mul] at e1
  rw [← hpoint (a * b) _ e1]
  exact (hq _).2 hm

theorem mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G instG hG w h1 h2
  let κ := (G ⊗ G).left.residueField w
  let j : Spec (CommRingCat.of κ) ⟶ (G ⊗ G).left := (G ⊗ G).left.fromSpecResidueField w
  let p : Spec (CommRingCat.of κ) ⟶ S := j ≫ (G ⊗ G).hom
  let a : Over.mk p ⟶ G := Over.homMk (j ≫ (fst G G).left) (by simp [p])
  let b : Over.mk p ⟶ G := Over.homMk (j ≫ (snd G G).left) (by simp [p, pullback.condition])
  have hw : j (IsLocalRing.closedPoint κ) = w := Scheme.fromSpecResidueField_apply w _
  have hl : lift a b = (Over.homMk j rfl : Over.mk p ⟶ G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext1
      simp [a]
    · ext1
      simp [b]
  have hm := mul_mem_of_field G hG κ p a b
    (by
      convert h1 using 2
      exact congrArg (fst G G).left hw)
    (by
      convert h2 using 2
      exact congrArg (snd G G).left hw)
  rw [Hom.mul_def, Over.comp_left, hl] at hm
  convert hm using 2
  exact (congrArg (μ[G]).left hw).symm

end GlobalTheory.IdCompMul
