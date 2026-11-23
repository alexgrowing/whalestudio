import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem exists_point {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (s : C ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (M : Over C) [LocallyOfFiniteType M.hom] (x : M.left) (hx : IsClosed {x}) :
    ∃ (p : Spec (.of k) ⟶ C) (_ : p ≫ s = 𝟙 _) (q : Over.mk p ⟶ M), ∀ a, q.left a = x :=
  ⟨pointOfClosedPoint (M.hom ≫ s) x hx ≫ M.hom, by rw [Category.assoc, pointOfClosedPoint_comp],
    Over.homMk (pointOfClosedPoint (M.hom ≫ s) x hx) rfl, fun a => pointOfClosedPoint_apply _ x hx a⟩

private theorem finite_cover_of_quasi_finite_local {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (s : C ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s] (G : Over C) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (W : G.left.Opens)
    (hW : ∀ p : Spec (.of k) ⟶ C, p ≫ s = 𝟙 _ → ∃ w : Over.mk p ⟶ G, ⊤ ≤ w.left ⁻¹ᵁ W)
    (hZ : ∀ p : Spec (.of k) ⟶ C, p ≫ s = 𝟙 _ → ∀ g : Over.mk p ⟶ G,
          ∃ (Z : Over C) (z : Z ⟶ G) (g₀ : Over.mk p ⟶ Z), QFin Z ∧ g₀ ≫ z = g) :
    ∃ (n : ℕ) (Z : Fin n → Over C) (z : ∀ m, Z m ⟶ G), (∀ m, QFin (Z m)) ∧
      ∀ p : Spec (.of k) ⟶ C, p ≫ s = 𝟙 _ → ∀ y : Over.mk p ⟶ G,
        ∃ (m : Fin n) (g₀ : Over.mk p ⟶ Z m) (w : Over.mk p ⟶ G), ⊤ ≤ w.left ⁻¹ᵁ W ∧ y = (g₀ ≫ z m) * w := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace (G.hom ≫ s)
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (G.hom ≫ s)
  let J := Σ Z : {Z : Over C // QFin Z}, (Z.1 ⟶ G)
  let mv (i : J) : i.1.1 ⊗ G ⟶ G := (fst i.1.1 G ≫ i.2)⁻¹ * snd i.1.1 G
  let O (i : J) : Set G.left := (snd i.1.1 G).left '' ((mv i).left ⁻¹ᵁ W : Set _)
  have hO (i : J) : IsOpen (O i) := by
    obtain ⟨h₁, h₂, -, -⟩ := i.1.2
    have : LocallyOfFinitePresentation i.1.1.hom := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr h₂
    have : UniversallyOpen i.1.1.hom := inferInstance
    have : UniversallyOpen (snd i.1.1 G).left :=
      inferInstanceAs (UniversallyOpen (pullback.snd i.1.1.hom G.hom))
    exact (snd i.1.1 G).left.isOpenMap _ ((mv i).left ⁻¹ᵁ W).isOpen
  have hcov : Set.univ ⊆ ⋃ i, O i := by
    by_contra hne
    have hne' : (⋃ i, O i)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      exact hne h.ge
    obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hne'
      (isOpen_iUnion hO).isClosed_compl.isLocallyClosed
    obtain ⟨p, hp, y, hy⟩ := exists_point s G x hc
    obtain ⟨w, hw⟩ := hW p hp
    obtain ⟨Z, z, g₀, hq, hg⟩ := hZ p hp (y * w⁻¹)
    refine hx (Set.mem_iUnion.2 ⟨⟨⟨Z, hq⟩, z⟩, (lift g₀ y).left (IsLocalRing.closedPoint k), ?_, ?_⟩)
    · have e : lift g₀ y ≫ mv ⟨⟨Z, hq⟩, z⟩ = w := by
        simp only [mv, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd, hg]
        group
      show ((lift g₀ y).left ≫ (mv ⟨⟨Z, hq⟩, z⟩).left) (IsLocalRing.closedPoint k) ∈ W
      rw [← Over.comp_left, e]
      exact hw trivial
    · show ((lift g₀ y).left ≫ (snd Z G).left) (IsLocalRing.closedPoint k) = x
      rw [← Over.comp_left, lift_snd]
      exact hy _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨t.card, fun m => (t.equivFin.symm m).1.1.1, fun m => (t.equivFin.symm m).1.2,
    fun m => (t.equivFin.symm m).1.1.2, fun p hp y => ?_⟩
  obtain ⟨i, hi, x, hxW, hxy⟩ : ∃ i ∈ t, y.left (IsLocalRing.closedPoint k) ∈ O i := by
    simpa using ht (Set.mem_univ (y.left (IsLocalRing.closedPoint k)))
  obtain ⟨m, rfl⟩ : ∃ m, i = (t.equivFin.symm m).1 := ⟨t.equivFin ⟨i, hi⟩, by simp⟩
  refine ⟨m, ?_⟩
  dsimp only
  generalize (t.equivFin.symm m).1 = i at x hxW hxy ⊢
  obtain ⟨-, h₂, -, -⟩ := i.1.2
  have : LocallyOfFiniteType (i.1.1 ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst i.1.1.hom G.hom ≫ i.1.1.hom))
  have : JacobsonSpace (i.1.1 ⊗ G).left := LocallyOfFiniteType.jacobsonSpace ((i.1.1 ⊗ G).hom ≫ s)
  have hy : y.left ≫ G.hom ≫ s = 𝟙 (Spec (.of k)) := by
    rw [← Category.assoc, Over.w y]
    exact hp
  have hyc : IsClosed {y.left (IsLocalRing.closedPoint k)} :=
    ((pointEquivClosedPoint (G.hom ≫ s)) ⟨y.left, hy⟩).2
  obtain ⟨x', ⟨hx'W, hx'y⟩, hc⟩ := nonempty_inter_closedPoints
    (Z := ((mv i).left ⁻¹ᵁ W : Set _) ∩ (snd i.1.1 G).left ⁻¹' {y.left (IsLocalRing.closedPoint k)})
    ⟨x, hxW, hxy⟩ (((mv i).left ⁻¹ᵁ W).isOpen.isLocallyClosed.inter
      (hyc.preimage (snd i.1.1 G).left.continuous).isLocallyClosed)
  obtain ⟨p', hp', q, hq⟩ := exists_point s (i.1.1 ⊗ G) x' hc
  have e : (q ≫ snd i.1.1 G).left = y.left := by
    refine ext_of_apply_closedPoint_eq (K := k) (G.hom ≫ s) ?_ hy ?_
    · rw [← Category.assoc, Over.w (q ≫ snd i.1.1 G)]
      exact hp'
    · exact (congrArg (snd i.1.1 G).left (hq _)).trans hx'y
  obtain rfl : p' = p := (Over.w (q ≫ snd i.1.1 G)).symm.trans ((congrArg (· ≫ G.hom) e).trans (Over.w y))
  have e' : q ≫ snd i.1.1 G = y := Over.OverMorphism.ext e
  refine ⟨q ≫ fst i.1.1 G, q ≫ mv i, fun a _ => ?_, ?_⟩
  · show (mv i).left (q.left a) ∈ W
    rw [hq a]
    exact hx'W
  · simp only [mv, MonObj.comp_mul, GrpObj.comp_inv, e', Category.assoc]
    group

theorem UpperTheory.finite_cover_of_quasi_finite :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
        ∀ (G : Over C) [GrpObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → ∀ W : G.left.Opens,
        (∀ p : Sp k ⟶ C, p ≫ strHom k C = 𝟙 _ → ∃ w : Over.mk p ⟶ G, ⊤ ≤ w.left ⁻¹ᵁ W) →
        (∀ p : Sp k ⟶ C, p ≫ strHom k C = 𝟙 _ → ∀ g : Over.mk p ⟶ G,
          ∃ (Z : Over C) (z : Z ⟶ G) (g₀ : Over.mk p ⟶ Z), QFin Z ∧ g₀ ≫ z = g) →
        ∃ (n : ℕ) (Z : Fin n → Over C) (z : ∀ m, Z m ⟶ G), (∀ m, QFin (Z m)) ∧
          ∀ p : Sp k ⟶ C, p ≫ strHom k C = 𝟙 _ → ∀ y : Over.mk p ⟶ G,
            ∃ (m : Fin n) (g₀ : Over.mk p ⟶ Z m) (w : Over.mk p ⟶ G), ⊤ ≤ w.left ⁻¹ᵁ W ∧ y = (g₀ ≫ z m) * w := by
  intro k _ _ C _ hC G _ h₁ h₂ W hW hZ
  have : IsProper (strHom k C) := by
    obtain ⟨N, i, hi, e⟩ := hC.2.1
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact finite_cover_of_quasi_finite_local (strHom k C) G W hW hZ
