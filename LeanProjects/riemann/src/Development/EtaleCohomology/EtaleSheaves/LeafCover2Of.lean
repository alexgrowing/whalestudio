import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafCover2Pf

variable (R : Type) [CommRing R]

theorem pre_eq {P Q : PSh} (G : Shv R) (φ : Q ⟶ P) (u v : (free R).obj P ⟶ G)
    (h : (free R).map φ ≫ u = (free R).map φ ≫ v) :
    (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ u.hom) =
      (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ v.hom) := by
  have k := congrArg (fun w => toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ w.hom) h
  exact (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) u.hom).trans
    (k.trans (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) v.hom).symm)

theorem gen_eq {P Q : PSh} (G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : Q ⟶ P) (a b : (freeP R).obj P ⟶ G)
    (h : (freeP R).map φ ≫ a = (freeP R).map φ ≫ b) (Y : Scheme.{0}) (y : Q.obj (op Y)) :
    a.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) := by
  have e : ((freeP R).map φ).app (op Y) (ModuleCat.freeMk (ULift.up y)) =
      ModuleCat.freeMk (ULift.up (φ.app _ y)) := by
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have h3 := congrArg (fun w => w (ModuleCat.freeMk (ULift.up y)))
    (congrArg (fun t => ConcreteCategory.hom t) (NatTrans.congr_app h (op Y)))
  simp only [NatTrans.comp_app] at h3
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e] at h3
  exact h3

theorem loc_eq {P : PSh} (G : Shv R) (a b : (freeP R).obj P ⟶ G.obj) (X : Scheme.{0}) (x : P.obj (op X))
    (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X)
    (h : ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
      a.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x)))) :
    a.app (op X) (ModuleCat.freeMk (ULift.up x)) = b.app (op X) (ModuleCat.freeMk (ULift.up x)) := by
  have key : ∀ (c : (freeP R).obj P ⟶ G.obj) (Y : Scheme.{0}) (k : Y ⟶ X),
      G.obj.map k.op (c.app (op X) (ModuleCat.freeMk (ULift.up x))) = c.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) := by
    intro c Y k
    have n1 := ConcreteCategory.congr_hom (c.naturality k.op) (ModuleCat.freeMk (ULift.up x))
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
    rw [← n1]
    congr 1
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have hE := Presheaf.IsSheaf.hom_ext G.2 ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (a.app (op X) (ModuleCat.freeMk (ULift.up x)))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (b.app (op X) (ModuleCat.freeMk (ULift.up x))))) (by
      intro I
      ext1
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      erw [key a, key b]
      exact h _ _ I.hf)
  have := ConcreteCategory.congr_hom hE (1 : ULift R)
  simpa using this

theorem LeafCover2_of : LateralTheory.E.D2.LeafCover2 := by
  intro R _ U V E f g hf hg hc
  refine ⟨hf, hg, fun n => ⟨fun {G} u v huv => ?_⟩⟩
  induction n using Opposite.rec with | op n => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = SimplexCategory.mk m := ⟨n.len, rfl⟩
  have h1 : (free R).map (f.app _) ≫ u = (free R).map (f.app _) ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have h2 : (free R).map (g.app _) ≫ u = (free R).map (g.app _) ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  have p1 := pre_eq R G _ u v h1
  have p2 := pre_eq R G _ u v h2
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (P := (freeP R).obj (E.obj (op (SimplexCategory.mk m)))) _ _ _ G.2 ?_
  apply NatTrans.ext
  funext Y
  induction Y using Opposite.rec with | op X => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  obtain ⟨S, hS, hk⟩ := hc m X x
  refine loc_eq R G _ _ X x S hS ?_
  intro Y k hk'
  rcases hk Y k hk' with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]; exact gen_eq R _ _ _ _ p1 Y y
  · rw [← hy]; exact gen_eq R _ _ _ _ p2 Y y

end LateralTheory.E.LeafCover2Pf
