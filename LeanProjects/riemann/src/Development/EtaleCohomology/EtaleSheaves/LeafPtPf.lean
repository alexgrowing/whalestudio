import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

theorem eq_generic_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) (x : X) :
    x = genericPoint X := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).1 hd
  let S : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hST : S ≤ T := fun _ _ => Set.mem_univ _
  have hTS : T ≤ S := hmax S hST
  have h1 : genericPoint X ⤳ x := genericPoint_specializes x
  have h2 : x ⤳ genericPoint X := by
    rw [specializes_iff_mem_closure]
    exact hTS (Set.mem_univ (genericPoint X))
  exact (h2.antisymm h1).eq

theorem subsingleton_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) : Subsingleton X :=
  ⟨fun x y => (eq_generic_of_dim hd x).trans (eq_generic_of_dim hd y).symm⟩

theorem leafPtIso (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    (hd : topologicalKrullDim X ≤ 0) : IsIso p := by
  haveI := subsingleton_of_dim hd
  haveI : IsAffine X := inferInstance
  let F : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ p.appTop
  have hfin : p.appTop.hom.Finite := finite_appTop_of_universallyClosed k p
  have hFfin : F.hom.Finite := by
    simp only [F, CommRingCat.hom_comp]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k Γ(X, ⊤) := F.hom.toAlgebra
  haveI : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun a => hFfin.to_isIntegral a⟩
  have hb : Function.Bijective F.hom := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).2 hb
  haveI : IsIso p.appTop := by
    have : p.appTop = (Scheme.ΓSpecIso _).hom ≫ F := by simp [F]
    rw [this]; infer_instance
  have e : p = X.isoSpec.hom ≫ Spec.map p.appTop ≫ (Sp k).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]; infer_instance

theorem sh_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] : SH k := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (IsLocalRing.residue k) := by
    exact ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField k) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

theorem finite_sp (hH : Hyps) (h0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    (n i : ℤ) : Finite (Ht q (sch.obj (Sp k)) n i) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (hH.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)).1 (sch.obj (Sp k)) n hn
    exact Finite.of_subsingleton
  · exact (h0 hH q k hq i).1
  · haveI := hH.2.2.2.2.2.2.2.2.2.2.2.1 (ZMod q) k (sh_of_isAlgClosed k) (tw q i) n hn
    exact Finite.of_subsingleton

theorem LeafPt_of (h0 : H0TwistOverClosedField) : LeafPt := by
  intro hH q _ k _ _ hq X _ p _ hd n i
  have := leafPtIso k p hd
  haveI := finite_sp hH h0 q k hq n i
  refine Finite.of_injective (pull (ZMod q) (sch.map (inv p)) (tw q i) n) ?_
  intro x y hxy
  have key : ∀ z : Ht q (sch.obj X) n i,
      pull (ZMod q) (sch.map p) (tw q i) n (pull (ZMod q) (sch.map (inv p)) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← key x, ← key y, hxy]

end LateralTheory.E.E4
