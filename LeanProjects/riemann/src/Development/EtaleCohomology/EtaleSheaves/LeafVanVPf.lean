import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanVPf

theorem free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] : IsZero ((free R).obj (yoneda.obj X)) := by
  have key : ∀ (F : Shv R) (f g : (freeP R).obj (yoneda.obj X) ⟶ F.obj), f = g := by
    intro F f g
    ext1
    funext U
    by_cases hU : IsEmpty U.unop
    · have hb : ⊥ ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology _
      exact (Sheaf.isTerminalOfBotCover F U.unop hb).hom_ext _ _
    · apply ModuleCat.free_hom_ext
      rintro ⟨x⟩
      exfalso
      apply hU
      exact ⟨fun u => IsEmpty.false ((show U.unop ⟶ X from x) u)⟩
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  exact key _ _ _

theorem chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  by_cases h : n ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact (free_empty R X).of_iso (chainsXIso R _ p)
  · refine HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat n ?_
    intro i hi
    change -(i : ℤ) = n at hi
    omega

theorem isIso_inr {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (h : ∀ n, IsZero (K.X n)) : IsIso (mappingCone.inr φ) := by
  have : ∀ n, IsIso ((mappingCone.inr φ).f n) := fun n =>
    ⟨(mappingCone.snd φ).v n n (add_zero n), by simp, by
      rw [← mappingCone.id_X φ n (n + 1) rfl, (h (n + 1)).eq_of_tgt ((mappingCone.fst φ).1.v n (n + 1) rfl) 0]
      simp⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem subsingleton_of_iso {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (m : ℤ)
    (h : Subsingleton (HK R K F m)) : Subsingleton (HK R L F m) := by
  have key : ∀ x : HK R L F m, HK.pull R (inv f) F m (HK.pull R f F m x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, IsIso.inv_hom_id, Cochain.id_comp]
  exact ⟨fun x y => by rw [← key x, ← key y, Subsingleton.elim (HK.pull R f F m x) (HK.pull R f F m y)]⟩

theorem LeafVanV_of : LateralTheory.E.LeafVan0Pf.LeafVanV := by
  intro _ q _ i B W Y S ι p s hs m hm
  have he : IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun z => by
    refine hs (pullback.snd p s (pullback.fst (pullback.snd p s ≫ s) ι z)) ⟨pullback.snd (pullback.snd p s ≫ s) ι z, ?_⟩
    have hc := congrArg (fun f => f z) (pullback.condition (f := pullback.snd p s ≫ s) (g := ι))
    simpa using hc.symm⟩
  have := isIso_inr ((chains (ZMod q)).map (sch.map (LateralTheory.E.LeafVan0Pf.prS p ι s))) (chains_empty _ _)
  exact subsingleton_of_iso (mappingCone.inr _) _ m hm

end LateralTheory.E.LeafVanVPf
