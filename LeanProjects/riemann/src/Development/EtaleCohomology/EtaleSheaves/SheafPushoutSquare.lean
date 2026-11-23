import Development.EtaleCohomology.EtaleSheaves.LeafSqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcPf LateralTheory.E.LeafSqPf

namespace LateralTheory.E.SheafPushoutSquare

theorem pushout_elem {R : Type} [CommRing R] {MA MB MC : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC) (T : Scheme.{0}ᵒᵖ)
    (z : (pushout a b).obj T) : ∃ (x : MB.obj T) (y : MC.obj T),
      ((pushout.inl a b).app T).hom x + ((pushout.inr a b).app T).hom y = z := by
  have hpo : IsPushout (a.app T) (b.app T) ((pushout.inl a b).app T) ((pushout.inr a b).app T) :=
    (IsPushout.of_hasPushout a b).map ((evaluation _ _).obj T)
  let P : Submodule (ULift.{1} R) ((pushout a b).obj T) :=
    LinearMap.range (((pushout.inl a b).app T).hom.coprod ((pushout.inr a b).app T).hom)
  let π : (pushout a b).obj T ⟶ ModuleCat.of _ (((pushout a b).obj T) ⧸ P) := ModuleCat.ofHom P.mkQ
  have h0 : π = 0 := by
    apply hpo.hom_ext
    · ext x
      exact (Submodule.Quotient.mk_eq_zero P).2 ⟨(x, 0), by simp <;> rfl⟩
    · ext y
      exact (Submodule.Quotient.mk_eq_zero P).2 ⟨(0, y), by simp <;> rfl⟩
  have hz : P.mkQ z = 0 := congrArg (fun f => f.hom z) h0
  obtain ⟨⟨x, y⟩, hxy⟩ := (Submodule.Quotient.mk_eq_zero P).1 hz
  exact ⟨x, y, by simpa using hxy⟩

theorem LeafSheafPush_pf : LeafSheafPush := by
  intro R _ MA MB MC MD a b c d w hon hker
  let φ := pushout.desc c d w
  have hinl : ∀ T x, (φ.app T).hom (((pushout.inl a b).app T).hom x) = (c.app T).hom x := fun T x => by
    change ((pushout.inl a b ≫ φ).app T).hom x = _
    rw [pushout.inl_desc]
  have hinr : ∀ T y, (φ.app T).hom (((pushout.inr a b).app T).hom y) = (d.app T).hom y := fun T y => by
    change ((pushout.inr a b ≫ φ).app T).hom y = _
    rw [pushout.inr_desc]
  have hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} φ := by
    constructor
    intro T z
    obtain ⟨S, hS, hP⟩ := hon T z
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V k hk
    obtain ⟨x, y, hxy⟩ := hP V k hk
    refine ⟨((pushout.inl a b).app _).hom x + ((pushout.inr a b).app _).hom y, ?_⟩
    change (φ.app _).hom _ = _
    rw [map_add, hinl, hinr]
    exact hxy
  have hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} φ := by
    constructor
    intro T u v huv
    obtain ⟨x, y, hxy⟩ := pushout_elem a b T (u - v)
    have h0 : (c.app T).hom x + (d.app T).hom y = 0 := by
      rw [← hinl, ← hinr, ← map_add, hxy, map_sub]
      exact sub_eq_zero.2 huv
    obtain ⟨S, hS, hP⟩ := hker T.unop x y h0
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V k hk
    obtain ⟨w', hw1, hw2⟩ := hP V k hk
    change ((pushout a b).map k.op).hom u = ((pushout a b).map k.op).hom v
    rw [← sub_eq_zero, ← map_sub, ← hxy, map_add]
    have n1 : ((pushout a b).map k.op).hom (((pushout.inl a b).app T).hom x) =
        ((pushout.inl a b).app _).hom ((MB.map k.op).hom x) := by
      change ((pushout.inl a b).app T ≫ (pushout a b).map k.op).hom x = _
      rw [← NatTrans.naturality]; rfl
    have n2 : ((pushout a b).map k.op).hom (((pushout.inr a b).app T).hom y) =
        ((pushout.inr a b).app _).hom ((MC.map k.op).hom y) := by
      change ((pushout.inr a b).app T ≫ (pushout a b).map k.op).hom y = _
      rw [← NatTrans.naturality]; rfl
    have hc : ((pushout.inl a b).app (op V)).hom ((a.app (op V)).hom w') =
        ((pushout.inr a b).app (op V)).hom ((b.app (op V)).hom w') := by
      change ((a ≫ pushout.inl a b).app (op V)).hom w' = ((b ≫ pushout.inr a b).app (op V)).hom w'
      rw [pushout.condition]
    have hy : (MC.map k.op).hom y = -(b.app (op V)).hom w' := by rw [hw2, neg_neg]
    rw [n1, n2, ← hw1, hy, map_neg, hc, add_neg_cancel]
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  have hW : Scheme.etaleTopology.{0}.W φ := Scheme.etaleTopology.W_of_isLocallyBijective φ
  have hiso : IsIso ((presheafToSheaf Scheme.etaleTopology.{0} _).map φ) := (GrothendieckTopology.W_iff _ φ).1 hW
  have h := (IsPushout.of_hasPushout a b).map (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso ((presheafToSheaf _ _).map φ)) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp, ← Functor.map_comp, φ, pushout.inl_desc]
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp, ← Functor.map_comp, φ, pushout.inr_desc]

end LateralTheory.E.SheafPushoutSquare
