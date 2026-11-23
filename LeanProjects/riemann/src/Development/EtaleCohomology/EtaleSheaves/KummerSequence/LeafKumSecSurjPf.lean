import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection

namespace LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf

theorem surj_of_mem {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] {U : Scheme.{0}}
    (s : Sec G U) (hs : Presheaf.imageSieve φ.hom s ∈ Scheme.etaleTopology U) :
    ∃ t : Sec F U, Sec.map φ t = s := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.cond)
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology G.obj (forget _)).1 G.cond)
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) (Presheaf.imageSieve φ.hom s).arrows :=
    fun V f hf => Presheaf.localPreimage φ.hom s f hf
  have hx : x.Compatible := by
    intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 w
    apply sec_injective φ Z
    have e1 := NatTrans.naturality_apply φ.hom g1.op (x f1 h1)
    have e2 := NatTrans.naturality_apply φ.hom g2.op (x f2 h2)
    dsimp only [Functor.comp_map] at *
    show φ.hom.app _ (F.obj.map g1.op (x f1 h1)) = φ.hom.app _ (F.obj.map g2.op (x f2 h2))
    rw [e1, e2]
    simp only [x, Presheaf.app_localPreimage]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, w]
  obtain ⟨t, ht, -⟩ := hF _ hs x hx
  refine ⟨t, ?_⟩
  apply (hG _ hs).isSeparatedFor.ext
  intro V f hf
  dsimp only [Functor.comp_map]
  have e := NatTrans.naturality_apply φ.hom f.op t
  show G.obj.map f.op (φ.hom.app _ t) = G.obj.map f.op s
  rw [← e]
  have := ht f hf
  refine (congrArg (φ.hom.app (op V)) this).trans ?_
  exact Presheaf.app_localPreimage φ.hom s f hf

def LeafUnitRoot : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) →
  ∀ b : (Γ(V, ⊤))ˣ, Presheaf.imageSieve (powGm q).hom (unitsToSec V (Additive.ofMul b)) ∈ Scheme.etaleTopology V

theorem kum_le (q : ℕ) {U : Scheme.{0}} (s : Sec Gm U) :
    Presheaf.imageSieve (powGm q).hom s ≤ Presheaf.imageSieve (kumM q).hom s := by
  rintro V f ⟨t, ht⟩
  refine ⟨(kumSC q).g.hom.app _ t, ?_⟩
  rw [← ht, ← kumSC_g_kumM q]
  rfl

theorem LeafKumSecSurj_of (hR : LeafUnitRoot) : LateralTheory.E.H2CurveOrder.KummerH0Surjection.LeafKumSecSurj := by
  intro q _ U hq s
  apply surj_of_mem
  apply Scheme.etaleTopology.superset_covering (kum_le q s)
  have hS : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) s ∈
      Scheme.etaleTopology U := @Presheaf.imageSieve_mem _ _ Scheme.etaleTopology _ _ _ _ _ _ _ _ (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (Presheaf.isLocallySurjective_toSheafify' (J := Scheme.etaleTopology) _) (op U) s
  refine Scheme.etaleTopology.transitive hS _ ?_
  rintro V f ⟨b, hb⟩
  rw [Presheaf.pullback_imageSieve]
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map f.appTop.hom
  have key := hR q V hqV (Additive.toMul b.down)
  have e : unitsToSec V (Additive.ofMul (Additive.toMul b.down)) = Gm.obj.map f.op s := hb
  rw [e] at key
  exact key

end LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf
