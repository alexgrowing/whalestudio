import Development.EtaleCohomology.EtaleSheaves.ChernClassSpecialization
import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsQthRootOfUnitWhenQInvertible

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassRootLocalization

open LateralTheory.E.CupProductRingLaws LateralTheory.E.ChernCocycleExistenceAndUniqueness

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  have hF := ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => hab V g hg)

variable {R : Type} [CommRing R] in
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res g (freeGen R P U x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (show uliftFunctor.{1, 0}.obj (P.obj (op U)) from ULift.up x))
  refine Eq.trans ?_ key
  unfold freeGen
  congr 1
  simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]
  erw [ModuleCat.free_map_apply]
  rfl

variable {R : Type} [CommRing R] in
theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : ev α p s h V (x.res g) = Sec.res g (ev α p s h U x) := by
  unfold ev Sx.res
  rw [freeGen_res]
  exact NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op _

def LeafRootLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem evUnique_of (hr : LeafRootLoc) : EtaleKummerChernCocycleEvaluationsUnique := by
  intro q _ E L hq γ γ' h h'
  constructor
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U x) fun V g hv => ?_
    obtain ⟨v, hv⟩ := hv
    rw [← ev_res, ← ev_res, h.2.1 V _ v hv, h'.2.1 V _ v hv]
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 0 1 (by omega)))
      (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 1 1 (by omega)))) fun V g hv => ?_
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hv
    rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
    rw [← ev_res, ← ev_res, h.2.2 V _ v w hv hw, h'.2.2 V _ v w hv hw]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hr : LeafRootLoc) : EtaleFirstChernClassRepresentedByChernCocycle :=
  LateralTheory.E.ChernCocycleExistenceAndUniqueness.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique hE (evUnique_of hr)

end LateralTheory.E.ChernClassRootLocalization
