import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

variable {R : Type} [CommRing R] {X : Scheme.{0}}

private theorem res_res_lemma {A B C : X.Opens} (f : B ⟶ A) (g' : C ⟶ B) (s : Γ(X, A)) :
    X.presheaf.map g'.op (X.presheaf.map f.op s) = X.presheaf.map (g' ≫ f).op s := by
  rw [op_comp, Functor.map_comp]
  rfl

theorem eq_of_res_affine (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W
    (fun i => homOfLE i.2)
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X) hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    exact h i.1 i.2

theorem exists_global (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i : X.affineOpens => i.1) g := by
    intro i j
    apply eq_of_res_affine
    intro V hV
    rw [res_res_lemma, res_res_lemma]
    exact (hg i V (hV.trans inf_le_left)).trans (hg j V (hV.trans inf_le_right)).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i : X.affineOpens => i.1) ⊤
    (fun i => homOfLE le_top) (by
      intro x _
      obtain ⟨V, hV, hxV, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X)
          (show x ∈ (⊤ : X.Opens) from trivial)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨V, hV⟩, hxV⟩) g hcompat
  exact ⟨t, ht⟩

theorem algebraMap_sec (s : X ⟶ Sp R) (U : X.Opens) (r : R) :
    algebraMap R (Sec s U) r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl

theorem stein_of_bijective (s : X ⟶ Sp R) (h : Function.Bijective s.appTop.hom) : Stein (OAff s) := by
  have key : ∀ (r : R) (U : X.affineOpens),
      (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) (op U) = X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r U
    exact algebraMap_sec s U.1 r
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hg : ∀ (U V : X.affineOpens) (hUV : V.1 ≤ U.1),
          X.presheaf.map (homOfLE hUV).op (y (op U)) = y (op V) := by
        intro U V hUV
        have e := congrFun (congrFun (congrFun hy (op U)) (op V)) (homOfLE (show V ≤ U from hUV)).op
        have e' : (show Γ(X, V.1) from y (op V)) - X.presheaf.map (homOfLE hUV).op (y (op U)) = 0 := e
        exact (sub_eq_zero.mp e').symm
      obtain ⟨t, ht⟩ := exists_global (fun U => y (op U)) hg
      obtain ⟨x, hx⟩ := h.2 t
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      funext T
      have hxinv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
        congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      have e1 := key ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) T.unop
      rw [hxinv, hx] at e1
      exact e1.trans (ht T.unop)
    · rintro ⟨r, rfl⟩
      funext T T' φ
      have hc : (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) =
          (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' := (GlobalTheory.CatCoh.mp (OAff s) φ).commutes r
      show (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' -
          (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) = 0
      rw [hc, sub_self]
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have e : s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
      apply eq_of_res_affine
      intro V hV
      rw [map_zero]
      have e2 := congrFun hr (op V)
      rw [key] at e2
      exact e2
    have e3 := h.1 (e.trans (map_zero _).symm)
    have hr2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
      congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
    rw [e3, map_zero] at hr2
    exact hr2.symm

theorem stein_holds : SteinSt := by
  unfold MainStatements.Hodge.SteinSt MainStatements.Hodge.AllAb
  intro R _ A _ g hA _
  exact stein_of_bijective A.hom (GlobalTheory.globalFns_holds (Sp R) A hA)

end GlobalTheory.CompanionTheory.Hodge
