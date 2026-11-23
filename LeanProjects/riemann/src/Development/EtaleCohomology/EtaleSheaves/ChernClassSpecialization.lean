import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleExistenceAndUniqueness

open LateralTheory.E.CupProductRingLaws

section Ext
variable {R : Type} [CommRing R]

theorem free_hom_ext {P : PSh} {F : Shv R} (f g : (free R).obj P ⟶ F)
    (h : ∀ U x, (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J := Scheme.etaleTopology) f.hom g.hom F.cond
  ext U : 2
  induction U using Opposite.rec with | _ U => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact h U x

theorem cochain_ext_ev {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hev : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) :
    α = β := by
  apply Cochain.ext
  intro p s hps
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
    have : (chainsXIso R E k).inv ≫ α.v _ _ hps = (chainsXIso R E k).inv ≫ β.v _ _ hps :=
      free_hom_ext _ _ (fun U x => hev k s hps U x)
    simpa using this
  · refine (HomologicalComplex.isZero_extend_X _ _ p (fun i => ?_)).eq_of_src _ _
    show -(i : ℤ) ≠ p
    omega

theorem res_isZero (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  HomologicalComplex.isZero_extend_X _ _ s (fun i => by show (i : ℤ) ≠ s; omega)

end Ext

def EtaleKummerChernCocycleEvaluationsUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernClassCocycle q L γ → IsEtaleFirstChernClassCocycle q L γ' →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 1 (by simp) U x = ev γ'.1 1 1 (by simp) U x) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev γ.1 2 0 (by simp) U x = ev γ'.1 2 0 (by simp) U x

def EtaleKummerChernCocycleExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ γ, IsEtaleFirstChernClassCocycle q L γ

theorem etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness (hU : EtaleKummerChernCocycleEvaluationsUnique) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hq : Inv q E)
    (γ γ' : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (h : IsEtaleFirstChernClassCocycle q L γ) (h' : IsEtaleFirstChernClassCocycle q L γ') :
    γ = γ' := by
  obtain ⟨h1, h2⟩ := hU q L hq γ γ' h h'
  apply Subtype.ext
  apply cochain_ext_ev
  intro p s hs U x
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [h.1 U x, h'.1 U x]
  · obtain rfl : s = 1 := by omega
    exact h1 U x
  · obtain rfl : s = 0 := by omega
    exact h2 U x
  · unfold ev
    rw [(res_isZero (tw q 1) s (by omega)).eq_of_tgt ((chainsXIso _ E _).inv ≫ γ.1.v _ _ hs)
      ((chainsXIso _ E _).inv ≫ γ'.1.v _ _ hs)]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hU : EtaleKummerChernCocycleEvaluationsUnique) : EtaleFirstChernClassRepresentedByChernCocycle := by
  intro q _ E L hq
  obtain ⟨γ0, h0⟩ := hE q L hq
  refine ⟨⟨γ0, h0⟩, fun γ hγ => ?_⟩
  have hex : ∃ c : Ht q E 2 1, ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧ IsEtaleFirstChernClassCocycle q L γ :=
    ⟨_, γ0, rfl, h0⟩
  obtain ⟨γ1, hc, h1⟩ := pick_spec hex
  have : γ1 = γ := etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness hU q L hq γ1 γ h1 hγ
  subst this
  exact hc.symm

end LateralTheory.E.ChernCocycleExistenceAndUniqueness
