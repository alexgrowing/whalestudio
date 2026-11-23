import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.DegRow

variable {R : Type} [CommRing R] (F : Shv R)

theorem cobd_disc (P : PSh) (s : (free R).obj ((disc.obj P).obj (op ⦋0⦌)) ⟶ F) :
    cobd (E := disc.obj P) s = 0 := by
  simp [cobd, Fin.sum_univ_two, SimplicialObject.δ]

theorem exists_rep (E : Spc) (x : H R E F 0) : ∃ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s x := by
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let b := (z.1 : Cochain ((chains R).obj E) (res R F) 0).v 0 0 (add_zero 0)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v (Cocycle.δ_eq_zero z 1) 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) _ 0 1 (zero_add 1) 0 1 (by omega) (zero_add 1),
      (hpos E 1 one_pos).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  refine ⟨(chainsXIso R E 0).inv ≫ t', z, rfl, ?_⟩
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    change b = (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 0).hom ≫ ((chainsXIso R E 0).inv ≫ t') ≫ resι R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp)
    rw [Cochain.single_v, ← ht']
    simp
  · rcases lt_or_gt_of_ne hp with hp | hp
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · exact (hpos E p hp).eq_of_src _ _

def clsFun (P : PSh) (s : (free R).obj P ⟶ F) : H R (disc.obj P) F 0 :=
  Classical.choose ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_spec (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (clsFun F P s) :=
  Classical.choose_spec ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_eq (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : clsFun F P s = x :=
  (isCls_basic R F (disc.obj P) 0).2.2.1 s _ _ (clsFun_spec F P s) h

def cls0 (P : PSh) : ((free R).obj P ⟶ F) →+ H R (disc.obj P) F 0 :=
  AddMonoidHom.mk' (clsFun F P) fun s s' =>
    clsFun_eq F P (s + s') _ ((isCls_basic R F (disc.obj P) 0).2.1 s s' _ _ (clsFun_spec F P s) (clsFun_spec F P s'))

theorem degreeZeroClassConstantSpaceAddHom_represents (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (cls0 F P s) :=
  clsFun_spec F P s

theorem degreeZeroClassConstantSpaceAddHom_eq_of_represents (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : cls0 F P s = x :=
  clsFun_eq F P s x h

theorem etaleSpaceCohomologyPullback_degreeZeroClass {P P' : PSh} (f : P ⟶ P') (s : (free R).obj P' ⟶ F) :
    pull R (disc.map f) F 0 (cls0 F P' s) = cls0 F P ((free R).map f ≫ s) :=
  (degreeZeroClassConstantSpaceAddHom_eq_of_represents F P _ _ ((isCls_basic R F (disc.obj P') 0).2.2.2.2 (disc.obj P) (disc.map f) s _ (degreeZeroClassConstantSpaceAddHom_represents F P' s))).symm

theorem degreeZeroClassConstantSpaceAddHom_eq_zero_imp (P : PSh) (s : (free R).obj P ⟶ F) (h : cls0 F P s = 0) : s = 0 :=
  (leray_inj R F (disc.obj P) 0 (fun k m hm hkm _ => by omega)).1 s (h ▸ degreeZeroClassConstantSpaceAddHom_represents F P s)

theorem simplicialSpectralRowDifferential_degreeZeroClass (E : Spc) (p : ℕ) (s : (free R).obj (E.obj (op ⦋p⦌)) ⟶ F) :
    rowD R E F 0 p (cls0 F _ s) = cls0 F _ (cobd s) := by
  simp only [rowD, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, etaleSpaceCohomologyPullback_degreeZeroClass, cobd, map_sum, map_zsmul]

end GlobalTheory.EtC.GmStep.DegRow

open GlobalTheory.EtC.GmStep.DegRow in

theorem GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
    (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
    (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  intro R _ F E hlev htot p y hy
  obtain ⟨s, hs⟩ : ∃ s : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ F, IsCls (E := disc.obj (E.obj (op ⦋p + 1⦌))) (n := 0) s y :=
    exists_rep F (disc.obj (E.obj (op ⦋p + 1⦌))) y
  obtain rfl : cls0 F (E.obj (op ⦋p + 1⦌)) s = y := degreeZeroClassConstantSpaceAddHom_eq_of_represents F _ s y hs
  rw [simplicialSpectralRowDifferential_degreeZeroClass] at hy
  have hc : cobd s = 0 := degreeZeroClassConstantSpaceAddHom_eq_zero_imp F _ _ hy
  obtain ⟨x, hx⟩ := (isCls_basic R F E (p + 1)).1 s hc
  have hx0 : x = 0 := @Subsingleton.elim _ (htot _ (by positivity)) x 0
  rw [hx0] at hx
  obtain ⟨t, ht⟩ := (leray_inj R F E p (fun k m hm _ y => @Subsingleton.elim _ (hlev k m (by exact_mod_cast hm)) y 0)).2 s hx
  exact ⟨cls0 F _ t, by rw [simplicialSpectralRowDifferential_degreeZeroClass, ht]⟩

end
