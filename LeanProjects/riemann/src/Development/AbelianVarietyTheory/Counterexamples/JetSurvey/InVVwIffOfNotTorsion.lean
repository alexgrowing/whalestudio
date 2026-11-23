import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PowEqOneOfLocalLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsDimOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FunEqZeroOfAffine

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.WeightProbe
variable {S : Scheme.{0}}

theorem pow_eq_one_of_section {A : Over S} [GrpObj A] {T T' : Over S} (u : T' ⟶ T) (v : T ⟶ T')
    (e : v ≫ u = 𝟙 T) (x : T ⟶ A) (N : ℕ) (h : (u ≫ x) ^ N = 1) : x ^ N = 1 := by
  have := congrArg (v ≫ ·) h
  simp only [MonObj.comp_pow, MonObj.comp_one] at this
  rwa [← Category.assoc, e, Category.id_comp] at this

theorem exists_section_top (T : Over S) : ∃ v : T ⟶ overRes (⊤ : T.left.Opens), v ≫ overResι ⊤ = 𝟙 T :=
  ⟨Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩

theorem inVVw_iff_of_not_torsion (P : PolAV S) (N m : ℕ) {T : Over S} {I : Type} (h : I → (T ⟶ P.A))
    (hh : ∀ i, h i ^ N ≠ 1) (χ : I → Γ(T.left, ⊤)ˣ) (s : LB.Sec (LPow P.A P.L N T)) :
    InVVw P N m h χ s ↔ Odd N ∧ IsUnit (N : Γ(T.left, ⊤)) ∧ InVV P N m s := by
  refine ⟨fun H => ⟨H.1, H.2.1, H.2.2.1⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, fun p => ⟨⊤, trivial, _,
    VVRank.isPullSec_pullS P.A N (overResι ⊤) s, fun i U s' hU _ => ?_⟩⟩⟩
  obtain ⟨v, e⟩ := exists_section_top T
  exact absurd (pow_eq_one_of_section _ v e (h i) N
    (hU.pt_eq ▸ PairingLawsCompare.theta_pt_pow P N U)) (hh i)

theorem exists_every_weight : ∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ P.A) (s : LB.Sec (LPow P.A P.L (3 ^ 2 : ℕ) T)), P.g = 1 ∧ Nonempty T.left ∧ s.f ≠ 0 ∧
      (∀ χ : Γ(T.left, ⊤)ˣ, InVVw P (3 ^ 2) 3 (fun _ : Unit => x) (fun _ => χ) s) ∧
      ∀ χ : Γ(T.left, ⊤)ˣ, ¬ InVVw' P (3 ^ 2) 3 (fun _ : Unit => x) (fun _ => χ) s := by
  obtain ⟨P, hP⟩ := MulLawTest.exists_dim_one
  have hc := (MulLawTest.mulN _ P 2 (by norm_num)).2.2.2.2 ℂ (𝟙 _) (by norm_num)
  rw [hP] at hc
  have hf : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hn : Nontrivial {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1} :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  obtain ⟨⟨x, hx⟩, hne⟩ := exists_ne (⟨1, one_pow 2⟩ :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1})
  have hx9 : x ^ (3 ^ 2) ≠ 1 := fun e => hne (Subtype.ext (by
    have : x ^ (3 ^ 2) = (x ^ 2) ^ 4 * x := by rw [← pow_mul, ← pow_succ]; rfl
    rwa [this, hx, one_pow, _root_.one_mul] at e))
  have hz := Complex.isPrimitiveRoot_exp (3 ^ 2) (by norm_num)
  have hlev := GlobalTheory.nonempty_level_of_isAlgClosed ℂ P (3 ^ 2) (hz.isUnit (by norm_num)).unit (by norm_num)
    (hz.isUnit_unit (by norm_num))
  have hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : Γ(Spec (CommRingCat.of ℂ), ⊤))) := fun n h0 => by
    have := (IsUnit.mk0 (n : ℂ) (by exact_mod_cast h0)).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  let p : (baseOver (Spec (CommRingCat.of ℂ))).left := (⊥ : PrimeSpectrum ℂ)
  obtain ⟨V, hp, -, -, hr⟩ := GlobalTheory.abelianSchemeLaws_all.1.vvRank _ P 3 _ (by decide) (hu 3 (by norm_num)) hlev
    (baseOver _) p
  have hsub : Subsingleton (baseOver (Spec (CommRingCat.of ℂ))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨v, e⟩ := GlobalLift.exists_section hp
  have hy : (overResι V ≫ x) ^ (3 ^ 2) ≠ 1 := fun h => hx9 (pow_eq_one_of_section _ v e x _ h)
  have hb : VVsub P (3 ^ 2) 3 (overRes V) ≠ ⊥ := fun h => by
    have hne : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨p, hp⟩, trivial⟩⟩
    have hnt : Nontrivial Γ((overRes V).left, ⊤) := Scheme.component_nontrivial V.toScheme ⊤
    rw [h, finrank_bot, hP] at hr; norm_num at hr
  have : ∃ f, (∃ h : f ∈ SecM P.A P.L (3 ^ 2 : ℕ) (overRes V), InVV P (3 ^ 2) 3 (SecM.toSec P.A ⟨f, h⟩)) ∧ f ≠ 0 := by
    by_contra H
    push Not at H
    exact hb (Submodule.span_eq_bot.2 H)
  obtain ⟨f, ⟨hf, hs⟩, h0⟩ := this
  refine ⟨P, overRes V, overResι V ≫ x, SecM.toSec P.A ⟨f, hf⟩, hP, ⟨⟨p, hp⟩⟩, h0, fun χ => ?_,
    fun χ H => hy (H.2.2.1 ())⟩
  refine (inVVw_iff_of_not_torsion P _ _ _ (fun _ => hy) _ _).2 ⟨by decide, ?_, hs⟩
  have := (hu (3 ^ 2) (by norm_num)).map (overRes V).hom.appTop.hom
  rwa [map_natCast] at this

theorem exists_symLift_top (P : PolAV S) {N : ℕ} (hN : Odd N) {T : Over S} (x : T ⟶ P.A) (hx : x ^ N = 1) :
    ∃ U : ThetaGrp P.A P.L N T, SymLift P.A P.L N N x U := by
  have g := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have lft := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
  have neg := GlobalTheory.exists_gen_negLB g
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local g P.isAb P.isLB hN
    ((GlobalTheory.symLift_odd g lft neg).1 S P N hN T x hx).1
  obtain ⟨nu, hnu⟩ := neg S P N T
  exact SymLiftOdd.exists_symLift g P.isAb P.isLB hN hx θ hθ hnu

open GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank VVCompare CommPairing in

theorem act_pull (P : PolAV S) {N : ℕ} (hN : Odd N) {T T' : Over S} (u : T' ⟶ T) {x : T ⟶ P.A}
    {θ : ThetaGrp P.A P.L N T} {θ' : ThetaGrp P.A P.L N T'} (H : SymLift P.A P.L N N x θ)
    (H' : SymLift P.A P.L N N (u ≫ x) θ') {s t : LB.Sec (LPow P.A P.L N T)} (a : IsActOf P.A P.L N θ s t) :
    IsActOf P.A P.L N θ' (pullS P.A N u s) (pullS P.A N u t) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val P.isLB u H
  have c := SymLiftOdd.symLift_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns P.isAb P.isLB hN θ' ξ H' Hξ
  refine VVCompare.isTwistPull_of_sv P.A P.isLB θ'.isGen fun y J hJ => ?_
  have e : tval θ' (𝟙 _) y J = tval θ (𝟙 _ ≫ (u ▷ P.A).left) y J := (val_corr hJ c _).trans (v _ _ y J hJ)
  have e' : (𝟙 _ ≫ (translT P.A θ'.pt).left) ≫ (u ▷ P.A).left =
      (𝟙 _ ≫ (u ▷ P.A).left) ≫ (translT P.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  rw [VVCompare.sv_pullS P.A _ u t _ y hJ, VVCompare.sv_pullS P.A _ u s _ y hJ, e']
  exact (VVCompare.sv_of_isTwistPull P.A a _ y hJ).trans (congrArg (fun q => Units.val q * _) e.symm)

end GlobalTheory.WeightProbe
