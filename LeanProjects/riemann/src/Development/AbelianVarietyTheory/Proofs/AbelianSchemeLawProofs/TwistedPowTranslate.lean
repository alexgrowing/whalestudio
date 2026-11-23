import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_gen_of_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ (y : Y) J, Good L y J → IsUnit (sval s (𝟙 Y) y J)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul (hs y J hJ))
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem gen_congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hf : FormEq φ ε φ' ε') (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL hf t ht
  exact ⟨t', ht'⟩

theorem gen_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) (h' : ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩

theorem gen_of_pull_top (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (W : Y.Opens) (hW : ∀ y, y ∈ W)
    (c : LB.Gen ((LB.LinComb L φ ε).pull W.ι)) (hc : c.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := Y) W.ι c hc
  let e := IsOpenImmersion.lift W.ι (𝟙 Y)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hW _)
  have he : e ≫ W.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine gen_congr hL ?_ (exists_gen_of_sec hL (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

end Gen

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem gen_square (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (x y : Over.mk t ⟶ P.A) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]), w.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hsq x y (IsLocalRing.closedPoint K)
  refine gen_of_pull_top P.isLB _ (fun z => ?_) c hc
  show (fst (Over.mk t) P.A).left z ∈ V
  rw [spec_pt_eq ((fst (Over.mk t) P.A).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem gen_iter (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (d : Over.mk t ⟶ P.A) :
    ∀ n : ℕ, ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left,
      (translPt P.A (d ^ (n + 1))).left, (translPt P.A d).left] ![(n : ℤ), 1, -((n : ℤ) + 1)]), w.IsGen
  | 0 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_square P t hsq d d) ⟨_, DVR.invGen_isGen _ _ _ _ (gen_square P t hsq d d).choose_spec⟩)
    simp [Fin.sum_univ_succ]
    module
  | n + 1 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_iter hsq d n) (gen_square P t hsq (d ^ (n + 1)) d))
    have e : d ^ (n + 1) * d = d ^ (n + 1 + 1) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

theorem exists_root [IsAlgClosed K] (r : ℕ) [IsFinite (mulA P.A r).left] [Surjective (mulA P.A r).left]
    (c : Over.mk t ⟶ P.A) : ∃ d : Over.mk t ⟶ P.A, d ^ r = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A r).left c.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ (mulA P.A r).left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb']; exact Over.w c
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.TwistTranslate

namespace GlobalTheory

theorem twisted_pow_translate :
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen := by
  intro hsq hmul S _ P K _ _ t q hq c
  obtain ⟨hfin, -, hsurj, -⟩ := hmul S P q hq
  obtain ⟨d, rfl⟩ := TwistTranslate.exists_root P t q c
  refine ⟨d, rfl, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine TwistTranslate.gen_congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_)
    (TwistTranslate.gen_iter P t (hsq S P _) d n)
  simp [Fin.sum_univ_succ]

end GlobalTheory
