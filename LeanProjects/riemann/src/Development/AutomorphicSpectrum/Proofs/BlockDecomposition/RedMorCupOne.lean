import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

universe w w' w'' u v u' v' u'' v''

theorem one_cyc {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) :
    (CH.cx (CH.modF A)).d 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem pull_oneH_eq {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R''} {σ' : R' →+* R''} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    {E : C'' ⥤ ModuleCat.{w''} R''} (m : CH.Mor (CH.modF A) E σ) (m' : CH.Mor (CH.modF A') E σ')
    (h : ∀ T : C'', m.τ T (1 : A.obj (m.G.obj T)) = m'.τ T (1 : A'.obj (m'.G.obj T))) :
    m.pull 0 (CH.oneH A) = m'.pull 0 (CH.oneH A') := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0)))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : (CH.cx E).d 0 (m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m.hom.comm, one_cyc, map_zero]
  have c' : (CH.cx E).d 0 (m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m'.hom.comm, one_cyc, map_zero]
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ c).trans (Eq.trans ?_ (CrystallineSemistableComparison.P.mapH_cls m'.hom 0 _ _ c').symm)
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem redMor_mul {O A R Λ : Type} [CommRing O] [CommRing A] [CommRing R] [CommRing Λ] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (T)
    (x y : (B.OM (nlFun δ l X q κ) c).obj ((redMor q s d 𝒱 c lam hc r).G.obj T)) :
    (redMor q s d 𝒱 c lam hc r).τ T ((CH.mulP (B.OA (nlFun δ l X q κ) c)).μ _ x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).μ T ((redMor q s d 𝒱 c lam hc r).τ T x) ((redMor q s d 𝒱 c lam hc r).τ T y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
  refine Subtype.ext ?_
  rfl

theorem redMor_cup_one {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) :
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := by
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (B.OA (nlFun δ l X q κ) c)) (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)))
      (redMor q s d 𝒱 c lam hc r).G (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).τ
      (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).nat (redMor q s d 𝒱 c lam hc r).nat
      (redMor q s d 𝒱 c lam hc r).nat (redMor_mul d q s 𝒱 c lam hc r) h x y
  · exact pull_oneH_eq _ _ (redMor q s d 𝒱 c lam hc r) (toSq (IdF.top _) (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)) fun _ => rfl)
      fun T => Subtype.ext (by
        change Ideal.Quotient.factor (ln_le q s 𝒱 r T) 1 = 1
        exact map_one _)

end GlobalTheory.CompanionTheory.RedCup
