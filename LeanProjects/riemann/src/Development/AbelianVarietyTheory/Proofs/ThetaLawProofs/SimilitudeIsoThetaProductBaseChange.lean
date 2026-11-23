import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyRow

theorem comb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (ψ : T'.left ⟶ T.left)
    (hψ : ψ ≫ T.hom = T'.hom ≫ f) {n : ℕ} (p : Fin n → (T ⟶ G)) (p' : Fin n → (T' ⟶ G'))
    (hp : ∀ c, (p' c).left ≫ φ = ψ ≫ (p c).left) (a : Fin n → ℤ) (ξ : 𝟙_ (Over S) ⟶ G) (ξ' : 𝟙_ (Over S') ⟶ G')
    (hξ : ξ'.left ≫ φ = f ≫ ξ.left) :
    ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')).left ≫ φ =
      ψ ≫ ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk ψ hψ
  have e₁ : ∀ c, pushHom h T' (p' c) = preHom U (p c) := fun c => Over.OverMorphism.ext (hp c)
  have t : ∀ {B : Scheme.{0}} (V : Over B), (toUnit V).left = V.hom := fun V =>
    (Category.comp_id _).symm.trans (Over.w (toUnit V))
  have e₂ : pushHom h T' (toUnit _ ≫ ξ') = preHom U (toUnit _ ≫ ξ) := Over.OverMorphism.ext (by
    show ((toUnit T').left ≫ ξ'.left) ≫ φ = ψ ≫ (toUnit T).left ≫ ξ.left
    rw [Category.assoc, hξ, t, t]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.left) hψ.symm).trans (Category.assoc _ _ _)))
  have e : pushHom h T' ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')) =
      preHom U ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)) := by
    rw [map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, e₂]
    congr 3
    funext c
    simp only [Function.comp_apply, map_zpow, e₁]
  exact congrArg (fun z => z.left) e

theorem cancel_units {A K κ : Type} [CommRing A] [Fintype K] [Fintype κ] [DecidableEq κ] {N m : ℕ} (s : K → Aˣ)
    (t : κ → Aˣ) (v : Aˣ) (x : K → A) (c : (κ → Fin N) → A) (y : κ → Fin N → A)
    (h : ∏ r, (s r ^ 1).val * x r = (((∏ r, s r ^ (1 : ℤ)) * ∏ k, t k ^ (-(m : ℤ))) * v).val *
      ∑ I, c I * ∏ k, (t k ^ m).val * y k (I k)) :
    ∏ r, x r = v.val * ∑ I, c I * ∏ k, y k (I k) := by
  simp only [pow_one, zpow_one, zpow_neg, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    ← Units.coe_prod, mul_left_comm _ (∏ k, t k ^ m).val, ← Finset.mul_sum] at h
  refine (Units.mul_right_inj (∏ r, s r)).1 (h.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_comm (∏ k, t k ^ m), mul_right_comm, inv_mul_cancel_right]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  rintro R R' _ _ x x' f φ u m N al b b' ξ ξ' w q ⟨he, hg, F, hφ, hu, -, hth, -⟩ hb hξ hw H
  obtain ⟨ψ, hψ, hc⟩ := KeyPow.exists_isGrpPullback_pow hφ (Out.powIsPowGrp x.P.A 4) (Out.powIsPowGrp x'.P.A 4)
  have hc' : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left := hc
  have ha : ∀ r, (alMap x' al r (ξ' r)).left ≫ φ = ψ ≫ (alMap x al r (ξ r)).left := fun r =>
    comb_push hφ ψ hψ.1.w _ _ hc' (al r) (ξ r) (ξ' r) (hξ r)
  obtain ⟨w', hw', P⟩ := H1.exists_gen_move x.P.isLB x'.P.isLB u ((isGen_iff u).1 hu) _
    (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) _ ψ
    (by rintro (r | c); exacts [ha r, hc' c]) w hw
  refine ⟨w', hw', fun Z ρ z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z ⟶ x.P.A.left => exists_chart x.P.isLB (χ z)
  have ha' : ∀ r, (ρ ≫ ψ) ≫ (alMap x al r (ξ r)).left = (ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, ha]
  have hc'' : ∀ c : Fin 4, (ρ ≫ ψ) ≫ (Out.powPr x.P.A c).left = (ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, hc']
  have E := H Z (ρ ≫ ψ) z J hJ
  have hv := (val_of w (ρ ≫ ψ) z J (fun k => J ((ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k) ≫ φ)) (by rintro (r | c); exacts [congrArg J (ha' r), congrArg J (hc'' c)])).trans
    (P Z ρ z _ (fun k => J' (ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k)) (fun k => hJ _) (fun k => hJ' _))
  rw [Fintype.prod_sum_type] at hv
  have hth' : KeyVia.Via u 1 x'.th.f x.th.f := fun j i h => (hth j i h).trans (by rw [pow_one])
  have hq : ∀ a : R, gs (ρ ≫ ψ) z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ a) =
      gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f a)) := fun a =>
    (gs_appLE ψ ⊤ ⊤ le_top ρ z trivial _).symm.trans
      (congrArg (gs ρ z ⊤) (KeyVia.appLE_cst f _ _ hψ.1.w le_top a))
  rw [hv] at E
  refine cancel_units (m := m)
    (fun r => gw u (ρ ≫ (alMap x' al r (ξ' r)).left) z (J ((ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ))
      (J' (ρ ≫ (alMap x' al r (ξ' r)).left)))
    (fun c => gw u (ρ ≫ (Out.powPr x'.P.A c).left) z (J ((ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ))
      (J' (ρ ≫ (Out.powPr x'.P.A c).left))) _ _ _
    (fun c k => gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J' (ρ ≫ (Out.powPr x'.P.A c).left)))
      ((b' k).f (J' (ρ ≫ (Out.powPr x'.P.A c).left)))) ?_
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) (E.trans (congrArg₂ (· * ·) rfl
    (Finset.sum_congr rfl fun I _ => congrArg₂ (· * ·) (hq _) (Finset.prod_congr rfl fun c _ => ?_))))
  · rw [ha']
    exact (KeyBasis.via_val hth' _ z (hJ _) (hJ' _)).symm
  · rw [hc'']
    exact KeyBasis.via_val (w := u) (hb (I c)) _ z (hJ _) (hJ' _)

end GlobalTheory.KeyRow
end
