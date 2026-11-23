import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilBaseChange

section Val

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem good_comp {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (σ : Z ⟶ Y) :
    Good L (σ z) (fun χ => J (σ ≫ χ)) := fun χ => hJ (σ ≫ χ)

theorem val_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Y' ⟶ Y) (σ : Z ⟶ Y') {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Units.map (σ.stalkMap z).hom.toMonoidHom (val t r (σ z) (fun χ => J (σ ≫ χ))) = val t (σ ≫ r) z J := by
  have hm := (good_comp hJ σ).mem φ r
  rw [val_of t (σ ≫ r) z J (fun k => J (σ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  refine Units.ext ?_
  exact (congrArg (σ.stalkMap z).hom (gs_unit r (σ z) _ hm _).symm).trans
    ((RelBasis.gs_comp σ r z _ hm _).symm.trans (gs_unit (σ ≫ r) z _ hm _))

theorem val_move {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' :=
  (val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by
    rw [Category.assoc, Category.assoc, hψ])).trans
    (H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k)))

end Val

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pow_push (h : IsGrpPullback G' G f φ) (m : ℕ) : ((𝟙 G') ^ m).left ≫ φ = φ ≫ ((𝟙 G) ^ m).left := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e₁ : pushHom h G' (𝟙 G') = preHom U (𝟙 G) :=
    Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have e : pushHom h G' ((𝟙 G') ^ m) = preHom U ((𝟙 G) ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e

theorem eSec_push (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem prod_eq_one (h : IsGrpPullback G' G f φ) {n : ℕ} (ξ : Fin n → (𝟙_ (Over S) ⟶ G))
    (ξ' : Fin n → (𝟙_ (Over S') ⟶ G')) (hξ : ∀ r, (ξ' r).left ≫ φ = f ≫ (ξ r).left) (a : Fin n → ℤ)
    (H : (List.ofFn fun r => ξ r ^ a r).prod = 1) : (List.ofFn fun r => ξ' r ^ a r).prod = 1 := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id f).trans (Category.id_comp f).symm)
  have e₁ : ∀ r, pushHom h _ (ξ' r) = preHom U (ξ r) := fun r => Over.OverMorphism.ext (hξ r)
  have e : pushHom h _ (List.ofFn fun r => ξ' r ^ a r).prod = preHom U (List.ofFn fun r => ξ r ^ a r).prod := by
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext c
    simp only [Function.comp_apply, map_zpow, e₁]
  rw [H, map_one, ← map_one (pushHom h (𝟙_ (Over S')))] at e
  refine Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ?_)
  rw [Over.w, Over.w]

end Grp

variable {R : Type} [CommRing R]

theorem eSec_powPr (x : KeyIn R) (c : Fin 4) :
    eSec (Out.powObj x.P.A 4) ≫ (Out.powPr x.P.A c).left = eSec x.P.A :=
  congrArg CommaMorphism.left (IsMonHom.one_hom (Out.powPr x.P.A c))

theorem eSec_alMap (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4) (ξ : Pt x) :
    eSec (Out.powObj x.P.A 4) ≫ (alMap x al r ξ).left = ξ.left := by
  have h1 : ∀ c : Fin 4, η[Out.powObj x.P.A 4] ≫ Out.powPr x.P.A c = 1 := fun c => by
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
  have : η[Out.powObj x.P.A 4] ≫ alMap x al r ξ = ξ := by
    simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
      MonObj.comp_one, h1, one_zpow, _root_.one_mul]
    rw [← Category.assoc, toUnit_unique (η[_] ≫ toUnit _) (𝟙 _), Category.id_comp]
  exact congrArg CommaMorphism.left this

theorem comp_pow_of_pow_eq_one (x : KeyIn R) {m : ℕ} (ξ : Pt x) (h : ξ ^ m = 1) :
    ξ.left ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A := by
  have : ξ ≫ (𝟙 x.P.A) ^ m = η[x.P.A] := by
    rw [MonObj.comp_pow, Category.comp_id, h, Hom.one_def, toUnit_unit, Category.id_comp]
  exact congrArg CommaMorphism.left this

theorem eSec_pow (x : KeyIn R) (m : ℕ) : eSec x.P.A ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A :=
  comp_pow_of_pow_eq_one x η[x.P.A] (by
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ x.P.A) = η[x.P.A] := by rw [Hom.one_def]; simp
    rw [← e₁, one_pow])

theorem cancel_mu {U : Type} [CommGroup U] (m : ℕ) (e a b : U)
    (h : (e ^ (1 : ℤ) * e ^ (-(m : ℤ) ^ 2)) * a = (e ^ (1 : ℤ) * b) ^ (1 - (m : ℤ) ^ 2)) :
    a = b ^ (1 - (m : ℤ) ^ 2) := by
  rw [mul_zpow, ← zpow_add, ← zpow_mul, _root_.one_mul, ← sub_eq_add_neg] at h
  exact mul_left_cancel h

theorem cancel_rho {A : Type} [CommRing A] (m : ℕ) (e a b : Aˣ) (s v : Fin 4 → Aˣ) (c : A)
    (h : ((((∏ r, s r ^ (1 : ℤ)) * ∏ _c : Fin 4, e ^ (-(m : ℤ))) * a) ^ (m ^ 2) *
      ∏ r, ((e ^ (1 : ℤ) * s r ^ (-(m : ℤ) ^ 2)) * v r)).val = c * ((e ^ (1 : ℤ) * b) ^ (4 - 4 * (m : ℤ) ^ 3)).val) :
    (a ^ (m ^ 2) * ∏ r, v r).val = c * (b ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  have e₁ : (((∏ r, s r ^ (1 : ℤ)) * ∏ _c : Fin 4, e ^ (-(m : ℤ))) * a) ^ (m ^ 2) *
      ∏ r, ((e ^ (1 : ℤ) * s r ^ (-(m : ℤ) ^ 2)) * v r) = e ^ (4 - 4 * (m : ℤ) ^ 3) * (a ^ (m ^ 2) * ∏ r, v r) := by
    simp only [zpow_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_zpow]
    generalize (∏ r, s r) = p
    generalize (∏ r, v r) = q
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
    module
  rw [e₁, zpow_one, mul_zpow, Units.val_mul, Units.val_mul (e ^ _), mul_left_comm] at h
  exact (Units.mul_right_inj _).1 h

theorem row_move {R' : Type} [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ u} {m N : ℕ}
    {al : Matrix (Fin 4) (Fin 4) ℤ} {b : Fin N → RR x m} {b' : Fin N → RR x' m} {ξ : Fin 4 → Pt x} {ξ' : Fin 4 → Pt x'}
    {w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left)
      (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))}
    {w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
      (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))}
    (q : (Fin 4 → Fin N) → R) (hth : KeyVia.Via u 1 x'.th.f x.th.f) (hb : ∀ k, SecVia x' x φ u (b' k) (b k))
    {ψ : (Out.powObj x'.P.A 4).left ⟶ (Out.powObj x.P.A 4).left}
    (hψ : ψ ≫ (Out.powObj x.P.A 4).hom = (Out.powObj x'.P.A 4).hom ≫ spMap f)
    (hc : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left)
    (ha : ∀ r, (alMap x' al r (ξ' r)).left ≫ φ = ψ ≫ (alMap x al r (ξ r)).left)
    (P : PMaps u _ _ _ w' w ψ)
    (H : ∀ (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J →
      ∏ r, gs (alMap x al r (ξ r)).left y _ (x.th.f (J (alMap x al r (ξ r)).left)) =
        (val w (𝟙 _) y J).val * ∑ I' : Fin 4 → Fin N, gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) *
          ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left))
            ((b (I' c)).f (J (Out.powPr x.P.A c).left)))
    (z : (Out.powObj x'.P.A 4).left) (J') (hJ' : Good x'.P.L z J') :
    ∏ r, gs (alMap x' al r (ξ' r)).left z _ (x'.th.f (J' (alMap x' al r (ξ' r)).left)) =
      (val w' (𝟙 _) z J').val * ∑ I' : Fin 4 → Fin N, gs (𝟙 _) z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) *
        ∏ c, gs (Out.powPr x'.P.A c).left z (x'.P.L.U (J' (Out.powPr x'.P.A c).left))
          ((b' (I' c)).f (J' (Out.powPr x'.P.A c).left)) := by
  choose J hJ using fun χ : (Out.powObj x'.P.A 4).left ⟶ x.P.A.left => exists_chart x.P.isLB (χ z)
  have E := congrArg (ψ.stalkMap z).hom (H (ψ z) _ (good_comp hJ ψ))
  rw [map_prod, map_mul, map_sum] at E
  have hv := (val_comp w (𝟙 _) ψ hJ).trans ((congrArg (fun r => val w r z J)
    ((Category.comp_id ψ).trans (Category.id_comp ψ).symm)).trans
    (val_move (by rintro (r | c); exacts [ha r, hc c]) P (𝟙 _) z hJ hJ'))
  rw [Fintype.prod_sum_type] at hv
  simp only [Category.id_comp, Sum.elim_inl, Sum.elim_inr] at hv
  have hq : ∀ a : R, (ψ.stalkMap z).hom (gs (𝟙 _) (ψ z) ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ a)) =
      gs (𝟙 _) z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f a)) := fun a =>
    (RelBasis.gs_comp ψ (𝟙 _) z ⊤ trivial _).symm.trans ((congrArg (fun r => gs r z ⊤ _)
      ((Category.comp_id ψ).trans (Category.id_comp ψ).symm)).trans
      ((gs_appLE ψ ⊤ ⊤ le_top (𝟙 _) z trivial _).symm.trans
      (congrArg (gs (𝟙 _) z ⊤) (KeyVia.appLE_cst f _ _ hψ le_top a))))
  refine KeyRow.cancel_units (m := m)
    (fun r => gw u (alMap x' al r (ξ' r)).left z (J ((alMap x' al r (ξ' r)).left ≫ φ))
      (J' (alMap x' al r (ξ' r)).left))
    (fun c => gw u (Out.powPr x'.P.A c).left z (J ((Out.powPr x'.P.A c).left ≫ φ))
      (J' (Out.powPr x'.P.A c).left)) _ _ _
    (fun c k => gs (Out.powPr x'.P.A c).left z (x'.P.L.U (J' (Out.powPr x'.P.A c).left))
      ((b' k).f (J' (Out.powPr x'.P.A c).left))) ?_
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) (E.trans (congrArg₂ (· * ·) (congrArg Units.val hv)
    (Finset.sum_congr rfl fun I _ => ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hq _) ((map_prod _ _ _).trans
      (Finset.prod_congr rfl fun c _ => ?_)))))))
  · refine Eq.trans ?_ (RelBasis.gs_comp ψ _ z _ (hJ (ψ ≫ _)) _)
    rw [← ha]
    exact (KeyBasis.via_val hth _ z (hJ _) (hJ' _)).symm
  · refine Eq.trans (RelBasis.gs_comp ψ _ z _ (hJ (ψ ≫ _)) _).symm ?_
    rw [← hc]
    exact KeyBasis.via_val (w := u) (hb (I c)) _ z (hJ _) (hJ' _)

def CmpVal (x : KeyIn R) (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (lam : Rˣ) : Prop :=
  ∃ (ξ : (Fin 4 → Fin N) → Fin 4 → Pt x)
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]))
    (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left))
      (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (Q : Matrix (Fin 4 → Fin N) (Fin 4 → Fin N) R) (rho : (Fin 4 → Fin N) → Rˣ),
    (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧
    (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) ∧
    mu.IsGen ∧ (∀ I, (w I).IsGen) ∧
    (∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J →
      val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) ∧
      ∀ I, (val (w I) (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ I r).left p J).val =
        gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ (rho I)) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val) ∧
    (∀ I (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J →
      ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) =
        (val (w I) (𝟙 _) y J).val * ∑ I', gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) *
          ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left))) ∧
    (lam : R) = Q.det ^ (2 * m ^ 2) * ∏ I, (rho I : R) ^ 2

theorem cmpVal_baseChange {R' : Type} [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ u} {m N N' : ℕ}
    {al : Matrix (Fin 4) (Fin 4) ℤ} (hN : N' = N) (hm : N ≠ 0 → m ≠ 0) {b : Fin N → RR x m} {b' : Fin N' → RR x' m}
    {lam : Rˣ} (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hx : KeyVia x' x f φ u)
    (hb : ∀ k, SecVia x' x φ u (b' k) (b (k.cast hN))) (H : CmpVal x m N al b lam) :
    CmpVal x' m N' al b' (Units.map f.toMonoidHom lam) := by
  subst hN
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, hmu, hw, h₃, h₄, h₅⟩ := H
  choose ξ' hξ using fun I r => (((KeyVia.main R R' x x' f).2 φ u hx).2.1 (ξ I r)).exists
  obtain ⟨he, hg, F, hφ, hu, hrig, hth, -⟩ := hx
  have hu' := (isGen_iff u).1 hu
  obtain ⟨ψ, hψ, hc⟩ := KeyPow.exists_isGrpPullback_pow hφ (Out.powIsPowGrp x.P.A 4) (Out.powIsPowGrp x'.P.A 4)
  have hc' : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left := hc
  have ha : ∀ I r, (alMap x' al r (ξ' I r)).left ≫ φ = ψ ≫ (alMap x al r (ξ I r)).left := fun I r =>
    KeyRow.comb_push hφ ψ hψ.1.w _ _ hc' (al r) (ξ I r) (ξ' I r) (hξ I r)
  have hwc : ∀ I k, Sum.elim (fun r => (alMap x' al r (ξ' I r)).left) (fun c => (Out.powPr x'.P.A c).left) k ≫ φ =
      ψ ≫ Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left) k := by
    rintro I (r | c); exacts [ha I r, hc' c]
  choose w' hw' P using fun I => H1.exists_gen_move x.P.isLB x'.P.isLB u hu' _ _ _ ψ (hwc I) (w I) (hw I)
  have hmc : ∀ k : Fin 2, ![((𝟙 x'.P.A) ^ m).left, 𝟙 x'.P.A.left] k ≫ φ =
      φ ≫ ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] k :=
    Fin.forall_fin_two.2 ⟨pow_push hφ m, (Category.id_comp φ).trans (Category.comp_id φ).symm⟩
  obtain ⟨mu', hmu', Pm⟩ := H1.exists_gen_move x.P.isLB x'.P.isLB u hu' _ _ _ φ hmc mu hmu
  have Pr : PMaps u (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => eSec x.P.A) (fun _ => 1) x'.rig x.rig (spMap f) :=
    (maps_iff u _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
      (fun _ => rfl)).1 hrig
  have h₂' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1 := fun I c =>
    prod_eq_one hφ (ξ I) (ξ' I) (hξ I) (fun r => al r c) (h₂ I c)
  refine ⟨ξ', mu', w', Q.map f, fun I => Units.map f.toMonoidHom (rho I), fun I I' hI p => ?_, h₂', hmu', hw',
    fun p J' hJ' => ?_, fun I => row_move (Q I) (fun j i h => (hth j i h).trans (by rw [pow_one])) hb hψ.1.w hc'
      (ha I) (P I) (h₄ I), ?_⟩
  · obtain ⟨r, hr⟩ := h₁ I I' hI (spMap f p)
    refine ⟨r, fun e => hr ?_⟩
    exact (congrArg (fun g => g p) (hξ I r)).symm.trans ((congrArg φ e).trans (congrArg (fun g => g p) (hξ I' r)))
  · let σ : (𝟙_ (Over (Sp R'))).left ⟶ (𝟙_ (Over (Sp R))).left := spMap f
    choose J hJ using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ x.P.A.left => exists_chart x.P.isLB (χ p)
    obtain ⟨E₁, E₂⟩ := h₃ (σ p) _ (good_comp hJ σ)
    let W := fun χ : (𝟙_ (Over (Sp R'))).left ⟶ x'.P.A.left => gw u χ p (J (χ ≫ φ)) (J' χ)
    let T := Units.map (σ.stalkMap p).hom.toMonoidHom
    have vr : T (val x.rig (𝟙 _) (σ p) (fun χ => J (σ ≫ χ))) = W (eSec x'.P.A) ^ (1 : ℤ) * val x'.rig (𝟙 _) p J' := by
      refine (val_comp x.rig (𝟙 _) σ hJ).trans ((congrArg (fun r => val x.rig r p J)
        ((Category.comp_id σ).trans (Category.id_comp σ).symm)).trans
        ((val_move (fun _ => he) Pr (𝟙 _) p hJ hJ').trans ?_))
      rw [Fintype.prod_unique, Category.id_comp]
    have vm : ∀ (ζ : Pt x) (ζ' : Pt x'), ζ'.left ≫ φ = σ ≫ ζ.left → ζ'.left ≫ ((𝟙 x'.P.A) ^ m).left = eSec x'.P.A →
        T (val mu ζ.left (σ p) (fun χ => J (σ ≫ χ))) =
          (W (eSec x'.P.A) ^ (1 : ℤ) * W ζ'.left ^ (-(m : ℤ) ^ 2)) * val mu' ζ'.left p J' := fun ζ ζ' e e' => by
      refine (val_comp mu ζ.left σ hJ).trans ((congrArg (fun r => val mu r p J) e.symm).trans
        ((val_move hmc Pm ζ'.left p hJ hJ').trans ?_))
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e', W]
    refine ⟨?_, fun I => ?_⟩
    · have E := congrArg T E₁
      rw [map_zpow, vr] at E
      exact cancel_mu m _ _ _ ((vm η[x.P.A] η[x'.P.A] he (eSec_pow x' m)).symm.trans E)
    · haveI := x'.P.isAb.comm
      have hm' : m ≠ 0 := hm (fun h => by subst h; exact (I 0).elim0)
      have hk : ∀ r, ξ' I r ^ m = 1 := SimilUnit.pow_eq_one_of_similitude m hm' al hal (ξ' I) fun c => by
        simpa only [List.prod_ofFn] using h₂' I c
      have vw : T (val (w I) (eSec (Out.powObj x.P.A 4)) (σ p) (fun χ => J (σ ≫ χ))) =
          ((∏ r, W (ξ' I r).left ^ (1 : ℤ)) * ∏ _c : Fin 4, W (eSec x'.P.A) ^ (-(m : ℤ))) *
            val (w' I) (eSec (Out.powObj x'.P.A 4)) p J' := by
        refine (val_comp (w I) _ σ hJ).trans ((congrArg (fun r => val (w I) r p J) (eSec_push hψ).symm).trans
          ((val_move (hwc I) (P I) _ p hJ hJ').trans ?_))
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, eSec_alMap, eSec_powPr, W]
      have hq : (σ.stalkMap p).hom (gs (𝟙_ (Over (Sp R))).hom (σ p) ⊤ (cst (𝟙 (Sp R)) ⊤ (rho I))) =
          gs (𝟙_ (Over (Sp R'))).hom p ⊤ (cst (𝟙 (Sp R')) ⊤ (f (rho I))) :=
        (RelBasis.gs_comp σ _ p ⊤ trivial _).symm.trans ((congrArg (fun r => gs r p ⊤ _)
          ((Category.comp_id σ).trans (Category.id_comp σ).symm)).trans
          ((gs_appLE σ ⊤ ⊤ le_top (𝟙 _) p trivial _).symm.trans
          (congrArg (gs (𝟙 _) p ⊤) (KeyVia.appLE_cst f (𝟙 (Sp R)) (𝟙 (Sp R'))
            ((Category.comp_id σ).trans (Category.id_comp σ).symm) le_top _))))
      refine cancel_rho m (W (eSec x'.P.A)) _ _ (fun r => W (ξ' I r).left) _ _ ?_
      have E := (congrArg (σ.stalkMap p).hom (E₂ I)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hq rfl))
      refine Eq.trans (congrArg Units.val (Eq.symm (?_ : T (val (w I) (eSec (Out.powObj x.P.A 4)) (σ p)
        (fun χ => J (σ ≫ χ)) ^ (m ^ 2) * ∏ r, val mu (ξ I r).left (σ p) (fun χ => J (σ ≫ χ))) = _))) (E.trans (congrArg _ (congrArg Units.val
        ((map_zpow T _ _).trans (congrArg (· ^ _) vr)))))
      refine (map_mul T _ _).trans (congrArg₂ (· * ·) ((map_pow T _ _).trans (congrArg (· ^ _) vw))
        ((map_prod T _ _).trans (Finset.prod_congr rfl fun r _ => ?_)))
      exact vm _ _ (hξ I r) (comp_pow_of_pow_eq_one x' _ (hk r))
  · show f lam = _
    rw [h₅, map_mul, map_pow, map_prod, RingHom.map_det]
    simp only [map_pow]
    rfl

theorem cmpVal_baseChange_similitude : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (b : Fin (m ^ x.P.g) → RR x m) (b' : Fin (m ^ x'.P.g) → RR x' m) (lam : Rˣ), al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b (k.cast (by rw [hg])))) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x' m al b' (Units.map f.toMonoidHom lam) := by
  intro R R' _ _ x x' f φ w m al hg b b' lam hal hx hb H
  exact cmpVal_baseChange (by rw [hg]) (fun h h0 => h (by
    have := x.g_pos
    rw [h0, zero_pow (by omega)])) hal hx hb H

end GlobalTheory.SimilBaseChange
end
