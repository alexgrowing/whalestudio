import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtVec

open ReciprocityTheory.ChartRestriction.G.DVR

section Local

variable {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_cpt (hM : M.IsLB) {φ : K → (Sp S ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp S ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) {J} (hJ : Good M (cpt S) J) (e : val t (𝟙 _) (cpt S) J = val t' (𝟙 _) (cpt S) J) :
    LB.Gen.Corr M _ _ _ _ t t' := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM hF t' ht'
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio hM rfl t u ht hu
  have h1 : Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ ρ = 1 :=
    mul_eq_right.1 ((hρ _ _ _ J hJ).symm.trans (e.trans (vu _ _ _ J hJ).symm))
  have h2 : ρ = 1 := by
    apply Units.ext
    obtain ⟨a, ha⟩ := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective ρ.val
    have h3 : toStkA (cpt S) a = toStkA (cpt S) 1 := by
      rw [map_one]
      refine Eq.trans ?_ (congrArg Units.val h1)
      rw [gm_val (𝟙 (Sp S)) (cpt S) ⊤ trivial, ← ha]
      rfl
    rw [← ha, toStkA_injective h3, map_one]; rfl
  refine corr_of_val hM fun y I hI => (hρ _ _ y I hI).trans ?_
  rw [h2, map_one, _root_.one_mul]
  exact vu _ _ y I hI

theorem exists_gen_cpt (hM : M.IsLB) (φ : K → (Sp S ⟶ X)) (ε : K → ℤ) {J} (hJ : Good M (cpt S) J)
    (u : ((Sp S).presheaf.stalk (cpt S))ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) (cpt S) J = u := by
  have all : ∀ w : Sp S, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_cpt (𝟙 (Sp S)) _).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) :=
    fun j w hw => ⟨hw, all w⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(Sp S, ⊤)ˣ, Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ c = u := by
    obtain ⟨U, hU, a, ha⟩ := (Sp S).presheaf.exists_germ_eq u.val
    obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) U).2 hU)
    have hb : (Sp S).basicOpen a = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) _).2
      (((Sp S).mem_basicOpen a _ hU).2 (ha ▸ u.isUnit)))
    have ha' : IsUnit a := (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      ((Sp S).mem_basicOpen a y hy).1 (hb.ge trivial)
    exact ⟨ha'.unit, Units.ext ((gm_val (𝟙 _) _ ⊤ trivial _).trans ha)⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) * res le_top c⟩
  have v : ∀ (w : Sp S) j, w ∈ LB.wchart M φ j → Geo.Tor.gm (𝟙 (Sp S)) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * Geo.Tor.gm (𝟙 (Sp S)) w ⊤ c := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      (gm_res _ w le_top h c))
  refine ⟨t, isGen_of_gm _ fun w j j' h h' => ?_, (v _ _ (all _)).trans ?_⟩
  · refine (v w j h).trans (Eq.trans ?_ (congrArg _ (v w j' h')).symm)
    rw [← trF_trans hM _ ε (𝟙 _) w h h' (all w), _root_.mul_assoc]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) _ (all _) (all _) (all _)), _root_.one_mul, hc]

end Local

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

open GlobalTheory.TorusModel

theorem exists_over {S : Type} [CommRing S] [IsLocalRing S] (f : Sp S ⟶ Sp R) (b : Over.mk f ⟶ D.P.A) :
    ∃ g : GtPt D (Over.mk f), g.b = b := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt S)
  have C : IsCub (th D (T := Over.mk f) (cpt S) J) := isCub_cubV D.cub hJ
  obtain ⟨v, m₀, m⟩ := exists_mult C (c := cP D (Over.mk f)) (cPoint_add D _) b
  choose s hs hv using fun χ => exists_gen_cpt D.P.isLB (DegPre.gtφT D (Over.mk f) b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_) (hs 0) (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
      ((hv 0).trans (m₀.trans (val_one _).symm)),
    fun χ χ' => corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAtT (T := Over.mk f) hJ _ _ _))).trans
        ((m χ χ').trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl⟩
  · refine (prod_pt b 0 h).trans ?_
    rw [cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_pt b _ h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt b χ h) (prod_pt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ => (val_corr hJ (h.2 χ) _).trans (val_corr hJ (h'.2 χ) _).symm

omit [IsDomain R] in
theorem red_comp : redE R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), (∀ b : epsR R ⟶ D.P.A, IsTangent b → ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = b) ∧ (∀ gm gm' : GtPt D (epsR R), ∃ gm'', GtPt.IsAdd gm gm' gm'' ∧ (GtTan gm → GtTan gm' → GtTan gm'')) ∧ (∀ (T T' : Over (Sp R)) (h : T' ⟶ T) (gm : GtPt D T), ∃ gm' : GtPt D T', GtPt.IsPull h.left gm gm') ∧ ∀ gm gm' : GtPt D (epsR R), gm.b = gm'.b → (∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (gm.s χ) (gm'.s χ)) → gm = gm' := by
  intro R _ _ _ D
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨G, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => isZero_of_isAdd (by simpa using ha T 1 1)
  let r : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) red_comp
  let a : epsR R ⟶ baseOver (Sp R) := Over.homMk (spMap (algebraMap R (DualNumber R))) (Category.comp_id _)
  have hra : r ≫ a = 𝟙 _ := Over.OverMorphism.ext red_comp
  have tan : ∀ x : epsR R ⟶ G, GtTan (Φ _ x) ↔ r ≫ x = 1 := fun x =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hp _ _ r x) h).trans (isZero_unique ho (hz _))),
      fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ r x⟩⟩
  refine ⟨fun b hb => ?_, fun g g' => ?_, fun T T' h g => ?_, fun g g' hb hs =>
    pt_ext hb fun χ _ _ hJ => val_corr hJ (hs χ) _⟩
  · have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
      simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
        IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
    obtain ⟨g, hg⟩ := exists_over (D := D) _ b
    obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    refine ⟨Φ _ (((a ≫ r) ≫ x)⁻¹ * x), (tan _).2 ?_, ?_⟩
    · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, hra, Category.id_comp,
        inv_mul_cancel]
    · have h₁ := ((TorusModel.isAdd_iff _ _ _).1 (ha _ ((a ≫ r) ≫ x) (((a ≫ r) ≫ x)⁻¹ * x))).1
      have h₂ := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ (a ≫ r) x)).1
      have h₃ : r ≫ b = 1 := Over.OverMorphism.ext (hb.trans (Category.id_comp _).symm)
      rw [mul_inv_cancel_left, h₂, hg, Category.assoc, h₃, MonObj.comp_one, _root_.one_mul] at h₁
      exact h₁.symm
  · obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    obtain ⟨x', rfl⟩ := (Φ (epsR R)).surjective g'
    refine ⟨_, ha _ x x', fun h h' => (tan _).2 ?_⟩
    rw [MonObj.comp_mul, (tan _).1 h, (tan _).1 h', _root_.mul_one]
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    exact ⟨_, hp _ _ h x⟩

end GlobalTheory.MBLow.GtVec

end
