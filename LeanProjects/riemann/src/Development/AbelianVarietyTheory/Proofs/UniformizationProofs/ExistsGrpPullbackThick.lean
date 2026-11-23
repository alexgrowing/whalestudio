import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoordPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace

section Transport

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} {ψ : K → (Y ⟶ X)} (hψ : ψ = fun k => φ' k ≫ F)
    (t : LB.Gen (LB.LinComb L ψ ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L ψ p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L ψ p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  subst hψ
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (y : Z) p,
      r y ∈ LB.wchart L (fun k => φ' k ≫ F) p → r y ∈ LB.wchart L' φ' q →
      gm r y _ s = (pw w φ' ε r y p q)⁻¹ * gm r y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (y : Z) p,
        r y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r y p q)⁻¹ * gm r y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans
        (congrArg (·⁻¹) (hu p q _ _ y hz))) (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r y p h₁ h₂ => ?_⟩
    have hz : r y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv _ r y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q hp hq => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg (pw w φ' ε r z p q * ·) (hs q Z r z p hp hq).symm)

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨a, ha, hv⟩ := exists_down_val hw hL hL' (φ' := φ') (ψ := fun k => h ≫ φ k)
    (funext fun k => (hψ k).symm) (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show (h ≫ φ k) (r z) ∈ L.U (p k)
    rw [← hψ k]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (q : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w q z (J (q ≫ F)) (J' q)

theorem val_of_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hψ])]
  exact H Z r z _ (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem exists_good' (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

end Transport

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem prod_O (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ b χ i) ^ Oinvε i =
      (h (b * cP D T χ).left)⁻¹ * h (cP D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (b * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem push_cP (hD : IsPullDeg φ D D') (T' : Over (Spec (CommRingCat.of R'))) (χ : D'.X) :
    pushPt (pull_grp hD).1.w (cP D' T' χ) = cP D _ (hD.xe χ) := Over.OverMorphism.ext (by
  show (T'.hom ≫ (D'.c χ).left) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
    (T'.hom ≫ specOf φ) ≫ (D.c (hD.xe χ)).left
  rw [Category.assoc, hD.c_pr, ← Category.assoc])

variable (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)

include hp in
theorem over_base : h ≫ T.hom = T'.hom ≫ specOf φ := by
  rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, (pull_grp hD).1.w, ← Category.assoc, Over.w]

include hp in
theorem Oφ_pull (x : D'.X) (κ : Fin 4) :
    D'.Oφ p' x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ D.Oφ p (hD.xe x) κ := by
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h (over_base hD p p' h hp)
  have e : pushPt (pull_grp hD).1.w p' = U ≫ p := Over.OverMorphism.ext hp
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p (hD.xe x) κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom (pull_grp hD) T') p' (cP D' T' x)).trans
      (congrArg (pushPt (pull_grp hD).1.w p' * ·) (push_cP hD T' x)))
  · exact congrArg (fun q => q.left) (push_cP hD T' x)
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom (pull_grp hD) T'))

include hp in
theorem mul_pull (hG : GlobalFnsSt) (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ p χ) Oinvε))
    (a : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε))
    (H : ∀ x, PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε (a x) (t (hD.xe x)) h)
    (hm : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') p)).left))
      (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) (χ χ' : D'.X) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.mulGen D'.P.L _ _ _ _ (a (χ + χ'))
        (LB.pullGen D'.P.L (thφ D'.P.A (x3 D'.P.A)) thε D'.cub.t
          (lift (toUnit _ ≫ D'.c χ) (lift (toUnit _ ≫ D'.c χ') p')).left))
      (LB.mulGen D'.P.L _ _ _ _ (a χ) (a χ')) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h (over_base hD p p' h hp)
  have e : pushPt (pull_grp hD).1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have va : ∀ x, val (t (hD.xe x)) h y J = (om hD.w y J J' (p' * cP D' T' x).left)⁻¹ *
      om hD.w y J J' (cP D' T' x).left * om hD.w y J J' p'.left * (om hD.w y J J' (1 : T' ⟶ D'.P.A).left)⁻¹ *
      val (a x) (𝟙 _) y J' := fun x => by
    have := val_of_pmaps (Oφ_pull hD p p' h hp x) (H x) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at this
    rw [this, prod_O]
  have c := cub_pull hG hD (T' := T') hJ hJ' (cP D' T' χ) (cP D' T' χ') p'
  have q : (lift (cP D' T' χ) (lift (cP D' T' χ') p')).left ≫ (cubeMapOf (pull_grp hD)).F3 =
      h ≫ (lift (cP D T (hD.xe χ)) (lift (cP D T (hD.xe χ')) p)).left := by
    refine Eq.trans (hom_ext_triple _ fun i => ?_ : _ = (lift (pushPt (pull_grp hD).1.w (cP D' T' χ))
      (lift (pushPt (pull_grp hD).1.w (cP D' T' χ')) (pushPt (pull_grp hD).1.w p'))).left) ?_
    · rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    · rw [push_cP, push_cP, e, ← comp_cP D U, ← comp_cP D U (hD.xe χ'), ← comp_lift, ← comp_lift]
      rfl
  rw [q] at c
  replace c := c.trans (congrArg₂ (· * ·) (prod_cub (cP D' T' χ) (cP D' T' χ') p' (om hD.w y J J')) rfl)
  have m : val (t (hD.xe χ + hD.xe χ')) h y J *
      val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        (h ≫ (lift (cP D T (hD.xe χ)) (lift (cP D T (hD.xe χ')) p)).left) y J =
      val (t (hD.xe χ)) h y J * val (t (hD.xe χ')) h y J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      ((val_corr hJ (hm (hD.xe χ) (hD.xe χ')) h).trans (val_mul hJ _ _ _))
  rw [← map_add] at m
  replace m := (congrArg₂ (· * ·) rfl c).symm.trans m
  rw [va, va, va, cPoint_add, mul_comm p', mul_comm p', mul_comm p'] at m
  have vc := val_cub D'.cub (𝟙 T') hJ' (cP D' T' χ) (cP D' T' χ') p'
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at vc
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl vc)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  show val (a (χ + χ')) (𝟙 T'.left) y J' * cubV D'.cub y J' (cP D' T' χ) (cP D' T' χ') p' =
    val (a χ) (𝟙 T'.left) y J' * val (a χ') (𝟙 T'.left) y J'
  apply Additive.ofMul.injective
  have m' := congrArg Additive.ofMul m
  simp only [ofMul_mul, ofMul_inv] at m' ⊢
  linear_combination (norm := abel) m'

include hp in
theorem val_unit_pull {x : D'.X} {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe x)) Oinvε)}
    {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε)}
    (H : PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε a t h) {T₀ : Over (Spec (CommRingCat.of R'))}
    (ρ : T₀ ⟶ T') (hρ : ρ ≫ p' = 1) {y : T₀.left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    val t (ρ.left ≫ h) y J = val a ρ.left y J' := by
  rw [val_of_pmaps (Oφ_pull hD p p' h hp x) H ρ.left hJ hJ']
  simp only [WeightPf.Oφ_comp, hρ]
  rw [prod_O, _root_.one_mul, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul]

include hp in
theorem val_ratio_pull {x : D'.X} {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe x)) Oinvε)}
    {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε)}
    (H : PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε a t h) {T₀ : Over (Spec (CommRingCat.of R'))}
    (ρ ρ' : T₀ ⟶ T') (hρ : ρ ≫ p' = ρ' ≫ p') {y : T₀.left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (u : (T₀.left.presheaf.stalk y)ˣ) (hu : val t (ρ.left ≫ h) y J = u * val t (ρ'.left ≫ h) y J) :
    val a ρ.left y J' = u * val a ρ'.left y J' := by
  rw [val_of_pmaps (Oφ_pull hD p p' h hp x) H ρ.left hJ hJ',
    val_of_pmaps (Oφ_pull hD p p' h hp x) H ρ'.left hJ hJ'] at hu
  simp only [WeightPf.Oφ_comp, hρ] at hu
  rw [mul_left_comm] at hu
  exact mul_left_cancel hu

end Pull

section Thick

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

omit [IsDomain R] in
theorem mono_thick (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

omit [IsDomain R] [IsDomain R'] in

theorem exists_grpPullback_thick (φ : R →+* R') (I : Ideal R) (I' : Ideal R')
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) (e : ℕ)
    (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left)
    (hh : h ≫ pullback.fst G.hom (thick R I e) =
      pullback.fst G'.hom (thick R' I' e) ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ))) :
    ∃ σ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      IsGrpPullback (thickObj R' I' e G') (thickObj R I e G) σ h := by
  have := mono_thick I e
  have b : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have n := (isGrpPullback_pullback G' (thick R' I' e)).comp b
  have g₀ := isGrpPullback_pullback G (thick R I e)
  have k : (h ≫ (thickObj R I e G).hom) ≫ thick R I e = (thickObj R' I' e G').hom ≫ thick R' I' e ≫ specOf φ := by
    rw [Category.assoc, ← g₀.1.w, ← Category.assoc, hh, n.1.w]
  have u : η[thickObj R' I' e G'].left ≫ (thickObj R' I' e G').hom = 𝟙 _ := Over.w _
  let σ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
    η[thickObj R' I' e G'].left ≫ h ≫ (thickObj R I e G).hom
  have s : σ ≫ thick R I e = thick R' I' e ≫ specOf φ :=
    (Category.assoc _ _ _).trans ((congrArg (η[thickObj R' I' e G'].left ≫ ·) k).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) u).trans (Category.id_comp _))))
  refine ⟨σ, g₀.cancel (n.congr s.symm hh.symm) ?_⟩
  rw [← cancel_mono (thick R I e), k, Category.assoc, s]

theorem val_charGen {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z W : Scheme.{0}} (L : LB Z) (χ : X)
    (r : W ⟶ (splitTorus S X ⊗ G).left) (y : W) (J : (W ⟶ Z) → L.ι) :
    val (charGen X G L χ) r y J = gm (r ≫ (fst (splitTorus S X) G).left) y ⊤ (charUnit S X χ) :=
  (gm_res r y _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ y ⊤ trivial _)

end Thick

section Clauses

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {S S' : Scheme.{0}} {j : S ⟶ Spec (CommRingCat.of R)}
  {j' : S' ⟶ Spec (CommRingCat.of R')} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
  [IsCommMonObj G'] (p : (Over.map j).obj G ⟶ D.P.A) (p' : (Over.map j').obj G' ⟶ D'.P.A) (h : G'.left ⟶ G.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
  {σ : S' ⟶ S} (gp : IsGrpPullback G' G σ h) {χ : D'.X}
  {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe χ)) Oinvε)} {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε)}
  (H : PMaps hD.w (D'.Oφ p' χ) (D.Oφ p (hD.xe χ)) Oinvε a t h)

include hp gp H in
theorem unit_pull (e₂ : (Over.map j').map η[G'] ≫ p' = 1)
    (hu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L)) :
    LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (eSec G')) (LB.oneGen D'.P.L) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have e₁ : eSec G' ≫ h = σ ≫ eSec G := (cubeMapOf gp).e_comm
  have e₄ : val t (σ ≫ eSec G) y J = 1 :=
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hu σ).trans (val_one _))
  have e₃ := val_unit_pull hD p p' h hp H ((Over.map j').map η[G']) e₂ (y := y) hJ hJ'
  have e₅ : val a (eSec G') y J' = 1 :=
    e₃.symm.trans ((congrArg (fun r => val t r y J) e₁).trans e₄)
  exact (val_pull hJ' _ _ _).trans ((congrArg (fun r => val a r y J') (Category.id_comp _)).trans
    (e₅.trans (val_one _).symm))

omit [IsCommMonObj G] [IsCommMonObj G'] in
include hp gp H in
theorem weight_pull (i : splitTorus S D.X ⟶ G) (i' : splitTorus S' D'.X ⟶ G')
    (hT : (splitTorus S' D'.X).left ⟶ (splitTorus S D.X).left) (hi : i'.left ≫ h = hT ≫ i.left)
    (hχ : hT.appTop.hom (charUnit _ D.X (hD.xe χ)).val = (charUnit _ D'.X χ).val)
    (aO : (Over.map j').map (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']) ≫ p' =
      (Over.map j').map (snd (splitTorus S' D'.X) G') ≫ p')
    (hw : LB.Gen.Corr D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left)
      (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L (hD.xe χ))
        (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left))) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.pullGen D'.P.L _ _ a (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']).left)
      (LB.mulGen D'.P.L _ _ _ _ (charGen D'.X G' D'.P.L χ)
        (LB.pullGen D'.P.L _ _ a (snd (splitTorus S' D'.X) G').left)) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have wT : hT ≫ (splitTorus S D.X).hom = (splitTorus S' D'.X).hom ≫ σ := by
    rw [← Over.w i, ← Category.assoc, ← hi, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
  obtain ⟨N, n₁, n₂, n₃⟩ : ∃ N : (splitTorus S' D'.X ⊗ G').left ⟶ (splitTorus S D.X ⊗ G).left,
      N ≫ (fst (splitTorus S D.X) G).left = (fst (splitTorus S' D'.X) G').left ≫ hT ∧
      N ≫ (snd (splitTorus S D.X) G).left = (snd (splitTorus S' D'.X) G').left ≫ h ∧
      N ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left =
        (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']).left ≫ h := by
    let p₁ := fst (splitTorus S' D'.X) G'
    let pr := snd (splitTorus S' D'.X) G'
    refine ⟨(lift (pushPt wT p₁) (pushPt gp.1.w pr)).left,
      congrArg (fun q => q.left) (lift_fst (pushPt wT p₁) (pushPt gp.1.w pr)),
      congrArg (fun q => q.left) (lift_snd (pushPt wT p₁) (pushPt gp.1.w pr)), ?_⟩
    have : lift (pushPt wT p₁) (pushPt gp.1.w pr) ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]) =
        (pushPt wT p₁ ≫ i) * pushPt gp.1.w pr :=
      (MonObj.comp_mul _ (fst _ _ ≫ i) (snd _ _)).trans (by rw [lift_fst_assoc, lift_snd])
    refine (congrArg (fun q => q.left) this).trans (gp.2 _ (p₁ ≫ i') pr _ _ ?_ rfl)
    show (p₁.left ≫ hT) ≫ i.left = (p₁.left ≫ i'.left) ≫ h
    rw [Category.assoc, Category.assoc, hi]
  have v₃ : val t (N ≫ (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left) y J =
      gm (N ≫ (fst (splitTorus S D.X) G).left) y ⊤ (charUnit _ D.X (hD.xe χ)) *
        val t (N ≫ (snd (splitTorus S D.X) G).left) y J :=
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))
  have v₄ : gm ((fst (splitTorus S' D'.X) G').left ≫ hT) y ⊤ (charUnit _ D.X (hD.xe χ)) =
      gm (fst (splitTorus S' D'.X) G').left y ⊤ (charUnit _ D'.X χ) :=
    (gm_pull _ hT y ⊤ trivial _).symm.trans (congrArg (gm (fst (splitTorus S' D'.X) G').left y ⊤) (Units.ext hχ))
  rw [n₁, n₂, n₃, v₄] at v₃
  have v₅ := val_ratio_pull hD p p' h hp H _ _ aO (y := y) hJ hJ' _ v₃
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_mul hJ' _ _ _).trans
    (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ' _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end Clauses

end GlobalTheory.TorusCoordPull

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TorusCoordPull

theorem exists_gtCoord_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G) (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) → (IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val) → ∃ g' : GtCoord I' D' e G', g'.q = q' ∧ ((g').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ (g).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ D.Oφ (g).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g').pG x) (D.Oφ (g).pG (hD.xe x)) Oinvε ((g').t x) ((g).t (hD.xe x)) h) := by
  intro hG R R' _ _ _ _ φ D D' hD I I' _ G _ _ G' _ _ bc hbc e g h q' i' hh
    ⟨q_hom, q_flat, q_surj, q_aff, i_hom, hker, hp, hT, hi, hχ⟩
  obtain ⟨σ, gp⟩ := exists_grpPullback_thick φ I I' bc hbc e h hh
  have hw := (isGen_iff hD.w).1 hD.w_gen
  have hO := Oφ_pull hD g.pG ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e) h hp
  choose a ha H using fun x : D'.X => exists_pmaps hw D.P.isLB D'.P.isLB (hO x) (g.t (hD.xe x)) (g.t_gen _)
  have e₂ : (Over.map (thick R' I' e)).map η[thickObj R' I' e G'] ≫
      ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e) = 1 := by
    rw [← Category.assoc, ← Functor.map_comp, IsMonHom.one_hom]
    refine Over.OverMorphism.ext ((cubeMapOf (isGrpPullback_pullback D'.P.A (thick R' I' e))).e_comm.trans ?_)
    show thick R' I' e ≫ η[D'.P.A].left = (𝟙 _ ≫ thick R' I' e) ≫ η[D'.P.A].left
    rw [Category.id_comp]
  have aq : ((fst (splitTorus _ D'.X) (thickObj R' I' e G') ≫ i') * snd _ _) ≫ q' = snd _ _ ≫ q' := by
    rw [MonObj.mul_comp, Category.assoc, hker.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have aO : (Over.map (thick R' I' e)).map (lift (fst (splitTorus _ D'.X) (thickObj R' I' e G') ≫ i') (snd _ _) ≫
        μ[thickObj R' I' e G']) ≫ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e) =
      (Over.map (thick R' I' e)).map (snd (splitTorus _ D'.X) (thickObj R' I' e G')) ≫
        ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Hom.mul_def, aq, Functor.map_comp, Category.assoc]
  exact ⟨⟨q', q_hom, q_flat, q_surj, q_aff, i', i_hom, hker, a, ha,
    mul_pull hD g.pG ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e) h hp hG g.t a H g.t_mul,
    fun χ => unit_pull hD g.pG _ h hp gp (H χ) e₂ (g.t_unit _),
    fun χ => weight_pull hD g.pG _ h hp gp (H χ) g.i i' hT hi (hχ χ) aO (g.t_weight _)⟩,
    rfl, hp, fun x => ⟨hO x, H x⟩⟩

end GlobalTheory
