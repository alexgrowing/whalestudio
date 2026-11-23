import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement

noncomputable section

namespace GlobalTheory.ConstLie

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Points

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem exists_isAdd (g g' : GtPt D T) : ∃ g'', g.IsAdd g' g'' := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
      (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b))) (𝟙 T.left) y J =
      cv g χ y J * cv g' χ y J * (th D y J (cP D _ χ) g.b g'.b)⁻¹ := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cubAtT hJ _ _ _))))
  obtain ⟨g'', hb, hv⟩ := exists_pt (g.b * g'.b) (fun χ => LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ)) (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b)))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (g'.isGen _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt g.b χ h) (prod_pt g'.b χ h))
        (prod_neg _ _ (prod_cub (cP D _ χ) g.b g'.b h))).trans ?_
      rw [prod_pt, _root_.mul_assoc (cP D _ χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      refine (vv 0 y J hJ).trans ?_
      rw [cv_zero g hJ, cv_zero g' hJ, cPoint_zero, C.face]; simp) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      have e₁ := congrArg Additive.ofMul (cv_add g hJ χ χ')
      have e₂ := congrArg Additive.ofMul (cv_add g' hJ χ χ')
      have e₃ := congrArg Additive.ofMul (C.compat (cP D _ χ) (cP D _ χ') g.b g'.b)
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₂ - e₃)
  exact ⟨g'', (TorusModel.isAdd_iff _ _ _).2 ⟨hb, fun χ y J hJ =>
    (congrArg₂ (· * ·) ((hv χ _ _ y J hJ).trans (vv χ y J hJ)) rfl).trans (inv_mul_cancel_right _ _)⟩⟩

theorem exists_isPull (k : T' ⟶ T) (g : GtPt D T) : ∃ g' : GtPt D T', GtPt.IsPull k.left g g' := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (g.s χ) k.left) (𝟙 T'.left) y J =
      val (g.s χ) k.left y J := fun χ y J hJ => by rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_pt (k ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) k.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen _) _)
    (fun χ U _ h => (FormalPoint.prod_gtφT k g.b χ h).trans (prod_pt _ χ h).symm)
    (fun y J hJ => (vv 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ]
      exact FormalPoint.val_s_add g k hJ χ χ')
  exact ⟨g', (isPull_iff _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩

theorem exists_gtComb {m : ℕ} (cf : Fin m → R) (e : Fin m → GtPt D (epsR R)) : ∃ ν, ArcQ.GtComb cf e ν := by
  choose u hu using fun i => exists_isPull (T' := epsR R) (T := epsR R)
    (Over.homMk (spMap (epsScaleR (cf i))) (LieCombBaseChange.epsScale_over _)) (e i)
  obtain ⟨o, ho⟩ := FormalValue.exists_isZero D (epsR R)
  choose add hadd using exists_isAdd (D := D) (T := epsR R)
  let p : Fin (m + 1) → GtPt D (epsR R) := fun i => Fin.induction o (fun j q => add q (u j)) i
  exact ⟨p (Fin.last m), u, p, hu, ho, fun i => hadd _ _, rfl⟩

end Points

section Transport

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstFam

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {f : R₀ →+* R} {φ : D.P.A.left ⟶ D₀.P.A.left}

def Tr (w : LB.Iso D.P.L (D₀.P.L.pull φ)) (e : D₀.X → D.X) {T : Over (Sp R)} {T₀ : Over (Sp R₀)}
    (h : T.left ⟶ T₀.left) (g : GtPt D T) (g₀ : GtPt D₀ T₀) : Prop :=
  ∀ x, (∀ k, DegPre.gtφT D T g.b (e x) k ≫ φ = h ≫ DegPre.gtφT D₀ T₀ g₀.b x k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D₀.P.L z J → Good D.P.L z J' →
      val (g₀.s x) (r ≫ h) z J =
        (∏ k, wVal w z J J' (r ≫ DegPre.gtφT D T g.b (e x) k) ^ DegPre.gtε k) * val (g.s (e x)) r z J'

variable {w : LB.Iso D.P.L (D₀.P.L.pull φ)}

theorem exists_tr_down (hG : GlobalFnsSt) (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (hw : w.IsGen)
    (e : D₀.X ≃+ D.X) (hc : ∀ y, (D.c (e y)).left ≫ φ = spMap f ≫ (D₀.c y).left) {T : Over (Sp R)}
    {T₀ : Over (Sp R₀)} (h : T.left ⟶ T₀.left) (hh : h ≫ T₀.hom = T.hom ≫ spMap f) (g₀ : GtPt D₀ T₀) :
    ∃ g : GtPt D T, Tr w e h g g₀ := by
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp hw e.symm.toAddMonoidHom
    (fun y => by have := hc (e.symm y); rwa [AddEquiv.apply_symm_apply] at this) h hh g₀
  refine ⟨g, fun x => ?_⟩
  have := hg (e x)
  rw [show e.symm.toAddMonoidHom (e x) = x from e.symm_apply_apply x] at this
  exact this

theorem exists_tr_up (hG : GlobalFnsSt) (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (hw : w.IsGen)
    (e : D₀.X ≃+ D.X) (hc : ∀ y, (D.c (e y)).left ≫ φ = spMap f ≫ (D₀.c y).left) {T : Over (Sp R)}
    (s₀ : T.left ⟶ Sp R₀) (hs : s₀ = T.hom ≫ spMap f) (g : GtPt D T) :
    ∃ g₀ : GtPt D₀ (Over.mk s₀), Tr w e (𝟙 T.left) g g₀ := by
  subst hs
  have hcP : ∀ y, pushPt gp.1.w (cP D T (e y)) = cP D₀ _ y := fun y => Over.OverMorphism.ext (by
    show (T.hom ≫ (D.c (e y)).left) ≫ φ = (T.hom ≫ spMap f) ≫ (D₀.c y).left
    rw [Category.assoc, hc, Category.assoc])
  have hψ : ∀ y k, DegPre.gtφT D T g.b (e y) k ≫ φ =
      DegPre.gtφT D₀ (Over.mk (T.hom ≫ spMap f)) (pushPt gp.1.w g.b) y k := fun y k => by
    fin_cases k
    · refine congrArg (fun q => q.left) ((map_mul (pushHom gp T) (cP D T (e y)) g.b).trans ?_)
      exact congrArg (· * pushPt gp.1.w g.b) (hcP y)
    · exact congrArg (fun q => q.left) (hcP y)
    · rfl
    · exact congrArg (fun q => q.left) (map_one (pushHom gp T))
  choose t ht vt using fun y => exists_up ((isGen_iff w).1 hw) D₀.P.isLB D.P.isLB (g.s (e y)) (g.isGen _)
  have vt₁ : ∀ y (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D₀.P.L z J → Good D.P.L z J' →
      val (t y) r z J = (∏ k, wVal w z J J' (r ≫ DegPre.gtφT D T g.b (e y) k) ^ DegPre.gtε k) *
        val (g.s (e y)) r z J' := fun y Z r z J J' hJ hJ' => by
    rw [val_of (t y) r z J (fun k => J ((r ≫ DegPre.gtφT D T g.b (e y) k) ≫ φ)) (fun k => by rw [Category.assoc])]
    exact vt y Z r z _ _ (Set.mem_iInter.2 fun k => hJ ((r ≫ DegPre.gtφT D T g.b (e y) k) ≫ φ)) (hJ'.mem _ r)
  have vt' : ∀ y (z : T.left) J J', Good D₀.P.L z J → Good D.P.L z J' → val (t y) (𝟙 _) z J =
      (wVal w z J J' (cP D T (e y) * g.b).left)⁻¹ * wVal w z J J' (cP D T (e y)).left *
        wVal w z J J' g.b.left * (wVal w z J J' (1 : T ⟶ D.P.A).left)⁻¹ *
        cv g (e y) z J' := fun y z J J' hJ hJ' => by
    have v := vt₁ y _ (𝟙 _) z J J' hJ hJ'
    simp only [Category.id_comp] at v
    exact v.trans (congrArg (· * _) (prod_pt g.b (e y) (wVal w z J J')))
  obtain ⟨g₀, hb, hv⟩ := exists_pt (D := D₀) (T := Over.mk (T.hom ≫ spMap f)) (pushPt gp.1.w g.b) t ht
    (fun y U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ DegPre.gtε k) (hψ y k))
    (fun z J hJ => by
      obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
      refine (vt' 0 z J J' hJ hJ').trans ?_
      rw [map_zero, cv_zero g hJ', cPoint_zero, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    (fun y y' z J hJ => by
      obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
      have e₁ := congrArg Additive.ofMul (cv_add g hJ' (e y) (e y'))
      have c := ConstPoint.th_pushPt hG gp ((isGen_iff w).1 hw) (T' := T) hJ hJ' (cP D T (e y)) (cP D T (e y')) g.b
      rw [hcP, hcP] at c
      refine (congrArg₂ (fun a b : (T.left.presheaf.stalk z)ˣ => a * b) (vt' _ z J J' hJ hJ') c).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (vt' _ z J J' hJ hJ') (vt' _ z J J' hJ hJ')).symm)
      rw [map_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e₁ ⊢
      linear_combination (norm := abel) e₁)
  refine ⟨g₀, fun x => ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩⟩
  · rw [hb]; exact (hψ x k).trans (Category.id_comp _).symm
  · exact (congrArg (fun q => val (g₀.s x) q z J) (Category.comp_id r)).trans
      ((hv x Z r z J hJ).trans (vt₁ x Z r z J J' hJ hJ'))

variable {e : D₀.X → D.X}

theorem Tr.cancel (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (he : Function.Surjective e) {T T' : Over (Sp R)}
    {T₀ : Over (Sp R₀)} {h : T.left ⟶ T₀.left} {h' : T'.left ⟶ T₀.left} {g : GtPt D T} {g' : GtPt D T'}
    {g₀ : GtPt D₀ T₀} (H : Tr w e h g g₀) (H' : Tr w e h' g' g₀) (r : T' ⟶ T) (hr : r.left ≫ h = h') :
    GtPt.IsPull r.left g g' := by
  have hp : ∀ x k, DegPre.gtφT D T' g'.b (e x) k = r.left ≫ DegPre.gtφT D T g.b (e x) k := fun x k => by
    refine gp.1.hom_ext ?_ ?_
    · rw [(H' x).1, Category.assoc, (H x).1, ← Category.assoc, hr]
    · rw [Category.assoc]
      refine Eq.trans ?_ ((Over.w r).symm.trans (congrArg (r.left ≫ ·) ?_))
      · fin_cases k <;> exact Over.w _
      · fin_cases k <;> exact (Over.w _).symm
  refine (isPull_iff _ _ _).2 ⟨Over.OverMorphism.ext (hp 0 2), fun χ z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := exists_good' D₀.P.isLB z
  have v := (H x).2 _ r.left z J J' hJ hJ'
  have v' := (H' x).2 _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp, hp] at v'
  rw [hr] at v
  exact mul_left_cancel (v'.symm.trans v)

theorem Tr.inj {T : Over (Sp R)} {T₀ : Over (Sp R₀)} {h : T.left ⟶ T₀.left} {g g' : GtPt D T}
    {g₀ g₀' : GtPt D₀ T₀} (H : Tr w e h g g₀) (H' : Tr w e h g' g₀') (r : T₀.left ⟶ T.left) (hr : r ≫ h = 𝟙 _)
    (hb : r ≫ g.b.left = r ≫ g'.b.left)
    (hv : ∀ χ z J, Good D.P.L z J → val (g.s χ) r z J = val (g'.s χ) r z J) : g₀ = g₀' := by
  have hp : ∀ χ k, r ≫ DegPre.gtφT D T g.b χ k = r ≫ DegPre.gtφT D T g'.b χ k := fun χ k =>
    ((TorusCoord.comp_eq_of_left g.b g'.b r r hb).1 χ k).trans (by rw [TorusCoord.gtφT_eq])
  refine pt_ext (Over.OverMorphism.ext ?_) fun x z J hJ => ?_
  · have a : g.b.left ≫ φ = h ≫ g₀.b.left := (H 0).1 2
    have a' : g'.b.left ≫ φ = h ≫ g₀'.b.left := (H' 0).1 2
    rw [← Category.id_comp g₀.b.left, ← Category.id_comp g₀'.b.left, ← hr, Category.assoc, Category.assoc, ← a, ← a',
      reassoc_of% hb]
  · obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
    have v := (H x).2 _ r z J J' hJ hJ'
    have v' := (H' x).2 _ r z J J' hJ hJ'
    rw [hr] at v v'
    simp only [hp, hv _ z J' hJ'] at v
    exact v.trans v'.symm

theorem Tr.smul (hG : GlobalFnsSt) (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (hw : w.IsGen)
    (he : Function.Surjective e)
    {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D₀.X] (oa : D.OAct O) (oa₀ : D₀.OAct O)
    (hl : ∀ (a : O) x, e (a • x) = a • e x) (ho : ∀ a, (oa.onB.act a).left ≫ φ = φ ≫ (oa₀.onB.act a).left) (a : O)
    {T : Over (Sp R)} {T₀ : Over (Sp R₀)} {h : T.left ⟶ T₀.left} (hh : h ≫ T₀.hom = T.hom ≫ spMap f)
    {g g' : GtPt D T} {g₀ g₀' : GtPt D₀ T₀} (r : Tr w e h g g₀) (r' : Tr w e h g' g₀')
    (h₀ : FormalPoint.IsSmulPt oa₀ a g₀ g₀') : FormalPoint.IsSmulPt oa a g g' := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := oa₀.onB.hom a
  have := oa₀.onB.hom (star a)
  let ρ : Over.mk (T.hom ≫ spMap f) ⟶ T₀ := Over.homMk h hh
  have r₁ : pushHom gp T g.b = ρ ≫ g₀.b := Over.OverMorphism.ext ((r 0).1 2)
  have r₁' : pushHom gp T g'.b = ρ ≫ g₀'.b := Over.OverMorphism.ext ((r' 0).1 2)
  have hc : ∀ x, pushHom gp T (cP D T (e x)) = cP D₀ _ x := fun x =>
    (Over.OverMorphism.ext ((r x).1 1)).trans (comp_cP D₀ ρ x)
  have hr := oa₀.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u₀, hu₀, n₀⟩ := exists_ros hG D₀.P.isAb D₀.P.isLB _ _ hr
  have hb : g'.b = g.b ≫ oa.onB.act a := ConstGrp.push_injective gp T (by
    rw [ConstGrp.push_act gp (ho a), r₁, r₁', h₀.1, Category.assoc])
  refine ⟨hb, fun u hu n χ => corr_of_val D.P.isLB fun z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := exists_good' D₀.P.isLB z
  have k := (val_smul oa₀ a g₀ u₀ x ρ hJ).symm.trans (val_corr hJ (h₀.2 u₀ hu₀ n₀ x) ρ.left)
  have c := ConstGrp.ros_push gp hG D.P.isAb D₀.P.isLB D.P.isLB ((isGen_iff w).1 hw) (ho (star a)) (ho a) u₀ hu₀ n₀
    u hu n (cP D T (e x)) g.b hJ hJ' (wVal w z J J') (fun _ => rfl)
  rw [hc, r₁] at c
  have b := (r (star a • x)).2 _ (𝟙 _) z J J' hJ hJ'
  have b' := (r' x).2 _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at b b'
  rw [prod_pt _ _ (wVal w z J J')] at b b'
  have k' := (congrArg₂ (fun a b : (T.left.presheaf.stalk z)ˣ => a * b) b c).symm.trans (k.trans b')
  beta_reduce at k'
  refine (val_smul' oa a g u (e x) hJ').trans ?_
  rw [hl] at k'
  generalize val (g'.s (e x)) (𝟙 _) z J' = s' at k' ⊢
  rw [hb, TorusExt.cPoint_smul oa] at k'
  apply Additive.ofMul.injective
  have k'' := congrArg Additive.ofMul k'
  simp only [ofMul_mul, ofMul_inv] at k'' ⊢
  linear_combination (norm := abel) k''

end Transport

section Lie

open ReciprocityTheory.ChartRestriction.G.Chart hiding spMap spMap_comp

variable {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
theorem exists_bar (w : epsR R ⟶ G) : ∃ w' : epsR A ⟶ (Over.pullback (spMap f)).obj G,
    w'.left ≫ pullback.fst G.hom (spMap f) = spMap (dualMapR f) ≫ w.left :=
  ⟨Over.homMk (pullback.lift (spMap (dualMapR f) ≫ w.left) (epsR A).hom (by
      rw [Category.assoc, Over.w w]; exact LieCombBaseChange.dualMap_over f)) (pullback.lift_snd _ _ _),
    pullback.lift_fst _ _ _⟩

omit [IsCommMonObj G] in

theorem red_eq_of_comb {n : ℕ} {v v' : Fin n → (epsR R ⟶ G)} {c c' : Fin n → R} {w w' : epsR R ⟶ G}
    (h : IsLieComb c v w) (h' : IsLieComb c' v' w') (e : ∀ i, f (c i) = f (c' i))
    (e' : ∀ i, spMap (dualMapR f) ≫ (v i).left = spMap (dualMapR f) ≫ (v' i).left) :
    spMap (dualMapR f) ≫ w.left = spMap (dualMapR f) ≫ w'.left := by
  choose bar hbar using exists_bar (G := G) f
  have gp := isGrpPullback_pullback G (spMap f)
  have a := (lieComb_baseChange R A f G _ _ gp n v w c (fun i => bar (v i)) (bar w) (fun i => hbar _) h).1 (hbar w)
  simp only [e] at a
  exact (hbar w).symm.trans
    ((lieComb_baseChange R A f G _ _ gp n v' w' c' (fun i => bar (v i)) (bar w)
      (fun i => (hbar _).trans (e' i)) h').2 a)

theorem isTangent_iff_comb (w : epsR R ⟶ G) : IsTangent w ↔ IsLieComb (fun _ : Fin 1 => 0) (fun _ => w) 1 := by
  have e : prodPts (fun _ : Fin 1 => (0 : R)) (fun _ => w) = Chart.spMap (scaleD 0) ≫ w := by simp [prodPts]
  have e₁ : scaleD (0 : R) = (Algebra.ofId R (DualNumber R)).comp (fstD R) := by
    refine DualNumber.algHom_ext ?_
    ext <;> simp [scaleD]
  have e₂ : (fstD R).comp (scaleD (0 : R)) = fstD R := by
    refine DualNumber.algHom_ext ?_
    simp [scaleD]
  rw [← isTan_iff, isLieComb_iff, e]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [e₁, ← Chart.spMap_comp, Category.assoc, h, comp_one']
  · rw [Chart.IsTan, ← e₂, ← Chart.spMap_comp, Category.assoc, ← h, comp_one']

theorem isLieBasis_of_red [IsLocalRing R] [Smooth G.hom] [IsLocalHom f] {n : ℕ} {w v : Fin n → (epsR R ⟶ G)}
    (hw : IsLieBasis w) (hv : ∀ i, IsTangent (v i))
    (e : ∀ i, spMap (dualMapR f) ≫ (v i).left = spMap (dualMapR f) ≫ (w i).left) : IsLieBasis v := by
  obtain ⟨x, hx, hxw⟩ := chart_of_basis hw
  have key : ∀ (u : Fin n → (epsR R ⟶ G)) (hu : ∀ i, Chart.IsTan (u i)) (t : epsR R ⟶ G) (ht : Chart.IsTan t) (c : Fin n → R),
      IsLieComb c u t ↔ tcoord hx t ht = ∑ i, c i • tcoord hx (u i) (hu i) := fun u hu t ht c => by
    obtain ⟨h, e⟩ := prodPts_tan hx c u hu
    rw [isLieComb_iff]
    exact ⟨fun hc => by subst hc; exact e, fun hc => tan_ext hx ht h (hc.trans e.symm)⟩
  have tw : ∀ i, Chart.IsTan (w i) := fun i => (isTan_iff _).2 (hw.1 i)
  have tv : ∀ i, Chart.IsTan (v i) := fun i => (isTan_iff _).2 (hv i)
  have cw : ∀ i, tcoord hx (w i) (tw i) = Pi.single i 1 := fun i => tcoord_eq hx _ _ _ (hxw i)
  have kw : ∀ (t : epsR R ⟶ G) (ht : Chart.IsTan t), IsLieComb (tcoord hx t ht) w t := fun t ht =>
    (key w tw t ht _).2 (by simp only [cw]; exact (sum_single _).symm)
  let N : Matrix (Fin n) (Fin n) R := Matrix.of fun i => tcoord hx (v i) (tv i)
  choose bar hbar using exists_bar (G := G) f
  have gp := isGrpPullback_pullback G (spMap f)
  have hb := isLieBasis_baseChange f gp hw (v' := fun i => bar (w i)) (fun i => hbar _)
  have hN : N.map f = 1 := by
    ext i k
    have a := (lieComb_baseChange R A f G _ _ gp n w (v i) _ (fun i => bar (w i)) (bar (w i)) (fun i => hbar _)
      (kw _ (tv i))).1 ((hbar _).trans (e i).symm)
    have a' := (lieComb_baseChange R A f G _ _ gp n w (w i) _ (fun i => bar (w i)) (bar (w i)) (fun i => hbar _)
      (kw _ (tw i))).1 (hbar _)
    have := congrFun ((hb.2 _ (hb.1 i)).unique a a') k
    rw [cw] at this
    refine this.trans ?_
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  have hdet : IsUnit N.det := by
    refine IsUnit.of_map f _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN, Matrix.det_one]
    exact isUnit_one
  have hsum : ∀ c : Fin n → R, ∑ i, c i • tcoord hx (v i) (tv i) = Matrix.vecMul c N := fun c =>
    (Matrix.vecMul_eq_sum c N).symm
  refine ⟨hv, fun t ht => ?_⟩
  have ht' := (isTan_iff _).2 ht
  simp only [key v tv t ht', hsum]
  refine ⟨Matrix.vecMul (tcoord hx t ht') N⁻¹, ?_, fun c hc => ?_⟩
  · simp only [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  · rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end Lie

section ThetaShiftProofs

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcQ GlobalTheory.FormalPoint GlobalTheory.ConstTan
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

theorem genRelR_of_tr {R R₀ S : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] [CommRing S]
    [IsLocalRing S] {I : Ideal R} {D : DegData R I} {D₀ : DegPre R₀} {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    {w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)} (hw : w.IsGen) {e : D₀.X → D.toPre.X}
    {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D P G) {T : Over (Sp R)} {T₀ : Over (Sp R₀)} {h : T.left ⟶ T₀.left} {g : GtPt D.toPre T}
    {g₀ : GtPt D₀ T₀} (H : Tr w e h g g₀) {n : ℕ} {r : Sp S ⟶ T.left} {y : Sp S ⟶ (thickObj R I n G).left}
    (hy : HasCoords U n g r y) {k : Sp S ⟶ T₀.left} (hk : r ≫ h = k) (x : D₀.X) :
    GenRelR w (LB.pullGen _ _ _ ((U.gt n).t (e x)) y) (LB.pullGen _ _ _ (g₀.s x) k) := by
  subst hk
  obtain ⟨h₁, h₂⟩ := (hasCoords_iff U n g r y).1 hy
  have hp := (TorusCoord.comp_eq_of_left g.b (U.gt n).pG r y h₁.symm).1 (e x)
  refine ConstPoint.genRelR_of_val hw D.toPre.P.isLB D₀.P.isLB (pullGen_isGen _ _ _ _ ((U.gt n).t_gen _) y)
    (pullGen_isGen _ _ _ _ (g₀.isGen x) _) (fun k => ?_) fun J J' hJ hJ' => ?_
  · rw [← hp, Category.assoc, (H x).1, Category.assoc]
  · have v := (H x).2 _ r _ J J' hJ hJ'
    simp only [hp] at v
    refine (val_pull hJ (g₀.s x) _ _).trans ?_
    rw [val_pull hJ']
    simp only [Category.id_comp]
    rw [h₂ _ _ J' hJ']
    exact v

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

abbrev cstE (A : Type) [CommRing A] : (epsR (PowerSeries A)).left ⟶ (epsR A).left :=
  spMap (dualMapR (PowerSeries.C (R := A)))

abbrev redE (A : Type) [CommRing A] : (epsR A).left ⟶ (epsR (PowerSeries A)).left :=
  spMap (dualMapR (PowerSeries.constantCoeff (R := A)))

theorem redE_cstE (A : Type) [CommRing A] : redE A ≫ cstE A = 𝟙 _ := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (Spec.map_id _))
  refine RingHom.ext fun x => ?_
  ext <;> simp

omit [IsNoetherianRing A] in
theorem lieImg_of_tr {ν : GtPt a.D₀ (epsR A)} {g : GtPt W.P.D.toPre (epsR (PowerSeries A))}
    {v : epsR (PowerSeries A) ⟶ W.t.G} (h : Tr W.w W.e (cstE A) g ν) (hv : IsPointOf W.P.U.toUnifPre g v) :
    LieImg W ν v := by
  intro n ρ κ vn h₁ h₂ h₃ h₄ _ h₆ x
  have hI : (Ideal.span {PowerSeries.X} : Ideal (PowerSeries A)) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_unit
  have : IsLocalRing (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)) :=
    isLocalRing_quotient_pow hI n
  have := isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
  refine genRelR_of_tr W.spec.2.1 W.P.U.toUnifPre h (hv n _ (spMap ρ) vn h₆) ?_ x
  refine (spMap_comp _ _).symm.trans (congrArg spMap ?_)
  rw [eq_dualMapR ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A))) κ h₃ h₄]
  exact eq_dualMapR _ _ (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (h₁ _))
    ((congrArg ρ (dualMapR_eps _)).trans h₂)

variable (hG : GlobalFnsSt)
include hG

theorem exists_tr {ν : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) :
    ∃ g, Tr W.w W.e (cstE A) g ν ∧ IsPointOf W.P.U.toUnifPre g v := by
  obtain ⟨g, hg⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν
  have : Module.Finite (PowerSeries A) (DualNumber (PowerSeries A)) :=
    inferInstanceAs (Module.Finite (PowerSeries A) (PowerSeries A × PowerSeries A))
  have := isAdicComplete_map_of_finite (Ideal.span {(PowerSeries.X : PowerSeries A)}) (DualNumber (PowerSeries A))
  have := isLocalRing_dual (PowerSeries A)
  obtain ⟨v', hv', -⟩ := existsUnique_isPointOf W.P.U.toUnifPre g
  obtain rfl : v' = v := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W ν).1.unique (lieImg_of_tr W hg hv') hv
  exact ⟨g, hg, hv'⟩

omit hG [IsLocalRing A] [IsNoetherianRing A] in
theorem exists_level_zero (v : epsR (PowerSeries A) ⟶ W.t.G) :
    ∃ y : (epsR A).left ⟶ (thickObj (PowerSeries A) (Ideal.span {PowerSeries.X}) 0 W.t.G).left,
      y ≫ (fstG (Ideal.span {PowerSeries.X}) 0 W.t.G).left = redE A ≫ v.left := by
  let q : PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (0 + 1) →+* A :=
    Ideal.Quotient.lift _ (PowerSeries.constantCoeff (R := A)) fun r hr => by
      rw [zero_add, pow_one, Ideal.mem_span_singleton] at hr
      exact PowerSeries.X_dvd_iff.1 hr
  have hq : spMap q ≫ thick (PowerSeries A) (Ideal.span {PowerSeries.X}) 0 =
      spMap (PowerSeries.constantCoeff (R := A)) := (spMap_comp _ q).symm
  refine ⟨pullback.lift (redE A ≫ v.left) ((epsR A).hom ≫ spMap q) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, Over.w v, Category.assoc, hq]
  exact LieCombBaseChange.dualMap_over _

theorem eq_of_red {ν ν' : GtPt a.D₀ (epsR A)} {v v' : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v)
    (hv' : LieImg W ν' v') (e : redE A ≫ v.left = redE A ≫ v'.left) : ν = ν' := by
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg', hp'⟩ := exists_tr W hG hv'
  obtain ⟨y, hy⟩ := exists_level_zero W v
  obtain ⟨h₁, h₂⟩ := (hasCoords_iff _ _ _ _ _).1 (hp 0 _ _ y hy)
  obtain ⟨h₁', h₂'⟩ := (hasCoords_iff _ _ _ _ _).1 (hp' 0 _ _ y (hy.trans e))
  exact hg.inj hg' (redE A) (redE_cstE A) (h₁.symm.trans h₁') fun x z J hJ => (h₂ x z J hJ).symm.trans (h₂' x z J hJ)

theorem exists_red (w : epsR (PowerSeries A) ⟶ W.t.G) :
    ∃ ν v, LieImg W ν v ∧ redE A ≫ v.left = redE A ≫ w.left := by
  obtain ⟨y, hy⟩ := exists_level_zero W w
  let T : Over (Sp (PowerSeries A)) := Over.mk (redE A ≫ (epsR (PowerSeries A)).hom)
  obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (W.P.U.gt 0) (T := T) y (by
    refine Eq.trans (congrArg (y ≫ ·) (Over.w (fstG (Ideal.span {PowerSeries.X}) 0 W.t.G)).symm) ?_
    rw [← Category.assoc, hy, Category.assoc, Over.w]; rfl)
  obtain ⟨ν, hν⟩ := exists_tr_up hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (T := T) (epsR A).hom (by
    have e₁ := LieCombBaseChange.dualMap_over (PowerSeries.C (R := A))
    show _ = (redE A ≫ _) ≫ _
    rw [Category.assoc, ← e₁, ← Category.assoc]
    exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (redE_cstE A).symm)) ξ
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W ν).1
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  have P := Tr.cancel W.spec.1 W.e.surjective hg hν (Over.homMk (redE A) rfl) (redE_cstE A)
  have hc : HasCoords W.P.U.toUnifPre 0 g (redE A) y :=
    ⟨hξ.1.symm.trans P.1, fun x => corr_trans W.P.D.toPre.P.isLB (corr_symm (hξ.2 x)) (P.2 x)⟩
  exact ⟨ν, v, hv, (hp.comp_fstG_eq hc).symm.trans hy⟩

theorem exists_act {ν : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E) :
    ∃ ν', LieImg W ν' (v ≫ W.t.act.act x) := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨ν', hν'⟩ := TorusModel.exists_isSmulPt hG a.oa x ν
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  exact ⟨ν', lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)⟩

end ThetaShiftProofs

end GlobalTheory.ConstLie

namespace GlobalTheory.ConstLie

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped MonObj

theorem exists_const_basis : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ (g : ℕ) (e : Fin g → Out.GtPt a.D₀ (epsR A)) (v : Fin g → (epsR (PowerSeries A) ⟶ W.t.G)) (M : 𝓞 E → Matrix (Fin g) (Fin g) A), (∀ i, GtTanR (e i) ∧ LieImg W (e i) (v i)) ∧ IsLieBasis v ∧ (∀ ν, GtTanR ν → ∃! cf : Fin g → A, GtComb cf e ν) ∧ ∀ (x : 𝓞 E) i, IsLieComb (fun k => PowerSeries.C (R := A) (M x i k)) v (v i ≫ W.t.act.act x) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W
  have := W.P.U.smooth
  obtain ⟨n, w, hw⟩ := Chart.exists_isLieBasis W.t.G this
  choose e v hv hr using fun i => exists_red W hG (w i)
  have hb : IsLieBasis v := by
    have : IsLocalHom (PowerSeries.constantCoeff (R := A)) := ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.2 h⟩
    refine isLieBasis_of_red (PowerSeries.constantCoeff (R := A)) hw (fun i => ?_) hr
    obtain ⟨o, ho⟩ := exists_gtComb (D := a.D₀) (m := 0) Fin.elim0 Fin.elim0
    obtain ⟨ν, hν⟩ := exists_gtComb (fun _ : Fin 1 => 0) (fun _ => e i)
    obtain ⟨t, ht, -⟩ := (ex ν).1
    have h₀ := (lin 0 _ _ o Fin.elim0 1 (fun j => j.elim0) ho).2 ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    have h₁ := (lin 1 _ _ ν (fun _ => v i) t (fun _ => hv i) hν).1 ht
    obtain rfl : ν = o := eq_of_red W hG ht h₀
      (red_eq_of_comb _ h₁ ((isTangent_iff_comb _).1 (hw.1 i)) (fun _ => by simp) fun _ => hr i)
    obtain rfl : t = 1 := (ex ν).1.unique ht h₀
    exact (isTangent_iff_comb _).2 (by simpa only [map_zero] using h₁)
  have hu : ∀ ν, GtTanR ν → ∃! cf : Fin n → A, GtComb cf e ν := fun ν hν => by
    obtain ⟨t, ht, -⟩ := (ex ν).1
    obtain ⟨cf, hc, hu⟩ := hb.2 t (((ex ν).2 t ht).1 hν)
    obtain ⟨ν', hν'⟩ := exists_gtComb (fun i => PowerSeries.constantCoeff (cf i)) e
    obtain ⟨t', ht', -⟩ := (ex ν').1
    obtain rfl : ν = ν' := eq_of_red W hG ht ht'
      (red_eq_of_comb _ hc ((lin n _ e ν' v t' hv hν').1 ht') (fun i => by simp) fun _ => rfl)
    refine ⟨_, hν', fun cf' h' => funext fun i => ?_⟩
    rw [← hu _ ((lin n _ e ν v t hv h').1 ht)]
    simp
  have hM : ∀ (x : 𝓞 E) i, ∃ m : Fin n → A,
      IsLieComb (fun k => PowerSeries.C (R := A) (m k)) v (v i ≫ W.t.act.act x) := fun x i => by
    obtain ⟨ν', hν'⟩ := exists_act W hG (hv i) x
    have := W.t.act.hom x
    have ht : IsTangent (v i ≫ W.t.act.act x) :=
      (Chart.isTan_iff _).1 (Chart.isTan_comp ((Chart.isTan_iff _).2 (hb.1 i)) _)
    obtain ⟨m, hm, -⟩ := hu ν' (((ex ν').2 _ hν').2 ht)
    exact ⟨m, (lin n m e ν' v _ hv hm).1 hν'⟩
  choose M hM using hM
  exact ⟨n, e, v, fun x => Matrix.of (M x), fun i => ⟨((ex _).2 _ (hv i)).2 (hb.1 i), hv i⟩, hb, hu, hM⟩

end GlobalTheory.ConstLie
