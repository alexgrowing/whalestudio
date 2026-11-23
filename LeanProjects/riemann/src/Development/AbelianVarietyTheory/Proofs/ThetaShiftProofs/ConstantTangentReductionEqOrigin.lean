import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanRed
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem comp_gtφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) (hb : ρ ≫ b = b') (χ : D.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT D T b χ k = DegPre.gtφT D T' b' χ k := by
  subst hb
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (comp_cP D ρ χ)))
  · exact congrArg (fun q => q.left) (comp_cP D ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one ρ)

theorem val_eq_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y Y' : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {ψ : K → (Y ⟶ B₀)} {ψ' : K → (Y' ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {u : LB.Gen (LB.LinComb M₀ ψ ε)} {u' : LB.Gen (LB.LinComb M₀ ψ' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (hu : u.IsGen) (hu' : u'.IsGen) {h : Sp A ⟶ Y} {h' : Sp A' ⟶ Y'} (H : GenRelR w t (LB.pullGen _ _ _ u h))
    (H' : GenRelR w t' (LB.pullGen _ _ _ u' h')) (q : Sp A ⟶ Sp A') (hq : ∀ k, q ≫ pt' k = pt k)
    {Z : Scheme.{0}} (r : Z ⟶ Sp A) (z : Z)
    (hv : ∀ J, Good M₀ z J → val u' ((r ≫ q) ≫ h') z J = val u (r ≫ h) z J) {J'} (hJ' : Good M z J') :
    val t' (r ≫ q) z J' = val t r z J' := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists M₀ hM₀ z
  have hw' := (isGen_iff w).1 hw
  have e := CubTransport.val_pmaps (fun k => (H.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (pullGen_isGen _ _ _ _ hu h) H) r hJ hJ'
  have e' := CubTransport.val_pmaps (fun k => (H'.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht' (pullGen_isGen _ _ _ _ hu' h') H') (r ≫ q) hJ hJ'
  rw [val_pull hJ, Category.comp_id] at e e'
  rw [hv J hJ, e] at e'
  simp only [Category.assoc r q, hq] at e'
  exact (mul_left_cancel e').symm

theorem corr_pull_of_valR {A F : Type} [CommRing A] [IsLocalRing A] [Field F] (p : A →+* F) [IsLocalHom p]
    {B : Scheme.{0}} {M : LB B} (hM : M.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp A ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (t' : LB.Gen (LB.LinComb M pt' ε))
    (hp : ∀ k, spMap p ≫ pt' k = pt k)
    (hv : ∀ j, ⊤ ≤ LB.wchart M pt' j → p (valR (𝟙 (Sp A)) (LB.wchart M pt' j) (t'.s j).val) =
      valR (𝟙 (Sp F)) (LB.wchart M pt j) (t.s j).val) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t' (spMap p)) t := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain rfl : y = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hc : spMap p (cpt F) = cpt A := IsLocalRing.comap_closedPoint p
  rw [val_pull hJ, Category.id_comp, val_of t' _ _ J (fun k => J (pt k)) (fun k => by rw [hp]),
    val_of t _ _ J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  have m : ⊤ ≤ (𝟙 (Sp F)) ⁻¹ᵁ LB.wchart M pt (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => hJ (pt k))
  have m' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M pt' (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => by
      have := hJ (pt k)
      rw [← hc]
      exact (congrArg (fun q => q (cpt F) ∈ M.U (J (pt k))) (hp k)).mpr this)
  have m'' := FormalValue.top_le_comp m' (spMap p)
  have e := FormalValue.valR_spMap p _ _ m' (t'.s (fun k => J (pt k))).val
  rw [Category.comp_id] at m'' e
  refine Units.ext ?_
  exact (toStkA_valR _ _ _ m'' _).symm.trans ((congrArg _ (e.trans (hv _ m'))).trans (toStkA_valR _ _ _ m _))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ g h z₀ ν Ξ v g₁ hd ht hf
  haveI := isLocalRing_dual ℂ
  haveI := isLocalRing_dual ℂ⟦X⟧
  let p : DualNumber ℂ⟦X⟧ →+* ℂ⟦X⟧ := (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom
  let p₀ : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  haveI : IsLocalHom p₀ := ⟨fun x hx => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩
  obtain ⟨h₁, h₂, -⟩ := hd
  have h₁' := h₁.1
  simp only [map_zero] at h₁' h₂
  have sq : spMap p ≫ spMap constEps = spMap (PowerSeries.C (R := ℂ)) ≫ spMap p₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => fst_dualMapR _ x)
  let ρ₀ : TF (R := ℂ) ℂ ⟶ epsR ℂ := Over.homMk (spMap p₀) (by
    show spMap p₀ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap (FractionRing ℂ) ℂ) ≫ spMap (algebraMap ℂ (FractionRing ℂ))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl)
  let ρ : selfR ⟶ epsR ℂ⟦X⟧ := Over.homMk (spMap p) (by
    show spMap p ≫ spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)
  have hb₀ : ρ₀ ≫ ν.b = (Λ.ex0 0).b := Over.OverMorphism.ext h₁'
  have hb : ρ ≫ g₁.b = (Ξ.g 0).b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (spMap p ≫ ·) ((ht 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ν.b.left) sq).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) h₁').trans ((Ξ.g_rel 0 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ x, LB.Gen.Corr a.D₀.P.L _ _ _ _ (LB.pullGen a.D₀.P.L _ _ (ν.s x) (spMap p₀)) ((Λ.ex0 0).s x) :=
    fun x => corr_pull_of_valR p₀ a.D₀.P.isLB _ _ (comp_gtφT a.D₀ ρ₀ ν.b _ hb₀ x) fun j hj =>
      (congrArg p₀ (h₂ x j hj)).trans ((TrivSqZeroExt.fst_add _ _).trans (add_zero _))
  have hv : ∀ y (Z : Scheme.{0}) (r : Z ⟶ Sp ℂ⟦X⟧) (z : Z) J', Good W.P.D.toPre.P.L z J' →
      val (g₁.s y) (r ≫ spMap p) z J' = val ((Ξ.g 0).s y) r z J' := fun y Z r z J' hJ' => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine val_eq_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g 0).isGen _) (g₁.isGen _)
      ((Λ.ex0 0).isGen x) (ν.isGen x) (Ξ.g_rel 0 x) (ht x) (spMap p) (comp_gtφT W.P.D.toPre ρ g₁.b _ hb _) r z
      (fun J hJ => ?_) hJ'
    have e : (r ≫ spMap p) ≫ spMap constEps = (r ≫ spMap (PowerSeries.C (R := ℂ))) ≫ spMap p₀ := by
      rw [Category.assoc, sq, Category.assoc]
    exact (congrArg (fun q => val (ν.s x) q z J) e).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (hc x) _))
  let I : Ideal ℂ⟦X⟧ := (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
  haveI : IsAdicComplete I ℂ⟦X⟧ := by
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine hom_ext_of_isHausdorff I fun e => ?_
  obtain ⟨xe, hxe⟩ := FormalValue.exists_lift_thick (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}) W.t.G
    (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (ρ ≫ v).left (Over.w (ρ ≫ v)) e
  have hs : spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) = adicLevelι I (e + 1) ≫ spMap p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : idealEps ^ (e + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) := fun s hs => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (mem_idealEps_pow hs).1
  have H₁ := hf.hasCoords _ hk (xe := xe) (hxe.trans (by rw [hs, Category.assoc]; rfl))
  rw [hs] at H₁
  obtain ⟨k₁, k₂⟩ := (FormalPoint.hasCoords_iff W.P.U.toUnifPre e g₁ _ xe).1 H₁.2
  have H₂ : FormalPoint.HasCoords W.P.U.toUnifPre e (Ξ.g 0) (adicLevelι I (e + 1)) xe :=
    (FormalPoint.hasCoords_iff W.P.U.toUnifPre e _ _ xe).2
      ⟨k₁.trans ((Category.assoc _ _ _).trans (congrArg (fun q => adicLevelι I (e + 1) ≫ q.left) hb)),
        fun y z J hJ => (k₂ y z J hJ).trans (hv y _ _ z J hJ)⟩
  exact hxe.symm.trans ((Ξ.x_pt 0).comp_fstG_eq H₂)

end GlobalTheory.ConstTanRed
