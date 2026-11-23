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
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTanFormal

theorem corr_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {pt₀ : K → (Y₀ ⟶ B₀)} {g : LB.Gen (LB.LinComb M pt ε)} {t : LB.Gen (LB.LinComb M pt' ε)}
    {ν : LB.Gen (LB.LinComb M₀ pt₀ ε)} (hg : g.IsGen) (ht : t.IsGen) (hν : ν.IsGen) {r : Sp A' ⟶ Sp A}
    {κ : Sp A ⟶ Y₀} {κ' : Sp A' ⟶ Y₀} (hκ : r ≫ κ = κ') (hp : ∀ k, pt' k = r ≫ pt k)
    (h : GenRelR w g (LB.pullGen _ _ _ ν κ)) (h' : GenRelR w t (LB.pullGen _ _ _ ν κ')) :
    LB.Gen.Corr M _ _ _ _ t (LB.pullGen M _ _ g r) := by
  have hw' := (isGen_iff w).1 hw
  have H := ConstGrp.pmaps_of_genRelR hw' hM hM₀ hg (DVR.pullGen_isGen _ _ _ _ hν κ) h
  have H' := ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ hν κ') h'
  refine corr_of_val hM fun y J' hJ' => ?_
  choose J hJ using fun ψ : Sp A' ⟶ B₀ => exists_chart hM₀ (ψ y)
  have v := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm) H r hJ hJ'
  have v' := CubTransport.val_pmaps (fun k => (h'.1 k).trans (Category.id_comp _).symm) H' (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.comp_id, hκ] at v
  rw [val_pull hJ, Category.comp_id, Category.id_comp] at v'
  rw [val_pull hJ', Category.id_comp]
  simp only [Category.id_comp, hp] at v'
  exact mul_left_cancel (v'.symm.trans v)

theorem dualMapR_surjective {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} (h : Function.Surjective φ) :
    Function.Surjective (dualMapR φ) := fun a => by
  obtain ⟨x, hx⟩ := h a.fst
  obtain ⟨y, hy⟩ := h a.snd
  exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by ext <;> simp [hx, hy]⟩

theorem ker_dualMapR_mk {R : Type} [CommRing R] (I : Ideal R) :
    RingHom.ker (dualMapR (Ideal.Quotient.mk I)) ≤ I.map (algebraMap R (DualNumber R)) := fun a ha => by
  have h₁ : a.fst ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.1 ha))
  have h₂ : a.snd ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.snd (RingHom.mem_ker.1 ha))
  have e : a = algebraMap R (DualNumber R) a.fst + algebraMap R (DualNumber R) a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W g ex₀ z₀ ν v g₁ hD hT
  refine FormalValue.isFormalPt_of_surjective _ fun e => ?_
  let I : Ideal ℂ⟦X⟧ := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsLocalRing (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := isLocalRing_dual (ℂ⟦X⟧ ⧸ I ^ (e + 1))
  have := isLocalRing_dual ℂ⟦X⟧
  let ρ : DualNumber ℂ⟦X⟧ →+* DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick ℂ⟦X⟧ I e = spMap ρ ≫ (epsR ℂ⟦X⟧).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)
  let xe : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj ℂ⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick ℂ⟦X⟧ I e)).obj (Out.thickObj ℂ⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR ℂ⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ : spMap ρ ≫ spMap constEps = spMap (ρ.comp constEps) := (Spec.map_comp _ _).symm
  have h' := hD.2.2 e ρ (ρ.comp constEps) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) hx
  have hp : ∀ x k, xe ≫ W.P.D.toPre.Oφ (W.P.U.gt e).pG (W.e x) k =
      spMap ρ ≫ Out.DegPre.gtφT W.P.D.toPre (epsR ℂ⟦X⟧) g₁.b (W.e x) k := fun x k => by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine ((h' x).1 k).trans ?_
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT x).1 k).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hx'.trans ?_)
      · refine congrArg (xe ≫ ·) ?_
        fin_cases k <;> exact Over.w _
      · refine congrArg (spMap ρ ≫ ·) ?_
        fin_cases k <;> exact (Over.w _).symm
  refine ⟨_, inferInstance, ρ, xe, dualMapR_surjective Ideal.Quotient.mk_surjective, ?_, hx, hp 0 2, fun y => ?_⟩
  · rw [idealEps, ← Ideal.map_pow]
    exact ker_dualMapR_mk _
  · obtain ⟨x, rfl⟩ := W.e.surjective y
    exact corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g₁.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x) hκ (hp x) (hT x) (h' x)

end GlobalTheory.ConstTanFormal
