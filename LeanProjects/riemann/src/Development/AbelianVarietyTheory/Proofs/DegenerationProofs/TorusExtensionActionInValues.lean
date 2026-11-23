import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Ex.GtValues

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem gtAct_pt (hG : GlobalFnsSt) {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L y J) (oa : D.OAct O) (a : O)
    {u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)}
    (hu : TorusExt.IsRos D.P.L _ _ u) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ,
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ,
      val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun u χ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine ⟨fun h => ⟨h.1, fun χ => (val_corr hJ (h.2 _ hu.1 hu.2 χ) _).symm.trans (vv _ χ)⟩,
    fun ⟨hb, hv⟩ => ⟨hb, fun u' hu' u₀ χ => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu' _)) (g'.isGen χ) hJ
      ((vv u' χ).trans ((congrArg₂ (· * ·) rfl
        (TorusExt.IsRos.unique hG D.P.isAb D.P.isLB ⟨hu', u₀⟩ hu hJ _ _)).trans (hv χ).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
    (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
  rw [prod_gt, TorusExt.cPoint_smul oa, hb]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end

theorem gtAct_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  intro hG R _ _ D F _ _ N ν O _ _
  refine ⟨fun oa x => ?_, fun oa x ρ ⟨u, hu, u₀, hρ⟩ g g' v v' h h' => ?_⟩
  · have := oa.hom x
    have := oa.hom (star x)
    have hr := oa.rosati (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    exact ⟨_, u, hu, u₀, fun _ _ => rfl⟩
  · let y : Sp F := (⊥ : PrimeSpectrum F)
    have hJ := good ν y
    obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
    obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
    rw [gtAct_pt hG hJ oa x ⟨hu, u₀⟩, ν.eX.surjective.forall]
    refine and_congr ?_ (forall_congr' fun χ => ?_)
    · rw [← a, ← a', actV, ν.eA.eq_symm_apply]
    · have e := b (ν.eX.symm (star x • ν.eX χ))
      rw [ν.eX.apply_symm_apply] at e
      have r : toStk y (ρ (N.c χ) v.b) = (val₂ u y ν.J (cP D _ (ν.eX χ)) g.b).val := by
        rw [hρ, toStk_vF _ _ hJ, c_eq, a]; rfl
      rw [← (toStk y).injective.eq_iff, map_mul, r, ← e, ← b', ← Units.val_inj, Units.val_mul]
      rfl

end GlobalTheory.Relabel
end
