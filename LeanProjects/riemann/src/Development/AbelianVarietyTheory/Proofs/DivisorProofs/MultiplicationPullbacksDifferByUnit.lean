import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.bijective_appTop {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    Function.Bijective T.G.hom.appTop.hom := by
  have hd : IsDiscreteValuationRing W := T.cdvr.1
  have := T.U.smooth
  have := T.U.separated
  have := C.semi.quasiCompact
  have : QuasiCompact T.G.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) T.cart.1 this
  exact GlobalFunctionsDvrGeneric.bij_of_generic T.G
    (GlobalFunctionsDvrPowers.bijective_of_iso T.U.gen (GlobalTheory.allSixLaws.1.globalFns _ T.A.A T.A.isAb))

theorem Trait.exists_unit_scal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (c : Γ(T.G.left, ⊤)ˣ) :
    ∃ v : Wˣ, scal T.G.hom (v : W) = c.val := by
  let e : W ≃+* Γ(T.G.left, ⊤) := RingEquiv.ofBijective
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)
    (T.bijective_appTop.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv))
  exact ⟨Units.map e.symm.toMonoidHom c, e.apply_symm_apply c.val⟩

theorem Trait.carries_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  intro R _ _ _ _ D C W _ _ _ T m u hu uG huG b σ' σ hcar σ₂ σ'' h₂ h''
  have hm := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  obtain ⟨a, ha, hP⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move C.P.L.isLB T.U.LG.isLB T.ℓ ((isGen_iff _).1 T.ℓ_gen)
    (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![𝟙 T.G.left, (mulA T.G m).left]
    ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] T.β (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact hm) u hu
  obtain ⟨c, hc⟩ := GlobalTheory.ZM.Coord.exists_global_unit (DVR.linComb_isLB _ T.U.LG.isLB _ _) ha huG
  obtain ⟨v, hv⟩ := T.exists_unit_scal c
  refine ⟨v, fun Z r z J J' hJ hJ' => ?_⟩
  have e₁ : (r ≫ T.β) ≫ (mulA C.G m).left = (r ≫ (mulA T.G m).left) ≫ T.β := by
    rw [Category.assoc, Category.assoc, hm]
  have hp : val u (r ≫ T.β) z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2) *
      (gw T.ℓ (r ≫ (mulA T.G m).left) z (J ((r ≫ (mulA T.G m).left) ≫ T.β)) (J' (r ≫ (mulA T.G m).left)))⁻¹) *
      val a r z J' := by
    refine (hP Z r z _ _ (fun k => ?_) (fun k => hJ' (r ≫ _))).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ T.β) ≫ 𝟙 _)
      · have := hJ ((r ≫ T.β) ≫ (mulA C.G m).left)
        exact (congrArg (fun q => q z ∈ C.P.L.L.U (J ((r ≫ T.β) ≫ (mulA C.G m).left))) e₁).mp this
    · refine congrArg (· * val a r z J') ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁, zpow_natCast, zpow_neg, pow_one]
  have hq : val a r z J' = gm r z ⊤ c * val uG r z J' := by
    have hm' := hJ'.mem ![𝟙 T.G.left, (mulA T.G m).left] r
    exact (congrArg (gm r z _) (hc _)).trans ((map_mul _ _ _).trans (congrArg (· * val uG r z J') (gm_res r z _ hm' _)))
  have hs : gs (r ≫ (mulA T.G m).left) z ⊤ (scal T.G.hom b) = gs r z ⊤ (scal T.G.hom b) := by
    refine (gs_pull r (mulA T.G m).left z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ?_)
    show ((mulA T.G m).left ≫ T.G.hom).appTop.hom _ = _
    rw [Over.w]; rfl
  have hbv : gs r z ⊤ (scal T.G.hom (b * v)) = gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val := by
    rw [← gs_unit r z ⊤ trivial, ← hv, ← gs_mul r z ⊤ trivial, scal, scal, scal, map_mul, map_mul]
  rw [h₂ Z r z J hJ, h'' Z r z J' hJ', hcar Z _ z J J' hJ hJ', hp, hq, hs, hbv, Category.comp_id, pow_one]
  generalize gw T.ℓ (r ≫ (mulA T.G m).left) z _ _ = g
  simp only [Units.val_mul]
  linear_combination (gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2)).val *
    (val uG r z J').val * sval σ' (r ≫ (mulA T.G m).left) z J') * g.inv_mul

end GlobalTheory.Mum
