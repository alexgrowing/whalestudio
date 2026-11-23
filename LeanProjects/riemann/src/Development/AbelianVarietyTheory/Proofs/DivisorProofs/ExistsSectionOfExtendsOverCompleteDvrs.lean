import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianBaseChangeNormalDomainGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SecExtend

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left}

theorem pullS_homMk_id {F : Type} [CommRing F] {x : Sp F ⟶ S} (t : SecAt G L x) :
    VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) t = t := by
  have e : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := Over.OverMorphism.ext rfl
  refine ThetaRuleCompare.sec_ext fun j => fn_ext fun y hy => ?_
  refine (ThetaRuleCompare.gs_pullS _ t (𝟙 _) y j hy).trans ?_
  rw [e, MonoidalCategory.id_whiskerRight, Over.id_left, Category.id_comp]

theorem eq_pullS_of_cast {F : Type} [CommRing F] {x₁ x₂ : Sp F ⟶ S} (h : x₁ = x₂)
    (t : SecAt G L x₁) (u : SecAt G L x₂) (E : SecM.ofSec G u = SecM.ofSec G (h ▸ t)) :
    u = VVRank.pullS G _ (Over.homMk (𝟙 _) (by simp [h]) : Over.mk x₂ ⟶ Over.mk x₁) t := by
  subst h
  rw [pullS_homMk_id]
  exact ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val E) j

theorem gs_appLE {Z Y : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (O : Z.Opens) (h : O ≤ g ⁻¹ᵁ U) (b : Γ(Y, U))
    (z : Z) (hz : z ∈ O) : gs (𝟙 Z) z O ((g.appLE U O h).hom b) = gs g z U b :=
  (gs_res (𝟙 Z) z h hz ((g.app U).hom b)).trans
    ((gs_pull (𝟙 Z) g z U (h hz) b).trans (by rw [Category.id_comp]))

theorem exists_sec_of_extends : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  intro S G _ L hL hG R _ _ _ _ _ χ θ H
  obtain ⟨hLN, hN, hPre, hInj⟩ := GlobalTheory.T.semiAbelian_baseChange_normal_domain_generic_fibre S G hG R χ
  let hK : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ :=
    Over.homMk (spMap (algebraMap R (FractionRing R))) rfl
  let fK : ∀ j, Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left,
      (hK ▷ G).left ⁻¹ᵁ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j) := fun j =>
    ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left.presheaf.map
      (homOfLE (ThetaRuleCompare.chart_ge hK j)).op).hom (θ.f j)
  have ext : ∀ j, ∃ s : Γ((Over.mk χ ⊗ G).left, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j),
      ((hK ▷ G).left.app _).hom s = fK j := fun j =>
    GenericExtend.exists_app_eq (hK ▷ G).left hInj _ (fK j) (GlobalTheory.T.extendsAt_of_codim_le_one_over_completeDVRs S G hG R χ _ (fK j) (by
      intro V _ _ _ hV φ φK h hφ
      obtain ⟨σV, E⟩ := H V hV φ φK h hφ
      let hφR : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap φ) rfl
      let hVV : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ) :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      let B : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
          Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) := Over.homMk (spMap φK) h
      have E' := eq_pullS_of_cast G h _ _ E
      have E'' : VVRank.pullS G _ hVV σV = VVRank.pullS G _ B θ := by
        refine E'.trans ((ThetaRuleCompare.pullS_comp _ _ θ).trans ?_)
        congr 1
      refine ⟨((Over.mk (spMap φ ≫ χ) ⊗ G).left.presheaf.map
        (homOfLE (ThetaRuleCompare.chart_ge hφR j)).op).hom (σV.f j), fun O h₁ h₂ => fn_ext fun x hx => ?_⟩
      have hx₁ := h₁ hx
      have hx₂ := h₂ hx
      have hxc : x ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ))).U j :=
        ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hVV j (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hφR j hx₁)
      rw [gs_appLE _ _ _ _ _ x hx, gs_appLE _ _ _ _ _ x hx, gs_res _ x _ hx₁, gs_res _ x _ hx₂]
      have a₁ := ThetaRuleCompare.gs_pullS hVV σV (𝟙 _) x j hxc
      have a₂ := ThetaRuleCompare.gs_pullS B θ (𝟙 _) x j hxc
      rw [Category.id_comp] at a₁ a₂
      rw [← a₁, ← a₂, E'']))
  choose s hs using ext
  have hv : ∀ j (w : (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left),
      (hK ▷ G).left w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j →
      gs (𝟙 _ ≫ (hK ▷ G).left) w _ (s j) = gs (𝟙 _) w _ (θ.f j) := fun j w hw =>
    (gs_pull (𝟙 _) _ w _ hw _).symm.trans ((congrArg (gs (𝟙 _) w _) (hs j)).trans
      (gs_res (𝟙 _) w (ThetaRuleCompare.chart_ge hK j) hw _))
  refine ⟨⟨s, fun j j' => hInj _ (fn_ext fun w hw => ?_)⟩,
    congrArg (SecM.ofSec G) (ThetaRuleCompare.sec_ext fun j => fn_ext fun w hw => ?_)⟩
  · have hw' : (𝟙 _ ≫ (hK ▷ G).left) w ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ⊓
        (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j' := hw
    refine (gs_pull (𝟙 _) _ w _ hw' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ w _ hw' _).symm)
    refine ((gs_res _ w _ hw' _).trans ((hv j w hw'.1).trans
      (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) G).left)
        (ε := fun _ => ((1 : ℕ) : ℤ)) θ (𝟙 _) w
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j hw'.1)
        (ThetaRuleCompare.chart_ge (a := ((1 : ℕ) : ℤ)) hK j' hw'.2)))).trans (Eq.symm ?_)
    refine (gs_mul _ w _ hw' _ _).trans (congrArg₂ (· * ·) ((gs_unit _ w _ hw' _).trans (congrArg Units.val
      ((gm_linComb L _ _ _ w j j' hw'.1 hw'.2).trans ?_))) ((gs_res _ w _ hw' _).trans (hv j' w hw'.2)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, VVRank.whisker_snd_left]
  · exact (ThetaRuleCompare.gs_pullS hK _ _ w j hw).trans
      (hv j w (chart_le_res G L (hK ▷ G) (whiskerRight_snd _ _) _ j hw))
end GlobalTheory.UMin.SecExtend
