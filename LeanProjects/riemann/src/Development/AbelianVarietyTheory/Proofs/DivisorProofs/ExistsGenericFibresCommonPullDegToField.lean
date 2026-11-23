import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenericPull

open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull GlobalTheory.FieldPull

theorem nonempty_isPullDeg_cancel {R K₁ K : Type} [CommRing R] [IsDomain R] [Field K₁] [Field K] {α : R →+* K₁}
    (hα : Function.Injective α) (β : K₁ →+* K) {D₀ : DegPre R} {D₁ : DegPre K₁} {D : DegPre K}
    (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, -, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap hα ≫ jK R :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

theorem exists_generic_fibre {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ E : DegPre (FractionRing R), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D E) := by
  obtain ⟨U, hU, hψ⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨E, p, -⟩ := DegPull.exists_isPullDeg polBaseChange_holds R (FractionRing R) (algebraMap R (FractionRing R))
    D U hψ (TauPull.jK_mem (R := R) (genericPoint (Spec (CommRingCat.of (FractionRing R)))) U ⟨_, hU⟩)
  exact ⟨E, ⟨p⟩⟩

end GlobalTheory.GenericPull

namespace GlobalTheory.Mum

open GlobalTheory.GenericPull

theorem exists_generic_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  intro R _ _ _ _ D₁ D₂ W _ _ φ hφ D' p₁ p₂
  obtain ⟨E₁, ⟨q₁⟩⟩ := exists_generic_fibre D₁.toPre D₁.tau_bimult
  obtain ⟨E₂, ⟨q₂⟩⟩ := exists_generic_fibre D₂.toPre D₂.tau_bimult
  obtain ⟨E', ⟨q⟩⟩ := exists_generic_fibre D' (TauPull.tauBimult_pull globalFns_holds p₁ D₁.tau_bimult)
  have e : (algebraMap W (FractionRing W)).comp φ = (ArcPull.fracMap hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (ArcPull.fracMap_algebraMap hφ x).symm
  have hR := IsFractionRing.injective R (FractionRing R)
  have hW := IsFractionRing.injective W (FractionRing W)
  obtain ⟨r₁⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₁ q
  obtain ⟨r₂⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₂ q
  exact ⟨E₁, E₂, FractionRing W, inferInstance, ArcPull.fracMap hφ, E', ⟨q₁⟩, ⟨q₂⟩,
    nonempty_isPullDeg_cancel hR _ q₁ r₁, nonempty_isPullDeg_cancel hR _ q₂ r₂⟩

end GlobalTheory.Mum
