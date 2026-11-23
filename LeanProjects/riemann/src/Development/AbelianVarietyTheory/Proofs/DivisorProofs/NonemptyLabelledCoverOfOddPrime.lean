import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UCoverLab

theorem jK_mono (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

theorem gp_mono {R : Type} [CommRing R] [IsDomain R] (M : Modif R) : Mono M.gp := by
  have : Mono (M.gp ≫ M.π) := by rw [M.gp_π]; exact jK_mono R
  exact mono_of_mono M.gp M.π

theorem mono_α {R : Type} [CommRing R] [IsDomain R] {M : Modif R} {X : Over M.S} [GrpObj X]
    {A : Over (Sp (FractionRing R))} [GrpObj A] {α : A.left ⟶ X.left} (h : IsGrpPullback A X M.gp α) : Mono α := by
  haveI := gp_mono M
  refine ⟨fun u v huv => h.1.hom_ext huv ?_⟩
  apply (cancel_mono M.gp).1
  rw [Category.assoc, Category.assoc, ← h.1.w, ← Category.assoc, huv, Category.assoc]

end GlobalTheory.Mum.UCoverLab

open GlobalTheory.Mum.UCoverLab GlobalTheory.Mum.CoverFin in

theorem GlobalTheory.Mum.UCover.labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  intro R _ _ _ hB D C lab n hn ho hu hone hgal
  refine ⟨{ toModif := C.toModif
            G := C.G
            semi := C.semi
            P := C.P
            A := C.A
            α := C.α
            α_cart := C.α_cart
            α_lb := C.α_lb
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := fun j => lab (n ^ j)
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hW', hio, hfin, hcart, hlb⟩ := C.trait W hW φ ξ hφ hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hsemi : IsSemiAbelian G' := semiAbelian_of_pull hcart C.semi
  have hγ : IsGrpPullback A'.A G' (jK W') (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) :=
    GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre
  have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' _).comp (hio.comp hφ)
  obtain ⟨ga, hga, hy⟩ := GlobalTheory.T.exists_factor_field_point_through_generic_point R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ) hinj (by
    rw [Category.assoc, Category.assoc, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)
  have hcomp : IsGrpPullback A'.A C.G (spMap ga ≫ C.gp) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β) :=
    (hγ.comp hcart).congr hy rfl
  let a : A'.A.left ⟶ C.A.A.left := C.α_cart.1.lift ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)
    (A'.A.hom ≫ spMap ga) (by rw [hcomp.1.w, Category.assoc])
  have ha : a ≫ C.α = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β := C.α_cart.1.lift_fst _ _ _
  have ha2 : a ≫ C.A.A.hom = A'.A.hom ≫ spMap ga := C.α_cart.1.lift_snd _ _ _
  have hcart' : IsGrpPullback A'.A C.A.A (spMap ga) a := IsGrpPullback.cancel C.α_cart (hcomp.congr rfl ha.symm) ha2
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hA' : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W'))) :=
    LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi)
      (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W')) _ _ fun _ => rfl) U'.ext
  have h2 : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')))
      (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.chartPull (chartPullPull U'.LG.L _) (chartPullSame C.P.L.L _ _ _ _ fun _ => rfl) hlb
  have h3 : LBIso A'.L (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB C.P.L.isLB _) hA' h2
  have hfib : IsFib (io.comp φ) C.A A' a :=
    ⟨ga, fun r => hga r, hcart', lbIso_factor C.P.L.isLB C.A.isLB A'.isLB ha C.α_lb h3⟩
  obtain ⟨hD, hind⟩ := GlobalTheory.T.recognition_degData_labels_at_every_trait R hB D C.A lab n hn ho hu hone hgal W' hW' (io.comp φ) (hio.comp hφ)
    inferInstance G' D' A' U' a hsemi hfib
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G', inferInstance, inferInstance, β, D', A', U', hD, hW',
    hio, hfin, hcart, hlb, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hind j F em hF p p₁ p' x' h₁ h₂ h₃ ?_
  haveI := mono_α C.α_cart
  rw [← cancel_mono C.α, Category.assoc, ha]
  simpa only [Category.assoc] using h₄
