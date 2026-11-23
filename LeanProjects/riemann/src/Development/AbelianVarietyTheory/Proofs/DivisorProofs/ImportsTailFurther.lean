import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem LabCover.exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (M' : Modif R) (h : M'.S ⟶ C.S), M'.gp ≫ h = C.gp → h ≫ C.π = M'.π → ∃ (C' : LabCover D) (eS : C'.S ≅ M'.S) (β : C'.G.left ⟶ C.G.left), eS.hom ≫ M'.π = C'.π ∧ IsGrpPullback C'.G C.G (eS.hom ≫ h) β ∧ LBIso C'.P.L.L (C.P.L.L.pull β) := by
  intro R _ _ _ D C M' h hgp hπ
  have hex : ∃ (P' : GlobalTheory.UU.CP ((Over.pullback h).obj C.G)) (w : _),
      GlobalTheory.UU.IsCPMap P' C.P h (pullback.fst C.G.hom h) pullback.condition w :=
    GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G h)
  obtain ⟨P', w, hP⟩ := hex
  have hG : IsGrpPullback ((Over.pullback h).obj C.G) C.G h (pullback.fst C.G.hom h) := isGrpPullback_pullback C.G h
  have hw : LBIso P'.L.L (C.P.L.L.pull (pullback.fst C.G.hom h)) := ⟨w, hP.gen⟩

  have key : ∀ {Y : Scheme.{0}} (b : Y ⟶ ((Over.pullback h).obj C.G).left) (c : Y ⟶ C.G.left),
      c = b ≫ pullback.fst C.G.hom h → LBIso (P'.L.L.pull b) (C.P.L.L.pull c) := fun b c e =>
    LBIso.chartPull (chartPullId _) (GlobalTheory.RigidBundleGlue.chartPullComp C.P.L.L _ b c e)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hw b)
  let α' : C.A.A.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift C.α (C.A.A.hom ≫ M'.gp) (by rw [C.α_cart.1.w, Category.assoc, hgp])
  have hα : α' ≫ pullback.fst C.G.hom h = C.α := pullback.lift_fst _ _ _
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj C.G
            semi := IsSemiAbelian.pullback h C.G C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := IsGrpPullback.cancel hG (C.α_cart.congr hgp.symm hα.symm) (pullback.lift_snd _ _ _)
            α_lb := LBIso.trans C.A.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) C.α_lb
              (LBIso.symm (key α' C.α hα.symm))
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }, Iso.refl _, pullback.fst C.G.hom h, Category.id_comp _,
      hG.congr (Category.id_comp _).symm rfl, hw⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, _, β, D', A', U', hD, hW', hio, hfin, hcart, hlb, hlab⟩ :=
    C.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  let β' : G''.left ⟶ ((Over.pullback h).obj C.G).left :=
    pullback.lift β (G''.hom ≫ spMap io ≫ ξ) (by rw [hcart.1.w, Category.assoc, Category.assoc])
  have hβ : β' ≫ pullback.fst C.G.hom h = β := pullback.lift_fst _ _ _
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, inferInstance, β', D', A', U', hD, hW',
    hio, hfin, IsGrpPullback.cancel hG (hcart.congr (Category.assoc _ _ _).symm hβ.symm) (pullback.lift_snd _ _ _),
    LBIso.trans U'.LG.isLB (pull_isLB C.P.L.isLB _) (pull_isLB P'.L.isLB _) hlb (LBIso.symm (key β' β hβ.symm)), ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hlab F em hF j p p₁ p' x' h₁ h₂ h₃ ?_
  have e := congrArg (· ≫ pullback.fst C.G.hom h) h₄
  simp only [Category.assoc, hβ, hα] at e
  simpa only [Category.assoc] using e

end GlobalTheory.Mum
