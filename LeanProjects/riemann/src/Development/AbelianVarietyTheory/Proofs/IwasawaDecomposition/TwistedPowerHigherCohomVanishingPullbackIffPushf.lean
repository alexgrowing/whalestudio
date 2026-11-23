import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem subsingleton_coh_twist_pushforward_iff {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    {A N : LB X} (hA : A.IsLB) (hN : N.IsLB) (G : Y.Modules) [G.IsQuasicoherent] (j m p : ℕ) :
    Subsingleton (coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p) ↔
      Subsingleton (coh (twist ((Scheme.Modules.pushforward g).obj G)
        (tens (lbPow A j) (lbPow N m))) p) := by
  have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  have hA' := LB.isLB_pull hA g
  have hN' := LB.isLB_pull hN g
  have hT' : (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m)).IsLB :=
    isLB_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m)
  have hTp := LB.isLB_pull hT g
  have e : cls _ hT' = cls _ hTp := by
    rw [cls_pull hT, cls_tens (isLB_lbPow hA j) (isLB_lbPow hN m),
      cls_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m), cls_lbPow hA, cls_lbPow hN, cls_lbPow hA',
      cls_lbPow hN', cls_pull hA, cls_pull hN, map_add, map_nsmul, map_nsmul]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq G hT' hTp e
  have := Twist.isQuasicoherent_twist (F := G) hTp
  have e₁ : coh (twist ((Scheme.Modules.pushforward g).obj G) (tens (lbPow A j) (lbPow N m))) p ≃ₗ[ℤ]
      coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p :=
    (cohOn.mapIso ℤ ⊤ p (Twist.projIso _ g G).symm).trans
      ((coh.pushforwardEquiv ℤ (fun r => by simp) (twist G _) p).trans (cohOn.mapIso ℤ ⊤ p i.symm))
  exact e₁.toEquiv.subsingleton_congr.symm

theorem twistConeVanishing_pull_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent],
    (TwistConeVanishing (A.pull g) (N.pull g) G ↔
      TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  intro X Y g _ A N hA hN G _
  unfold TwistConeVanishing
  simp only [subsingleton_coh_twist_pushforward_iff g hA hN G]

end GlobalTheory
