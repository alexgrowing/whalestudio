import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubledStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramifiedStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem unrAt_inv_of_unrAt {D : D7} {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : GlobalTheory.LFun.UnrAt χ w) : GlobalTheory.LFun.UnrAt χ⁻¹ w := by
  intro x hx
  have := h x hx
  simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
  rw [this, inv_one]

theorem isHeckeChar_inv_sph {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]

set_option maxHeartbeats 1000000 in

theorem sphFactor_of_weilRepresentationUnitaryPair (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) : SphFactor D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv s
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  have hδ := (hTC Φ₁ Φ₂ hΦ₁ hΦ₂).1
  have hco := (hCC Φ₁ Φ₂ hΦ₁ hΦ₂).2
  have hlaw := GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh homh ν 𝓕 hP.covol _ hδ
  have hvac := GlobalTheory.T.doubledTheta_vector_fixed_unramified_stabilizer D ψ A B χB omh homh LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv
  haveI : Submodule.IsLattice D.host.E LA := hU.sdA.1
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram LA a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A LA a hU.sdA hP.maj
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hK : IsCompact (KAd D.sp.cm.sig (dblSp A).gram LA a : Set (GA D (dblSp A))) := isCompact_KAd (isCMExt_host D)
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : GA D (dblSp A) → ℂ, Ψ = fun g => swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) g *
      npow (hgtAd D.sp.cm.sig (dblSp A).gram LA a g) (s - sZero A B) := ⟨_, rfl⟩
  have hw : ∀ g : GA D A, wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A LA a g) (s - sZero A B) = Ψ (io A (g, 1)) := by
    intro g
    simp only [hΨdef, wcoef, hgtL, hco g]
  have hΨlaw : ∀ (p : siegelH _ D.sp.cm.sig (dblSp A).gram) (g : GA D (dblSp A)),
      Ψ ((p : GA D (dblSp A)) * g) = (χB⁻¹ (aH _ D.sp.cm.sig (dblSp A).gram p) : Circle) *
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g := by
    intro p g
    simp only [hΨdef]
    have hleft : hgtAd D.sp.cm.sig (dblSp A).gram LA a ((p : GA D (dblSp A)) * g) =
        absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p) * hgtAd D.sp.cm.sig (dblSp A).gram LA a g :=
      hI.hgtH_left continuous_absE hK p g
    have hr : npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) =
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (sZero A B + (A.rank : ℂ) / 2) *
          npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s - sZero A B) := by
      rw [← npow_add (hom_pos (absE D.host.F D.host.E) (aH _ D.sp.cm.sig (dblSp A).gram p))]
      congr 1; ring
    rw [hlaw p g, hleft, npow_mul, hr]
    ring
  have hΨright : ∀ g, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v,
      Ψ (g * emb D.sp.cm.sig (dblSp A).gram v k) = Ψ g := by
    intro g k hk
    simp only [hΨdef]
    have hright : hgtAd D.sp.cm.sig (dblSp A).gram LA a (g * emb D.sp.cm.sig (dblSp A).gram v k) =
        hgtAd D.sp.cm.sig (dblSp A).gram LA a g := hI.hgtH_right continuous_absE hK g (emb_mem_KAd hk)
    rw [hright]
    congr 1
    simp only [swSec]
    rw [show ((g * emb D.sp.cm.sig (dblSp A).gram v k, (1 : GA D B))) =
      (g, 1) * (emb D.sp.cm.sig (dblSp A).gram v k, 1) by simp, map_mul, Module.End.mul_apply, hvac k hk]
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χB⁻¹ w := by
    intro w hw'
    refine unrAt_inv_of_unrAt (hU.unr w ?_)
    intro hmem
    exact hv (by simpa [GlobalTheory.LFun.above, hw'] using hmem)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_unique_spherical_doubling_section_unramified D A LA hU.sdA χB⁻¹ (isHeckeChar_inv_sph homh.hecT) v hunr s
  have huniq := hφ.2
  refine ⟨φ, hφ.1, fun x hx y => ?_⟩
  have hx' : proj D.sp.cm.sig (dblSp A).gram v (io A (x, 1)) = 1 := by
    rw [io, proj_ioH, hx, map_one, ioH_one]
  have hl : ∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) (g : Gv (dblSp A) v),
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (p * g) * io A (x, 1)) =
        charAt χB⁻¹ v (aH _ D.sp.cm.sig (dblSp A).gram p) *
          npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) *
          Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro p g
    rw [map_mul, mul_assoc, ← coe_embP, hΨlaw, aH_embP, absE_ideleAt]
    rfl
  have hr : ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, ∀ g : Gv (dblSp A) v,
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (g * k) * io A (x, 1)) =
        Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro k hk g
    rw [map_mul, mul_assoc, (commute_emb D.sp.cm.sig (dblSp A).gram k hx').eq, ← mul_assoc, hΨright _ k hk]
  have key := huniq (fun g => Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1))) hl hr (ioAt A v y)
  simp only [map_one, one_mul] at key
  rw [hw, hw, ← key, ioAt, emb_ioH, io, ← map_mul, Prod.mk_mul_mk, map_one, one_mul,
    (commute_emb D.sp.cm.sig A.gram y hx).eq]

end GlobalTheory.Core.Rk.IP
