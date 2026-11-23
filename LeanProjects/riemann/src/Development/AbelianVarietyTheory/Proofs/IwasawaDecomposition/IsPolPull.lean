import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartOfTwistedMapStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolPull

theorem isPol_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (Z : GMod Xo c) (Z' : GMod Xo' c') (BD : EffCartierData Z.X)
    (BD' : EffCartierData Z'.X) (f : InvFun (𝓞 E)) (m : ℕ) (b : 𝓞 c.F →+* 𝓞 c'.F) (σ : 𝓞 E ≃+* 𝓞 E)
    (r : Xo'.XF c' ⟶ Xo.XF c) (ν : TwMap σ Z'.oF.t Z.oF.t r) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b)
    (mu : TwMap σ Z'.t Z.t π), IsTwInv H f → σ H.w0 = H.w0 → IsFinite (pullback.lift π Z'.s hπ) →
    Z'.j ≫ π = r ≫ Z.j → IsPol f m Z BD → IsPhiDiv f Z' BD' → IsPol f m Z' BD' := by
  intro E _ _ _ H D l l' Xo Xo' c c' Z Z' BD BD' f m b σ r ν π hπ mu htw hσ hfin hj hP hB'
  obtain ⟨hd, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨hd', hft', -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l' c'
  have hI : BD'.idealSheaf = BD.idealSheaf.comap π :=
    GlobalTheory.PolDiv.idealSheaf_eq_comap E H D l l' Xo Xo' c c' (𝓞 c.F) (𝓞 c'.F) _ _ Z Z' BD BD' f σ r ν hd hd' hft' htw hσ
      hP.1 hB' π hj
  have hA := hP.2
  have hL := GlobalTheory.PolFin.isLB_detLie_of_polOf hA.isLB
  have hL' : (GlobalTheory.FlagMod.detLie Z').IsLB := by
    refine GlobalTheory.FlagMod.isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_) fun i j k _ _ z => GlobalTheory.FlagMod.ev_detChg_mul i j k z
    obtain ⟨M, hM⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ (π x)))
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_chart_of_twisted_map E H D l l' Xo Xo' c c' Z Z' σ π mu hσ M x hM
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨M', hM'⟩
  have e₁ : CechPic.pull π (CechPic.cls _ hL) = CechPic.cls _ hL' :=
    (CechPic.cls_eq_iff (pull_isLB hL π) hL').2 (GlobalTheory.PolFin.lbIso_detLie mu.cart)
  have hk : BD.KeepsRegular π := (BD.keepsRegular_iff_effCartier π).2 (hI ▸ BD'.effCartier_idealSheaf)
  have e₂ : CechPic.pull π (CechPic.cls _ BD.isLB_lb) = CechPic.cls _ BD'.isLB_lb :=
    ((CechPic.cls_eq_iff (BD.pull π hk).isLB_lb (pull_isLB BD.isLB_lb π)).2 (BD.lbIso_pull π hk)).symm.trans
      ((CechPic.cls_eq_iff _ _).2 (EffCartierData.lbIso_of_idealSheaf_eq _ _
        ((BD.idealSheaf_pull π hk).trans hI.symm)))
  have cl : ∀ {X : Scheme.{0}} {L B : LB X} (hL : L.IsLB) (hB : B.IsLB)
      (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB),
      CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB := fun hL hB h => by
    rw [CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB),
      CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]
  have hA' : (polOf Z' m BD').IsLB :=
    CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual hL') m) (CechPic.isLB_dual BD'.isLB_lb)
  have e : CechPic.pull π (CechPic.cls _ hA.isLB) = CechPic.cls _ hA' :=
    (congrArg _ (cl hL BD.isLB_lb hA.isLB)).trans (Eq.trans
      (by rw [map_add, map_nsmul, map_neg, map_neg, e₁, e₂]) (cl hL' BD'.isLB_lb hA').symm)
  have hiso : LBIso (polOf Z' m BD') ((polOf Z m BD).pull π) :=
    (CechPic.cls_eq_iff hA' (pull_isLB hA.isLB π)).1 ((e.symm.trans (CechPic.cls_pull hA.isLB π _).symm))
  have : IsAffineHom (pullback.lift π Z'.s hπ) := inferInstance
  have : IsAffineHom (pullback.fst Z.s (spMap b)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback Z.s (spMap b)).flip (isAffineHom_of_isAffine _)
  have hπa : IsAffineHom π := by
    rw [← pullback.lift_fst π Z'.s hπ]; infer_instance
  exact ⟨hB', (hA.pull_of_isAffineHom π).of_lbIso hA' hiso⟩

end GlobalTheory.PolPull
