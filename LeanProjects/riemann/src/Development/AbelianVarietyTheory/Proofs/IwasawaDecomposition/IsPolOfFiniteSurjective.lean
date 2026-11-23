import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullbackStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.AmpleDown

theorem isFinite_of_lift {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (b : R →+* R')
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (π : X' ⟶ X) (hπ : π ≫ s = s' ≫ spMap b) (hb : b.Finite)
    [IsFinite (pullback.lift π s' hπ)] : IsFinite π := by
  have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hb
  rw [← pullback.lift_fst π s' hπ]
  infer_instance

theorem isNoetherian_gmod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) : AlgebraicGeometry.IsNoetherian Z.X := by
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  have : IsNoetherianRing (𝓞 c.F) := Algebra.FiniteType.isNoetherianRing ℤ (𝓞 c.F)
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  exact ⟨⟩

theorem isPol_of_finite_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (Z : GMod Xo c) (Z' : GMod Xo' c') (BD : EffCartierData Z.X)
    (BD' : EffCartierData Z'.X) (f : InvFun (𝓞 E)) (m : ℕ) (b : 𝓞 c.F →+* 𝓞 c'.F) (σ : 𝓞 E ≃+* 𝓞 E)
    (r : Xo'.XF c' ⟶ Xo.XF c) (ν : TwMap σ Z'.oF.t Z.oF.t r) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b)
    (mu : TwMap σ Z'.t Z.t π), IsTwInv H f → σ H.w0 = H.w0 → b.Finite → IsFinite (pullback.lift π Z'.s hπ) →
    Z'.j ≫ π = r ≫ Z.j → Function.Surjective π → (polOf Z m BD).IsLB → IsPol f m Z' BD' → IsPhiDiv f Z BD →
    IsPol f m Z BD := by
  intro E _ _ _ H D l l' Xo Xo' c c' Z Z' BD BD' f m b σ r ν π hπ mu htw hσ hb hlift hj hsurj hLB hP' hD
  refine ⟨hD, ?_⟩
  obtain ⟨hβ, -, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨hβ', hft', -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l' c'
  have hI : BD'.idealSheaf = BD.idealSheaf.comap π :=
    GlobalTheory.PolDiv.idealSheaf_eq_comap E H D l l' Xo Xo' c c' _ _ _ _ Z Z' BD BD' f σ r ν hβ hβ' hft' htw hσ hD hP'.1 π hj
  have hA' := hP'.2
  have hL := GlobalTheory.PolFin.isLB_detLie_of_polOf hLB
  have hL' := GlobalTheory.PolFin.isLB_detLie_of_polOf hA'.isLB
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
  have e : CechPic.pull π (CechPic.cls _ hLB) = CechPic.cls _ hA'.isLB :=
    (congrArg _ (cl hL BD.isLB_lb hLB)).trans (Eq.trans
      (by rw [map_add, map_nsmul, map_neg, map_neg, e₁, e₂]) (cl hL' BD'.isLB_lb hA'.isLB).symm)
  have hiso : LBIso ((polOf Z m BD).pull π) (polOf Z' m BD') := by
    rw [← CechPic.cls_pull hLB π (pull_isLB hLB π)] at e
    exact (CechPic.cls_eq_iff (pull_isLB hLB π) hA'.isLB).1 e
  have hpull : GlobalTheory.IsAmpleLB ((polOf Z m BD).pull π) := hA'.of_lbIso (pull_isLB hLB π) hiso
  exact GlobalTheory.T.ample_of_finite_surjective_pullback Z.X Z'.X π (isNoetherian_gmod Z) Z.normal (isFinite_of_lift b Z.s Z'.s π hπ hb) hsurj _ hLB hpull

end GlobalTheory.AmpleDown
