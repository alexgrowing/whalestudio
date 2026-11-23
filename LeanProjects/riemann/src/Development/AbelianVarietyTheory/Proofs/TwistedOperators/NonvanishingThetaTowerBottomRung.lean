import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawPeriodNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.AscBottom

variable {D : D7}

theorem rapidDec_star {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun γ hγ g => by simp [Pi.star_apply, h1 γ hγ g], h2.star, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  exact ⟨C, fun g => by simpa [Pi.star_apply, norm_star] using hC g⟩

theorem rung0 (hF : FockTot) : Rung0 := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h
  have hm : 0 < D.R.m := by omega
  obtain ⟨hom, homC, -, hev, hdep, hdn, hpart, -, -, -⟩ := GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hq T L μ0 hL sc G W M hM 0 hm
  obtain ⟨hchT, hchS⟩ := hev ⟨0, rfl⟩
  obtain ⟨hrap, hch⟩ := hΨ
  obtain ⟨f, hf, hΨ0⟩ := hch 0 hm
  have hhf := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vT : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hhf.1, hhf.2⟩
  let ρ₀ : G.RealVec := fun _ => 0
  let Φ₀ : G.Datum := fun _ => default
  have hu' : RapidDec (Yc D 0) (star u) := rapidDec_star (hu ρ₀ Φ₀ 0 (Nat.zero_le _))
  have hφ : RapidDec (G.V (.core 1)) (star (Ψ 1)) := rapidDec_star (hrap 1 (by omega))

  set a := G.ch.chi (D.R.m - 0) with ha
  have homR : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta) (omRow W 0) := by
    have := hom
    rwa [hchS, hchT] at this
  have homX : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta * L.eta⁻¹) (omCore W 0) := by
    rw [mul_inv_cancel_right]; exact homC
  have hHeta : IsHeckeChar D L.eta := by
    have := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homR.hecS) homR.hecT
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hReta : ResEta D L.eta (negSp F.Lz).rank := by
    have h1 := Formalism.L2.Theta.resEta_mul (Formalism.L2.Theta.resEta_inv homC.resT) homR.resT
    rw [inv_inv, mul_inv_cancel_left] at h1
    refine Formalism.L2.Theta.resEta_parity h1 ?_
    have hr : (G.V (.grid 0 0)).rank + 1 = (G.V (.core 0)).rank := by
      have := F.oz.rank_add; rw [F.rk] at this; exact this
    show _ = F.Lz.rank % 2
    rw [F.rk]
    omega
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.core 1)) (negSp F.Lz) W.ψ a⁻¹⁻¹ L.eta W.ψ_std
    (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homX.hecS) hHeta (Formalism.L2.Theta.resEta_inv homX.resS) hReta

  have hΞ : VacG W.ψ _ _ (latCore G 0) (star f) := (hdep f).1 hf
  have hlift : liftT (omCore W 0) (v 1).μ (v 1).𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := by
    rw [hΨ0]; exact (hdn v f (Ψ 1)).symm
  have hint : (∫ x in vT.𝓕, liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) (F.oz.emb (x, 1)) *
      star u x ∂vT.μ) ≠ 0 := by
    have e : (fun x : GA D (Yc D 0) => liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f)
        (F.oz.emb (x, 1)) * star u x) = fun x => (starRingEnd ℂ) (Ψ 0 (stabilizerEmbedding G.sp.dec0 x) * u x) := by
      funext x
      have hl : liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := hlift
      rw [hl, hE.bot x, map_mul]; rfl
    rw [e, integral_conj]
    intro h0
    apply hper
    have := congrArg (starRingEnd ℂ) h0
    rw [Complex.conj_conj, map_zero] at this
    exact this
  obtain ⟨Φ', Φz, hΦ', hΦz, hne⟩ := GlobalTheory.T.lastSeesaw_periodNonvanishing D W.ψ (F.jac v 0 h) (G.V (.core 0)) (Yc D 0) F.Lz F.oz (latRow G 0) (ΓL 0)
    (latCore G 0) F.rk (hG.last h) (F.ζ 0) a⁻¹ (a⁻¹ * L.eta) L.eta (omRow W 0) (omCore W 0) omz homR homX homz vT
    (star (Ψ 1)) (star u) hφ hu' (star f) hΞ hint

  let ℓ : (WO (G.V (.grid 1 0)) (G.V (.grid 0 0)) → ℂ) → ℂ := fun Φ =>
    (F.jac v 0 h).per W.ψ (F.ζ 0) omz (star (Ψ 1)) (liftS (omRow W 0) vT.μ vT.𝓕 (star u) Φ) Φz
  have hT : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ (Yc D 0) vT (star u) hu').2 0 (F.jac v 0 h) a⁻¹ (a⁻¹ * L.eta) (omRow W 0) homR (negSp F.Lz)
      (F.ζ 0) a⁻¹⁻¹ L.eta omz homz (star (Ψ 1)) Φz hφ hΦz.1
  have hK : ∃ κ P, ℓ (star (W.fock (.chi 0 0) (W.cosVec 0 κ) P)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hne (hF D hq T L μ0 hL sc G W M hM ⟨0, hm⟩ ℓ hT hno Φ' hΦ')
  obtain ⟨κ, P, hκP⟩ := hK
  let ρ : G.RealVec := Function.update ρ₀ ⟨0, hm⟩ P
  let Φ : G.Datum := Function.update Φ₀ ⟨0, hm⟩ κ
  refine ⟨a⁻¹⁻¹, omz, homz, ρ, Φ, Φz, hΦz, ?_⟩
  have hp := hpart ρ Φ u
  have hd : W.datum ρ Φ ⟨0, hm⟩ = W.fock (.chi 0 0) (W.cosVec 0 κ) P := by
    show W.fock (.chi 0 0) (W.cosVec 0 (Φ ⟨0, hm⟩)) (ρ ⟨0, hm⟩) = _
    simp only [ρ, Φ, Function.update_self]
  rw [hd] at hp
  change ℓ _ ≠ 0 at hκP
  convert hκP using 2
  exact hp

end GlobalTheory.AscBottom
end
