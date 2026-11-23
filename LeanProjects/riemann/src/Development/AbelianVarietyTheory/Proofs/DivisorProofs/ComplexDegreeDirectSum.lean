import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CxDegSum

theorem isProjOver_cxFibre {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsProjOver (cxFibre.snd p) := by
  have := h.finite
  have := h.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  have H : IsPullback (cxFibre.fst p) (cxFibre.snd p) (p ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom ℂ)) := IsPullback.of_hasPullback _ _
  exact ProjSpace.isProjOver_of_isPullback_spMap _ H hP

theorem cxDeg_biprod : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsArithVar p 1 → ∀ (E F : S.Modules) (r s : ℕ), VB.IsVB E r → VB.IsVB F s → cxDeg p (E ⊞ F) (r + s) = cxDeg p E r + cxDeg p F s := by
  intro k _ S p _ h E F r s hE hF
  have hf := isProjOver_cxFibre h
  have fin {G : (cxFibre p).Modules} {r : ℕ} (h : IsVB G r) : FiniteCoh ℂ G :=
    have := h.isFiniteQC
    finiteCoh_of_isProjOver (fun _ => rfl) G hf
  have : PreservesBinaryBiproduct E F (Scheme.Modules.pullback (cxFibre.fst p)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  have e := (Scheme.Modules.pullback (cxFibre.fst p)).mapBiprod E F
  rw [cxDeg, cxDeg, cxDeg, degOfRank_congr ℂ e]
  simp only [degOfRank, chi_biprod (fin (hE.pullback _)) (fin (hF.pullback _))]
  push_cast
  ring

end GlobalTheory.CxDegSum
