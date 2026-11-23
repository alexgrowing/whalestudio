import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResUnr

open Formalism.L2.Host

theorem exists_int_div {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (k : E)
    (hk : P.valuation E k = 1) :
    ∃ a s : 𝓞 E, a ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ k * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, h | h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := E) k
  · refine ⟨n, d, ?_, d.2, h⟩
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E), ← h, map_mul, hk, one_mul,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact d.2
  · refine ⟨d, n, d.2, ?_, h⟩
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, hk, one_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) (r := (d : 𝓞 E)) P).2 d.2] at h2
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).1 h2

theorem loc_eq_of_isRes {D : D7} {H₁ H₂ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {ξ : (kP PP)ˣ →* ℂˣ}
    (h₁ : IsRes H₁ PP ξ) (h₂ : IsRes H₂ PP ξ) (x : (PP.adicCompletion D.host.E)ˣ) (hx : IsUnitAt PP x) :
    H₁.loc PP x = H₂.loc PP x := by
  have hc : IsClopen {x : (PP.adicCompletion D.host.E)ˣ | IsUnitAt PP x} := by
    have := (Valued.isClopen_sphere (PP.adicCompletion D.host.E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := PP.adicCompletion D.host.E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  have hK : ∀ k : D.host.Eˣ, PP.valuation D.host.E (k : D.host.E) = 1 → H₁.locK PP k = H₂.locK PP k := by
    intro k hk
    obtain ⟨a, s, ha, hs, hks⟩ := exists_int_div PP (k : D.host.E) hk
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    have hne : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := fun b hb h0 =>
      hb (by rw [(IsFractionRing.injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)]; exact PP.asIdeal.zero_mem)
    have hq : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun b hb h0 =>
      hb (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let A : D.host.Eˣ := Units.mk0 _ (hne a ha)
    let S : D.host.Eˣ := Units.mk0 _ (hne s hs)
    let ua : (kP PP)ˣ := Units.mk0 _ (hq a ha)
    let us : (kP PP)ˣ := Units.mk0 _ (hq s hs)
    have hkS : k * S = A := Units.ext hks
    have e1 : H₁.locK PP A = H₂.locK PP A := ((h₁ a A ua rfl rfl).symm.trans (h₂ a A ua rfl rfl))
    have e2 : H₁.locK PP S = H₂.locK PP S := ((h₁ s S us rfl rfl).symm.trans (h₂ s S us rfl rfl))
    rw [← hkS, map_mul, map_mul, e2] at e1
    exact mul_right_cancel e1
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin PP).induction_on
    (p := fun x => IsUnitAt PP x → H₁.loc PP x = H₂.loc PP x) x ?_
    (fun k hk => hK k ((PP.valuedAdicCompletion_eq_valuation' _).symm.trans hk)) hx
  exact isClosed_imp hc.2 (isClosed_eq (H₁.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP))
    (H₂.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP)))

theorem unrAt_div_of_isRes : ∀ (D : D7) (c₁ c₂ : (AE D)ˣ →* Circle) (H₁ H₂ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), ChrEq c₁ H₁ → ChrEq c₂ H₂ → IsRes H₁ PP ξ → IsRes H₂ PP ξ → GlobalTheory.LFun.UnrAt (F := D.host.F) (c₁ * c₂⁻¹) PP := by
  intro D c₁ c₂ H₁ H₂ PP ξ hc₁ hc₂ h₁ h₂ x hx
  have e : GlobalTheory.LFun.locChar (c₁ * c₂⁻¹) PP x = GlobalTheory.LFun.locChar c₁ PP x * (GlobalTheory.LFun.locChar c₂ PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq hc₁, GlobalTheory.LFun.locChar_eq_of_chrEq hc₂, loc_eq_of_isRes h₁ h₂ x hx, mul_inv_cancel]

end GlobalTheory.ResUnr
