import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotientsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChainTw

open GlobalTheory.LFun in

theorem dv_center_of_isSplit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (a t : ℕ) :
    dv E a (a + t) v ((t : ℂ) / 2) =
      (∏ n ∈ Finset.Ioc t (a + t), (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ n)⁻¹))⁻¹ := by
  have hI : Finset.Icc (t + 1) (t + a) = Finset.Ioc t (a + t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have he : etaU E v = 1 := by unfold etaU; exact if_pos hv
  rw [dv_center, hI, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [locL, etaFam_of_unram (isUnram_of_isSplit h2 hv), he, one_pow, eulerFac_singleton, Units.val_one, one_mul,
    npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem dSfun_twist_restore : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  intro D c w hw a
  classical
  obtain ⟨hS, hQS₀, hinj, hsplit, -⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
  have ht : 0 < ((D.R.t : ℂ) / 2).re := by
    have h3 := D.R.three_m_lt_t
    have h1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 1 ≤ D.R.t)
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set s : ℂ := (D.R.t : ℂ) / 2 with hs_def
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + D.R.t) v s with hf
  set Qv : Finset (HeightOneSpectrum (𝓞 D.host.F)) := w.Q.image fun PP => PP.under (𝓞 D.host.F) with hQv
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ w.S₀}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv w.S₀ a (a + D.R.t) ht).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ht).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Qv : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Qv f)
  have hmem : ∀ v, v ∈ Qv ↔ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v := fun v => by simp [hQv]
  have hsplitf : Set.mulIndicator {v | v ∉ w.S₀} f =
      Set.mulIndicator {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Qv : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe]
    by_cases hq : v ∈ Qv
    · obtain ⟨PP, hPP, rfl⟩ := (hmem _).1 hq
      have hc : PP.under (𝓞 D.host.F) ∈ c.S := (hS _).2 (Or.inr ⟨PP, hPP, rfl⟩)
      simp [hQS₀ PP hPP, hc, hq]
    · by_cases h0' : v ∈ w.S₀
      · have hc : v ∈ c.S := (hS _).2 (Or.inl h0')
        simp [h0', hc, hq]
      · have hc : v ∉ c.S := fun hc => ((hS _).1 hc).elim h0' fun hx => hq ((hmem _).2 hx)
        simp [h0', hc, hq]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s =
      GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) s * ∏ v ∈ Qv, f v :=
    h0.unique (h1.mul h2)
  have hloc : ∀ PP ∈ w.Q, f (PP.under (𝓞 D.host.F)) = ((zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ)⁻¹ := by
    intro PP hPP
    obtain ⟨hsp, hN, -⟩ := hsplit PP hPP
    show GlobalTheory.LFun.dv D.host.E a (a + D.R.t) (PP.under (𝓞 D.host.F)) ((D.R.t : ℂ) / 2) = _
    rw [dv_center_of_isSplit D.sp.cm.deg2 hsp, hN, zinv]
    push_cast
    rfl
  have hprod : ∏ v ∈ Qv, f v = (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ)⁻¹ := by
    rw [hQv, Finset.prod_image (fun x hx y hy h => hinj hx hy h), Finset.prod_congr rfl hloc,
      Finset.prod_inv_distrib]
    push_cast
    rfl
  have hne : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s ≠ 0 := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ ht
  rw [hprod] at key
  have hZ : (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ) ≠ 0 := by
    intro h0
    apply hne
    rw [key, h0, _root_.inv_zero, mul_zero]
  refine ⟨hne, ?_⟩
  rw [key, mul_assoc, inv_mul_cancel₀ hZ, mul_one]

end GlobalTheory.ChainTw
