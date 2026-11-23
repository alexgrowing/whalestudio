import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.IsPotCrysAtOfMono0G
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AHodgeDlocParTwistAbsM
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsPotCrysAtOfMono0G
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
end G
theorem galHodge0_of_cgTrue (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    {D : D7} {T : WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) : UpperTheory.GalS.GalHodge0 D T := by
  intro l _ ι π s hc hr
  have := host_isCMField D.host
  have ha : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have inf₁ : ∀ τ, (CG.mk (π₀.twist ν)).infChar τ = (D.naut.infG π τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ν
    rw [(GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ] at h1
    rw [C.inf, CGu.infChar, ← hmk]
    exact h1.infChar_eq
  have hreg : (CG.mk (π₀.twist ν)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨h1, h2⟩ := hr τ
    rw [inf₁]
    refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact h2 y hy
  obtain ⟨ψp, hP⟩ := isPolarized_twist hc₀ hν
  obtain ⟨r, wt, HT, H⟩ := hG _ D.nd.Om l ι _ (by omega) _ ψp hreg hP
  have hloc : ∀ (w : PlE D.host) (u : ℝ), T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [T.tw, C.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (D.R.r : ℝ)) / 2))) := fun w hl => by
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    have k := H.aw_locPar hL hF hl (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.lpTw_add, ← hloc] at k
    exact k
  have hv : s + (1 - (D.R.r : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    have hm : ∀ τ, π₀.HasInfChar τ ((CG.mk π₀).infChar τ) := fun τ => ParLaws.hasInfChar_infChar (CG.mk π₀) τ
    have hw := _root_.GlobalTheory.TempSatGal.weight_eq_alt_alt (by omega) H (fun τ => (CG.mk π₀).infChar τ) s (fun τ => (hm τ).1)
      (fun τ => by rw [inf₁, C.inf, CGu.infChar, ← hmk])
      (fun τ => GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd _ _ π₀ hc₀ τ _ _ (hm τ) (hm _))
    rw [hw]; ring
  have htemp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
      ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) + 3) / 2) := fun w hl hu α hα => by
    obtain ⟨-, hU, hS⟩ := _root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C
    obtain ⟨B, hB, e⟩ := hS _ π w (by omega) hu
    rw [e] at hα
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
    have k : UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) :=
      PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E _ _ (hU _ π (by omega)) w B hB b hb
    rw [Units.val_inv_eq_inv_val]
    have hq := UpperTheory.GalN.one_lt_q (H := D.host) w
    refine (k.inv hq).2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) ?_)
    have : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    linarith
  refine ⟨r, ⟨Units.continuous_val.comp H.cont, H.ss, haway, htemp⟩, fun w hw O _ _ _ Bw hj => ?_⟩
  have hpar : T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w) := by
    rw [C.loc, hmk]
    rfl
  have hab := H.above (D.loc l) (D.locA l) ⟨D.locT l⟩ w _ (D.nd.plOm.2 w) O Bw hj
  have hN : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → _root_.UpperTheory.GalS.NiceAlt (π₀.twist ν) (D.nd.plOm.2 w) := fun k => by
    refine _root_.UpperTheory.GalS.nice_of_loc_par hL hF _ (UpperTheory.GalS.NcW.tw ?_ _)
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, ← hpar]
    exact (UpperTheory.GalS.ncW_of_nc T k).tw _
  refine ⟨fun k => ⟨hab.deRham (hN k), fun τ L τ' hτ => ⟨HT τ, ?_, hab.jumps (hN k) τ L τ' hτ⟩⟩, fun hu => ?_, fun hm => ?_⟩
  · rw [H.weights, inf₁, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  · obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ (π₀.twist ν) w
    refine hab.crys σ₀ hσ₀ ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) (ParLaws.toRep σ₀)).1 ?_)
    rw [← _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.unr_tw, ← hpar]
    exact (T.unr w _).1 hu
  · have hm' : UpperTheory.GalS.NcW (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)) := by
      rw [← hpar]
      exact UpperTheory.GalS.ncW_of_nc T hm
    have hgood : UpperTheory.Zero.LLC.Good (⟨D.R.r, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion D.host.E)) := by
      rw [hmk]
      exact _root_.UpperTheory.One.M.New.cgGood sw C _ π w
    have hs2 : 2 * s = ((D.R.r : ℤ) - 1 - wt : ℤ) := by
      push_cast
      linarith
    have key : ∀ ξ : HChar D.host.E, (∀ τ, ∃ n : ℤ, expo ξ τ = (s : ℂ) + n) →
        (CG.mk (π₀.twist ξ)).IsRegAlg ∧ ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n := fun ξ hξ => by
      refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun τ => ?_⟩
      · obtain ⟨h1, h2⟩ := hr τ
        obtain ⟨n, hn⟩ := hξ τ
        have e := ((ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ξ).infChar_eq
        have e' : (CG.mk (π₀.twist ξ)).infChar τ = (D.naut.infG π τ).map (· + expo ξ τ) := by
          rw [C.inf, CGu.infChar, ← hmk]
          exact e
        rw [e']
        refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨m, hm2⟩ := h2 y hy
        refine ⟨m + n, ?_⟩
        simp only [hn]
        push_cast
        linear_combination hm2
      · obtain ⟨n, hn⟩ := hξ τ
        refine ⟨-n, ?_⟩
        rw [expo_mul, expo_inv, hn, (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
        push_cast
        ring
    have hD : ∀ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite → Dense {g : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ S,
        ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) g} := fun S hS =>
      Dense.mono (by rintro g ⟨w, h1, -, h2⟩; exact ⟨w, h1, h2⟩)
        (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne') S hS)
    obtain ⟨ξh, x1, x2, x3, x4⟩ := exists_halfChar D
    have hone : ∀ v, (1 : HChar D.host.E).UnrAt v := fun v x _ => rfl
    have cone : (CG.ofChar (1 : HChar D.host.E)).IsCsd := isCsd_ofChar_of_res _ _ (Or.inl
      ⟨fun v k => by
        simp only [HChar.resFin, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl,
      fun v k => by
        simp only [HChar.resInf, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl⟩)
    rcases Int.even_or_odd' ((D.R.r : ℤ) - 1 - wt) with ⟨k, hk | hk⟩
    · have hsk : (s : ℂ) = k := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key 1 fun τ => ⟨-k, by rw [CG.expo_one, hsk]; push_cast; ring⟩
      exact _root_.GlobalTheory.HodgeOfTrue.isPotCrysAt_of_mono0' hL hF hG hB hGL hD ha hc₀ hν (fun v => hone v) cone (by rwa [inv_one]) k1 k2 H (D.locT l) hw
        (D.nd.plOm.2 w) Bw hj hm' hgood
    · have hsk : (s : ℂ) = k + 1 / 2 := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k + 1 / 2 := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key ξh fun τ => by
        obtain ⟨n, hn⟩ := x4 τ
        exact ⟨n - k, by rw [hn, hsk]; push_cast; ring⟩
      exact _root_.GlobalTheory.HodgeOfTrue.isPotCrysAt_of_mono0' hL hF hG hB hGL hD ha hc₀ hν x1 x2 x3 k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm' hgood
end GlobalTheory.HodgeOfTrue
end
end
