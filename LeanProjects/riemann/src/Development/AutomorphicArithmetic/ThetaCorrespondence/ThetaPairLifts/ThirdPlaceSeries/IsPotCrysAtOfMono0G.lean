import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.IsPotCrysAtOfMono0G
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsChar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AHodgeDgoodOfUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAlgNorm
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

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
theorem isPotCrysAt_of_mono0' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {π₀ : CuspSub E a} (ha : 2 ≤ a) (hc : π₀.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s)
    {ξ : HChar E} (hξu : ∀ v, ξ.UnrAt v) (hξc : (CG.ofChar ξ).IsCsd) (hξc' : (CG.ofChar ξ⁻¹).IsCsd)
    (hreg : (CG.mk (π₀.twist ξ)).IsRegAlg) (hint : ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n)
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : _root_.UpperTheory.GalS.IsGalUAlt (π₀.twist ν) χ ι r wt HT)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hm : UpperTheory.GalS.NcW (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) h))
    (hgood : UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion E))) :
    IsPotCrysAt P Bw (r.comp (Dec (F := E) A).subtype) := by
  have hc' : (π₀.twist ξ).IsCsd := CG.IsCsd.twist hξc (π := CG.mk π₀) hc
  obtain ⟨r₀, wt₀, HT₀, H₀, K₀⟩ := hGL E Ω l ι a ha _ hc' hreg
  have e0 : (π₀.twist ξ).twist (ξ⁻¹ * ν) = π₀.twist ν := by
    rw [← CuspSub.twist_mul, mul_inv_cancel_left]
  have hψu : ∀ v, (ξ⁻¹ * ν).UnrAt v := fun v => (hξu v).inv.mul (hν.1 v)
  have hp : ∃ χ', IsPolarized ((CuspSub.triv E (le_refl 1)).twist (ξ⁻¹ * ν)) χ' := by
    rw [CuspSub.twist_mul]
    exact isPolarized_twist hξc' hν
  obtain ⟨c, hcc, hcf, hcr⟩ := _root_.GlobalTheory.HodgeOfTrue.exists_galois_character_crystalline_at_places (Ω := Ω) hL hF hG ι (ξ⁻¹ * ν) hψu hint hp
  have hc0 : Continuous fun g => (r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H₀.cont
  have hc1 : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  have hc2 : Continuous fun g => (twistBy c r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [coe_twistBy]
    exact (Units.continuous_val.comp hcc).smul hc0
  obtain ⟨B, hBc⟩ := conj_of_frob hD hc1 hc2 H.ss (isSSRep_twistBy c H₀.ss) (by
    filter_upwards [eventually_natCast_notMem E l, _root_.GlobalTheory.CuspRep.ParLaws.eventually_unramified_local_parameter (Ω := Ω) hL hF (CG.mk (π₀.twist ξ))] with w hl hu Bp g hBp hg
    have e3 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) hBp =
        (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) hBp).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar (ξ⁻¹ * ν)) hBp) := by
      rw [← e0]
      exact _root_.UpperTheory.One.M.locPar_twist_alt hL hF (CG.mk (π₀.twist ξ)) _ hBp (_root_.GlobalTheory.HodgeOfTrue.llc_good_of_locPar_unr hL _ hBp (hu _ hBp))
    obtain ⟨y1, y2⟩ := _root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL (ξ⁻¹ * ν) hBp (hψu w)
    have u1 := hu _ hBp
    have e1 := H.eq_locPar hL hF hl hBp (by rw [e3]; exact WD.unr_lpChar _ _ u1 y1)
    have e2 := H₀.eq_locPar hL hF hl hBp u1
    have u2 : (wdOf hBp hl ι r).unr := by rw [e1, e3, WD.unr_tw]; exact WD.unr_lpChar _ _ u1 y1
    have u3 : (wdOf hBp hl ι r₀).unr := by rw [e2, WD.unr_tw]; exact u1
    have f1 := frobEig_wdOf hl ι hc1 u2 hBp hg
    have f2 := frobEig_wdOf hl ι hc0 u3 hBp hg
    rw [e1, e3, WD.frobEig_tw _ _ (WD.unr_lpChar _ _ u1 y1), WD.frobEig_char _ _ _ u1 y1 y2] at f1
    rw [e2, WD.frobEig_tw _ _ u1] at f2
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [f1, coe_twistBy]
    have f3 : (((c g : Qbar l) • (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))).charpoly.map ι.toRingHom) =
        ((ι (c g : Qbar l)) • ((r₀ g : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom)).charpoly := by
      rw [← Matrix.charpoly_map]
      congr 1
      ext i j
      simp
    rw [f3, GlobalTheory.Triple.charpoly_smul_of_prod _ _ _ (by rw [Matrix.charpoly_map]; exact f2), hcf w hl Bp g hBp hg]
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    congr 2
    ring)
  obtain ⟨σ₁, hσ₁, -⟩ := LocEx.exists_isLocComp hF E a (π₀.twist ξ) w
  have g2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (algNorm σ₁) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2) := by
    rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) σ₁]
    exact congrArg (fun x : WD h => x.lpTw _) (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₁ h).symm
  have hn : UpperTheory.GalS.NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2)) := by
    have e4 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h =
        (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) h).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ξ) h) :=
      _root_.UpperTheory.One.M.locPar_twist_alt hL hF (CG.mk π₀) ξ h hgood
    rw [e4]
    exact (hm.char (_root_.GlobalTheory.CuspRep.ParLaws.dim_local_parameter_eq_rank hL _ h) (_root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ξ h (hξu w)).1).tw _
  have g1 := K₀ P AI ⟨T⟩ w hw A h O Bw hj σ₁ hσ₁ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (g2 ▸ hn)
  have hm' : (wdAt P ι Bw h hj (r₀.comp (Dec (F := E) A).subtype)).mono0 := g1.mono (g2 ▸ hn.2.1)
  have hab := H₀.above P AI ⟨T⟩ w A h O Bw hj
  have hpst := hB.isPstAt T Bw (r₀.comp (Dec (F := E) A).subtype) (H₀.cont.comp continuous_subtype_val |> Units.continuous_val.comp)
    (hab.deRham (_root_.UpperTheory.GalS.nice_of_loc_par hL hF h hn))
  have hpot := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι _ hpst).1 hm'
  have hpot2 := potCrys_twistBy T Bw (c.comp (Dec (F := E) A).subtype) (r₀.comp (Dec (F := E) A).subtype) hpot
    (hcr P AI ⟨T⟩ w A h O Bw hj)
  refine (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ (r.comp (Dec (F := E) A).subtype) B⁻¹ (fun g => ?_)).2.2.1 hpot2
  have := hBc g
  change r g = B⁻¹ * twistBy c r₀ g * B⁻¹⁻¹
  rw [this]
  group
end G
end GlobalTheory.HodgeOfTrue
end
end
