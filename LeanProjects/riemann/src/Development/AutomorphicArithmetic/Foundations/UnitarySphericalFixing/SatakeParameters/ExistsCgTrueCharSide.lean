import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LiftToGlobalDescentData

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocGL GlobalTheory.HeightCounting GlobalTheory.HeightCounting.TrueSide UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section Twist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} [IsTotallyComplex E]
  (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)

include hF in
theorem locPar_twist (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w)
    (hg : Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E))) :
    ParLaws.locPar hL (π.twist χ) h = (ParLaws.locPar hL π h).lpChar (ParLaws.locPar hL (CG.ofChar χ) h) := by
  obtain ⟨_, _, _, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, ParLaws.locPar, ParLaws.locPar, cls_loc_twist]
  have _ := hF
  exact Old.twist H _ _ _ hg

include hF in
theorem locPar_tw (π : CG E a) (χ : CG E 1) (h : IsPlaceOver A w)
    (hg : Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E))) :
    ParLaws.locPar hL (π.tw χ) h = (ParLaws.locPar hL π h).lpChar (ParLaws.locPar hL χ h) := by
  rw [CG.tw, locPar_twist hL hF _ _ _ hg, CG.ofChar_toChar]

end Twist

namespace Old

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (s : Sw) (C : CGTrue hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := s.elim

theorem cgSurj (C : CGTrue hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ :=
  fun a h ρ _ => C.surj a h ρ

def cgMk (s : Sw) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (_good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (_surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (_zero : IsEmpty (D.naut.CG 0))
    (_loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w)
    (_tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (_inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (_csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrue hL D T := False.elim s

end Old

namespace New

variable {hL : RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem cgGood (_ : TrivialCondition) (C : CGTrueT hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := C.good

theorem cgSurj (C : CGTrueT hL D T) : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, C.e a π = ρ := C.surj

def cgMk (_ : TrivialCondition) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (good : ∀ a (π : D.naut.CG a), GoodAll (e a π))
    (surj : ∀ a, 0 < a → ∀ ρ : HostCGu D.host a, GoodAll ρ → ∃ π, e a π = ρ) (zero : IsEmpty (D.naut.CG 0))
    (loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLawsT.locGT hL D.nd.plOm (e a π) w)
    (tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ))
    (inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ)
    (csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd) : CGTrueT hL D T :=
  ⟨e, good, surj, zero, loc, tw, inf, csd⟩

theorem locParT_unr_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLawsT.locParT hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hL h
  rw [ParLawsT.locParT_ofChar_eq, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_cgTrue_charSide : ∀ hL : RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (D : D7)
    (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (cf : CharFrame D), (∀ k v, cf.P.Div k (D.naut.plGw k v)) →
    ∃ K : CGK D.naut, Nonempty (CGTrueT hL (setCG D hE K) (wdCG hE K T)) ∧ Nonempty (CharSide (setCG D hE K) (cfCG hE K cf)) := by
  intro hL _ D hE T cf hP
  haveI := host_isCMField D.host
  obtain ⟨η, η', e1, e2, h1, h2, h3, h4⟩ := etaLawsT hL D cf.isEta
  refine ⟨trueKT hL D T η η' h1 h2 h3 h4, ⟨trueCGT hL D hE T η η' h1 h2 h3 h4⟩, ⟨
    { e1 := (Equiv.subtypeUnivEquiv (fun π => ⟨Nat.one_pos, goodAll_one π⟩)).trans (CGu.equivChar D.host.E)
      unr_iff := fun π w => ?_
      frob := fun π w hu => ?_
      tw := fun π χ => CGu.equivChar_tw π.1 χ.1
      infG := fun π a ha g => ?_
      csd := fun π => ?_
      etaT := ?_
      etaTinv := ?_
      plGw := hP }⟩⟩
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change D.naut.unr ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) ↔ (CGu.equivChar D.host.E π.1).1.UnrAt w
    rw [e, equivChar_ofU]
    exact (unr_symm T w _).trans (locParT_unr_iff hL χ (D.nd.plOm.2 w))
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.UnrAt w at hu
    change D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hL D.nd.plOm π.1 w)) =
      {(((CGu.equivChar D.host.E π.1).1.val w)⁻¹ : ℂˣ).1}
    rw [e, equivChar_ofU] at *
    have h5 := locParT_unr hL χ (D.nd.plOm.2 w) hu
    exact (frob_symm T w _ h5.1).trans h5.2
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change (CGu.equivChar D.host.E π.1).1.HasInfQ (embPsi D.host) a at ha
    change π.1.1.infChar (embPsi D.host g) = {(a g : ℂ)} ∧
      π.1.1.infChar ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
    rw [e, equivChar_ofU] at *
    exact infChar_ofChar_of_hasInfQ D.host χ a ha g
  · obtain ⟨χ, h, e⟩ := exists_ofU π.1
    change π.1.1.IsCsd ↔ IsCSD D.host (CGu.equivChar D.host.E π.1).1
    rw [e, equivChar_ofU]
    exact isCsd_ofChar_iff D.host χ
  · exact (congrArg CG.toChar e1).trans (CG.toChar_ofChar _)
  · exact (congrArg CG.toChar e2).trans (CG.toChar_ofChar _)

end New

end UpperTheory.One.M

end
