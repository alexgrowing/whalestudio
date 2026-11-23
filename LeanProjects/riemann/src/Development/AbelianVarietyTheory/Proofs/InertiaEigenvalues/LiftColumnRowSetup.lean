import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalErrorBoundPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrystallineLatticeOfJumpPoints
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrCrysAtRangePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LiftExpSplit

open Module

variable {D : D7}

theorem lift_of_window (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hC : C.IsGood)
    (hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)) (hl : D.nd.l i ≠ 2) {ι : Type} {k : ℕ}
    (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (M h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(M : ℤ)) h))
    (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {CA CB CK : ℝ} (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (e' : ℕ)
    (he : CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' : ℝ)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) e' := by
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl (le_trans (le_inf le_rfl hur) le_sup_left)
  have hA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hg hur hl
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₂ hs2
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hg) T₁
      (fun _ => M) (fun _ => h) := fun _ τ _ => hj1 τ
  have h1 := h54.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg hA T₁ T₂ F (fun _ => M) (fun _ => h)
    ⟨hcr1, hcr2, hF'⟩ hJ
  have h2 := (h54.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg T₁ (fun _ => M) (fun _ => h) hcr1 hJ).1 hA
  refine LiftF_mono _ F ?_ h1
  have hp : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by
    rw [(D.loc (D.nd.l i)).PD_p]
  have hl1 : (1 : ℝ) < (D.nd.l i : ℝ) := by exact_mod_cast (D.nd.lPrime i).out.one_lt
  have hH : ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) ≤ ((M + h : ℕ) : ℝ) := by exact_mod_cast Hmax_const_le _ M h
  rw [hp] at h2
  have h3 : CA * (1 + ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) / (D.nd.l i : ℝ) + (1 + Real.logb (D.nd.l i)
        (((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) + 1))) ≤ CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) := by
    apply mul_le_mul_of_nonneg_left _ hCA
    have ha := div_le_div_of_nonneg_right hH (le_of_lt (lt_trans zero_lt_one hl1))
    have hb := Real.logb_le_logb_of_le hl1 (by positivity) (add_le_add_left hH 1)
    linarith
  exact_mod_cast (h2.trans (h3.trans he))

theorem shape_le_eA (L : SizeData₂ D) (CA : ℝ) (l : ℕ) :
    CA * (1 + ((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) / (l : ℝ) +
      (1 + Real.logb l (((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) + 1))) ≤ (eA L CA l : ℝ) := by
  unfold eA
  exact Nat.le_ceil _

theorem mem_window (L : SizeData₂ D) (a : ℤ) (ha : |(a : ℝ)| ≤ Formalism.MainNotions.TwistedPlaces.hB L) :
    a ∈ Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L) := by
  have h1 : a.natAbs ≤ Formalism.MainNotions.N.hN L := by
    unfold Formalism.MainNotions.N.hN
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact ha
  constructor <;> omega

end GlobalTheory.LiftExpSplit

end

namespace GlobalTheory.LiftExpSplit

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → EmbeddingTypes.LiftExponentColumn i (X.r i) (X.dc i) (X.eS i) ∧ EmbeddingTypes.LiftExponentDualPlaces i (X.r i) (X.dc i) (X.eS i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hR hsp
  have hAJ : AdmissibleParameterJ.AdmJ L := hS.facts.admJ L hS.par
  have hJ : AdmissibleParameterJ.JumpConditions L := GlobalTheory.JumpStatement.holds_all D L hAJ
  obtain ⟨⟨ep, hA⟩, -, -, -, he, -, -⟩ := hJ
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hS.canon.fam.good
  have hAA : SumRepresentations.AdmA D := hS.facts.toCore.admA
  have hUC := GlobalTheory.HubX.unrCrysAtRangePrime hP.font D L X hgood hAA.1 hAA.2.2.2.1 hAA.2.2.2.2.2.2
    hS.facts.g2.1 hS.facts.block hS.facts.muUnr i hTw hg hR hsp
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hG2 : EmbeddingTypes.admG2 i (X.r i) ep := GlobalTheory.T.admG2_twist_setup hP D L P nch HW F Cm X C₂ hS ep hA i
  have h2 : D.nd.l i ≠ 2 := fun h => hR.1 (Or.inl (h ▸ D.host.two_mem_small))
  have heS : X.eS i = eA L 23 (D.nd.l i) := hS.canon.data.eS i hsp
  have h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32 :=
    (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := GlobalTheory.T.fontaineAtPlacesOverL D i
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring

  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  rw [heS]
  refine ⟨?_, ?_⟩
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => (hG2 hg0 hg1 w hw C).2.1 x) (fun x => hwinT w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => hUC.2 w hw C hC x) (fun x => hwinD w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))

end GlobalTheory.LiftExpSplit
