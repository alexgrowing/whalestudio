import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.PropositionTwoFiveFamilyOfAdmitted
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Imports
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Formalism.SharpRestriction.SmoothDesignExistence.AtMostOneExceptionalRealCharacter
import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLd
import Formalism.LocalToGlobal.Divisibility.BrJoint

noncomputable section

namespace Formalism.MainNotions.Wire

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk Formalism.L2.GlobalTheoryTheory

theorem s59 (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i) :=
  Closed.of_all fun Fm _ => UnusedSlot33.family_finite_order_holds Fm

theorem lemma_one_seven_closed (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => EvD Fm UnusedSlot33.division_rows_rational_lattice :=
  Closed.of_all fun Fm _ => EvD.of_all Fm UnusedSlot33.division_rational_lattice

theorem hLit (𝒞 : FamClass) (h6 : Closed 𝒞 fun Fm _ => ShortIntervalPrimes.FamilySixthHypothesis Fm) :
    Closed 𝒞 fun Fm _ => ShortIntervalPrimes.FamilySixthHypothesis Fm ∧ ShortIntervalPrimes.adm7F Fm ∧ ShortIntervalPrimes.ComplementTwoFamily Fm :=
  h6.imp fun Fm _ _ h => ⟨h, ShortIntervalPrimes.family_explicit_formula_holds Fm, ShortIntervalPrimes.family_zero_window_holds Fm⟩

theorem t7 (𝒞 : FamClass) (C0 : ℝ) (h : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → LLKerE Fm) :
    Closed (Des 𝒞 C0) fun Fm _ => flipTwoThree.admF7 Fm :=
  kernel_ratio_closed_of_class fun Fm hc => h Fm hc.1.1.1

theorem log_gamma_small_family {eps : ℝ} (Fm : FamP eps) : ShortIntervalPrimes.compactDualInputFamily Fm := ShortIntervalPrimes.family_log_gamma_small_holds Fm

theorem log_X_lower_family_of_theorems {eps : ℝ} (Fm : FamP eps) (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass)
    (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap) : ShortIntervalPrimes.proportionalityInputFamily Fm :=
  ShortIntervalPrimes.log_X_lower_of_corollary_five_six Fm (StandardLattice.division_level_prime_family Fm h2b h2v h3)

structure FamGLmin (𝒞 : FamClass) (C5 : ℝ) : Prop where
  h2b : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.MassRatio₂
  h2v : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass
  h3 : Closed 𝒞 fun Fm _ => flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap
  hZa : Closed 𝒞 fun Fm _ => flipTwoThree.FamilySlopeLowerOpenPart Fm
  hZb : Closed 𝒞 fun Fm _ => flipTwoThree.FamilySlopeMaxOpenPart Fm C5
  tCV : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  hW : Closed 𝒞 fun Fm _ => FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)
  hμ : Closed 𝒞 fun Fm _ => FamU Fm product_first_zeroth_parts.SlopeLine
  hI : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.HeckeIntegralLevelZero
  hR : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero
  hB : Closed 𝒞 fun Fm _ => FamU Fm LocalLatticeBases.SecondBranchInclusionLength

theorem linkGLOBAL_of_7 {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) (h : LinkGLOBAL7 Fm Cabs CH C0 eD eL)
    (hc : Fm.CoverAll) : LinkGLOBAL Fm Cabs CH C0 eD eL :=
  fun hCh hIn => h (Formalism.L2.GlobalTheoryTheory.Loss7.loss_requirements_of_local_input Fm C0 CH hCh hIn.1 hc) hIn

theorem linkGLOBAL_of_7w {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) (h : LinkGLOBAL7 Fm Cabs CH C0 eD eL)
    (hW : ChosenWall Fm) : LinkGLOBAL Fm Cabs CH C0 eD eL :=
  fun hCh hIn => h (Formalism.L2.GlobalTheoryTheory.Loss7.loss_requirements_of_small_shares Fm C0 CH hCh hW) hIn

theorem FamGLmin.link7 {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (Cabs C0 : ℝ) (hCabs : 0 ≤ Cabs) (hC0 : 3 ≤ C0) :
    Closed 𝒞 fun Fm CH => TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  ((closed_CH 𝒞).and (h.h2b.and (h.h2v.and (h.h3.and (h.hZa.and (h.hZb.and (h.tCV.and (h.hW.and (h.hμ.and
    (h.hI.and (h.hR.and h.hB))))))))))).imp
    fun Fm CH _ ⟨hCH, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ =>
      linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11

theorem FamGLmin.link {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (Cabs C0 : ℝ) (hCabs : 0 ≤ Cabs) (hC0 : 3 ≤ C0) :
    Closed 𝒞 fun Fm CH => Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs 0 :=
  (h.link7 Cabs C0 hCabs hC0).imp fun Fm CH _ l hc hT _ => linkGLOBAL_of_7 Fm Cabs CH C0 Cabs 0 (l hT) hc

theorem FamGLmin.link8 {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (Cabs C0 : ℝ) (hCabs : 0 ≤ Cabs) (hC0 : 3 ≤ C0)
    (hW : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ChosenWall Fm) :
    Closed 𝒞 fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs 0 :=
  ((h.link7 Cabs C0 hCabs hC0).and (Closed.of_class (P := fun Fm _ => ChosenWall Fm) fun Fm _ hc => hW Fm hc)).imp
    fun Fm CH _ ⟨l, hWa⟩ hT _ => linkGLOBAL_of_7w Fm Cabs CH C0 Cabs 0 (l hT) hWa

theorem family_theorems_two_and_five {eps : ℝ} (Fm : FamP eps) (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u))
    (hμ : FamU Fm product_first_zeroth_parts.SlopeLine) (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    FamU Fm product_first_zeroth_parts.family_property_and ∧ FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound :=
  ⟨(hW.and hμ).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zeroth_parts.division_side_conditions_at_sizeData hS W hm,
   (hB.and (hI.and hR)).mono fun _ _ hS h => LocalLatticeBases.congruence_no_kernel_minimal hS h.1 h.2.1 h.2.2⟩

theorem FamGLmin.muRank {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (C0 : ℝ) (hC0 : 0 < C0) :
    Closed 𝒞 fun Fm CH => TuSize Fm → ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm :=
  (h.hW.and (h.hμ.and (h.hI.and (h.hR.and h.hB)))).imp fun Fm _ _ ⟨hW, hμ, hI, hR, hB⟩ hTu hCh => by
    have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
    obtain ⟨hT2, hT5⟩ := family_theorems_two_and_five Fm hW hμ hI hR hB
    have hE : J.LvlF Fm := lvlF_of Fm tSet hT2 hT5
    have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_min Fm hE)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
    exact ⟨hNF, muRank_min Fm hC0 cPr hNF hE tSet⟩

theorem FamGLmin.muRank7 {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5) (C0 : ℝ) (hC0 : 0 < C0) :
    Closed 𝒞 fun Fm CH => TuSize Fm → WeightVectorSmallSharesSeven Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm :=
  (h.hW.and (h.hμ.and (h.hI.and (h.hR.and h.hB)))).imp fun Fm _ _ ⟨hW, hμ, hI, hR, hB⟩ hTu hCh => by
    obtain ⟨hT2, hT5⟩ := family_theorems_two_and_five Fm hW hμ hI hR hB
    obtain ⟨_, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
    exact muRank_items Fm C0 hC0 hT2 hT5 hTu cPr

theorem FamGLmin.nuFull {𝒞 : FamClass} {C5 : ℝ} (h : FamGLmin 𝒞 C5)
    (hTu : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) : Closed 𝒞 fun Fm _ => NuFullF Fm :=
  ((h.hW.and (h.hμ.and (h.hI.and (h.hR.and h.hB)))).and
    (Closed.of_class (P := fun Fm _ => TuSize Fm) fun Fm _ hc => hTu Fm hc)).imp
    fun Fm _ _ ⟨⟨hW, hμ, hI, hR, hB⟩, hT⟩ => by
      obtain ⟨hT2, hT5⟩ := family_theorems_two_and_five Fm hW hμ hI hR hB
      exact nuFullF_of Fm (nuCommensF_min Fm (lvlF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hT) hT2 hT5))

end Formalism.MainNotions.Wire

namespace Formalism.MainNotions.Wire

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

def BrExists (D : D7) (u : D.what₂.Word) : Prop := ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

def IncidenceTransportConditionsWithoutExistence (D : D7) (u : D.what₂.Word) : Prop := product_first_zeroth_parts.UpDownIncidenceInverse D u ∧ product_first_zeroth_parts.admT D u ∧ product_first_zeroth_parts.admB D u

theorem packet_conditions_iff_pure (D : D7) (u : D.what₂.Word) : IncidenceTransportConditions D u ↔ IncidenceTransportConditionsWithoutExistence D u ∧ BrExists D u :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩, fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

theorem packet_conditions_closed (𝒞 : FamClass)
    (hT : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditionsWithoutExistence (Fm.D x i) u)
    (hB : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), BrExists (Fm.D x i) u) :
    Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u :=
  (hT.and hB).imp fun _ _ _ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ =>
    ⟨max a b, fun x hx i u => (packet_conditions_iff_pure _ u).2
      ⟨ha x (le_trans (le_max_left _ _) hx) i u, hb x (le_trans (le_max_right _ _) hx) i u⟩⟩

theorem brExists_of {D : D7} {u : D.what₂.Word} (H : PrimeDegreeVariant.Conclusion6) (P : product_first_zeroth_parts.Pend D u) (tie : J.BrTie P) : BrExists D u :=
  ⟨P, J.pending_condition_of_sixth P H tie⟩

theorem brExists_of_tie {D : D7} {u : D.what₂.Word} (P : product_first_zeroth_parts.Pend D u) (tie : J.BrTie P) : BrExists D u :=
  brExists_of Formalism.L2.DIV.BrJ.branching_interlacing_pairs P tie

open Formalism.MainNotions.flipTwoThree in

theorem mass_count_uniform_constant (C₀ : ℝ) (h2 : 2 ≤ C₀) : ∃ C : ℝ, ∀ (Cn : ℝ) (D : D7) (x : ℝ), MsCount D C₀ → Conclusion1 D Cn C x := by
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.moduli_arithmetic_bound C₀ (by linarith)
  refine ⟨2 * max C 0, fun Cn D x hM u b L b' Sc eta hN hT => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  have hNum := numbers_of_nums 1 le_rfl (by have := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1; linarith) hN
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv1 : 1 ≤ D.host.v := hNum.one_le_v
  set lT := Real.log (Tu D u) with hlT
  set lg := Real.log ((D.host.g 0 : ℝ) * D.host.g 1) with hlg
  have hlT0 : 0 ≤ lT := hNum.logT_nonneg
  have hlg0 : 0 ≤ lg := hNum.logg_nonneg
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hxb : b ≤ x * b := by nlinarith
  have hxbv : x * b ≤ x * b * D.host.v := le_mul_of_one_le_right (by positivity) hv1
  have hNle : (D.R.N D.R.m : ℝ) ≤ x * b * D.host.v := by
    have h1 := hNum.lin
    have h0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
    have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L := le_mul_of_one_le_right h0 hL1
    linarith
  have hlogn : ∀ n : ℕ, 1 ≤ n → n ≤ D.R.N D.R.m → Real.log n ≤ L := fun n h1 h2 => by
    refine le_trans (Real.log_le_log (by exact_mod_cast h1) ?_) hNum.log_av
    have : (n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h2
    linarith
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfN : D.R.f ≤ D.R.N D.R.m := by
    have := D.R.f_le_k
    unfold Ranks.f Ranks.n Ranks.N
    omega
  have hlv : Real.log D.host.v ≤ L := by
    refine le_trans (Real.log_le_log (by linarith) ?_) hNum.log_av
    have : (1 : ℝ) ≤ x * b := by nlinarith
    exact le_mul_of_one_le_left (by linarith) this
  have step : ∀ (n : ℕ) (logh : ℝ), 1 ≤ n → n ≤ D.R.N D.R.m → logh ≤ msBound D u C₀ n →
      logh ≤ 2 * max C 0 * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L + lT + lg) := by
    intro n logh hn1 hnN hh
    have hfn : (0 : ℝ) ≤ (D.R.f : ℝ) * (n : ℝ) ^ 2 := by positivity
    have key := hC D.R.f n D.host.v (Tu D u) L (lT + lg) _ logh hf1 hn1 hv1 hT1 hL1 (by linarith)
      (hlogn _ hf1 hfN) (hlogn _ hn1 hnN) hlv rfl (by
        refine le_trans hh ?_
        unfold msBound
        have e1 : 2 * (D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg) ≤
            (D.R.f : ℝ) * n * lT + C₀ * D.R.f * (n : ℝ) ^ 2 * (lT + lg) := by
          have a1 : 0 ≤ (D.R.f : ℝ) * n * lT := by positivity
          have a2 : 2 * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg)) ≤ C₀ * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg)) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          linarith
        linarith)
    refine le_trans key ?_
    have hn2 : (n : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 2 := by
      have : (n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hnN
      exact pow_le_pow_left₀ (by positivity) this 2
    have hCp : C ≤ max C 0 := le_max_left _ _
    have hCp0 : 0 ≤ max C 0 := le_max_right _ _
    generalize max C 0 = Cp at hCp hCp0
    calc C * D.R.f * (n : ℝ) ^ 2 * (L + lT + (lT + lg))
        = C * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (L + lT + (lT + lg))) := by ring
      _ ≤ Cp * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (L + lT + (lT + lg))) :=
          mul_le_mul_of_nonneg_right hCp (by positivity)
      _ ≤ Cp * ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (2 * (L + lT + lg))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCp0
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn2 (by positivity)) (by linarith) (by positivity)
            (by positivity)
      _ = 2 * Cp * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L + lT + lg) := by ring
  obtain ⟨m1, m2⟩ := hM u hT
  have hk := D.R.m_add_three_le_k
  refine ⟨fun i hi => step _ _ ?_ ?_ (m1 i hi), step _ _ ?_ (Nat.sub_le _ _) m2⟩
  · unfold Ranks.N; omega
  · unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  · unfold Ranks.N; omega

theorem mass_count_uniform_holds : ∃ C : ℝ, ∀ (Cn : ℝ) (D : D7) (x : ℝ), flipTwoThree.Conclusion1 D Cn C x :=
  let ⟨C, hC⟩ := mass_count_uniform_constant 90 (by norm_num)
  ⟨C, fun Cn D x => hC Cn D x (flipTwoThree.msCount_holds D)⟩

theorem VolumeRatio₂ (Cn Cd : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x Cth : ℝ), flipTwoThree.adm2 D Cn Cth x → flipTwoThree.Conclusion2 D Cn Cd C x :=
  let ⟨C1, h1⟩ := mass_count_uniform_holds
  let ⟨C, hC⟩ := flipTwoThree.opNorm_estimate_of_theta_mass Cn Cd C1
  ⟨C, fun D x Cth h2 => hC D x Cth h2 (h1 Cn D x)⟩

theorem counting_constant_as_function (Cd : ℝ) : ∃ K : ℝ → ℝ, ∀ (Cn : ℝ) (D : D7) (x Cth : ℝ), flipTwoThree.adm2 D Cn Cth x → flipTwoThree.Conclusion2 D Cn Cd (K Cn) x :=
  ⟨fun Cn => Classical.choose (VolumeRatio₂ Cn Cd), fun Cn => Classical.choose_spec (VolumeRatio₂ Cn Cd)⟩

end Formalism.MainNotions.Wire

end
