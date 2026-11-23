import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
open IsDedekindDomain GlobalTheory.LamT GlobalTheory.KeyFourth
open GlobalTheory.AllWt

namespace GlobalTheory.KeyPowTw

theorem exists_twSec_key (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (K : (Rul Xo c)ˣ) (C : (c.F →+* ℂ) → ℝ) (hP : HasPts U Z) (hks : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hpq : 1 ≤ Dw.p + Dw.q) (hKmem : (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw)) (hCpos : ∀ σ, 0 < C σ) (hCeq : ∀ σ, ∀ k, ∀ y ∈ ((U (goodOf c σ)).X k).dom, homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C σ) (hval : ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal)) :
    ∃ t : TwSec U x Z (wtOf Dw 0 (-4)), (∀ w, t.lo w = 0) ∧ ∀ σ, t.cInf σ = C σ := by
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · show (2 * (-4) : ℤ) = 4 * (-2)
      norm_num
    · show (wtOf Dw 0 (-4)).1 (τ, (i : ℕ)) = 4 * 1
      rw [hwt (-4) τ i i.2]; norm_num
  have hadd : wtOf Dw 0 (-4) + wtOf Dw 0 4 = 0 := by
    rw [← wtOf_add, add_zero, neg_add_cancel, wtOf_zero]
  have hneg : -wtOf Dw 0 (-4) = wtOf Dw 0 4 := neg_eq_of_add_eq_zero_right hadd
  have hi := idem_mul_idem Z
  set s : Rul Xo c := idem Z * (K : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-4))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hKmem
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex, ← exZ_neg_eq, hneg] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hss' : s * s' = idem Z := by rw [hs, hs', mul_mul_mul_comm, hi, Units.mul_inv, mul_one]
  have hnorm : ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z,
      homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ ∧ homN (U (goodOf c σ)) x (wtOf Dw 0 4) s' z = (C σ)⁻¹ := by
    intro σ z hz
    obtain ⟨hd, hl⟩ := hz
    have h1 := homN_idem (U (goodOf c σ)) x hd hl ((hP.1 σ).2 z ⟨hd, hl⟩ hd)
    have hm : ∀ (m m' : ℤ) (f g : Rul Xo c), homN (U (goodOf c σ)) x (wtOf Dw 0 (m + m')) (f * g) z =
        homN (U (goodOf c σ)) x (wtOf Dw 0 m) f z * homN (U (goodOf c σ)) x (wtOf Dw 0 m') g z := fun m m' f g => by
      rw [← homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) f g z hd, ← wtOf_add, add_zero]
    rw [← wtOf_zero (Dw := Dw)] at h1
    have h2 : homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ := by
      have := hm 0 (-4) (idem Z) K
      rw [zero_add, h1, one_mul] at this
      rw [hs, this, hCeq σ z.1 z.2 hd]
    refine ⟨h2, ?_⟩
    have h5 := hm (-4) 4 s s'
    rw [hss', neg_add_cancel, h1, h2] at h5
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h5.symm)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-4)) s z ≤ D := by
    intro σ hσ
    refine ⟨C σ, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 4) s' z ≤ D := by
    intro σ hσ
    refine ⟨(C σ)⁻¹, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hvs : ∀ w, ∀ v ∈ valOn Z w, v s = v (K : Rul Xo c) := fun w v hv => by
    rw [hs, (isVal_valOn hv).mul, val_idem hv, zero_add]
  let t : TwSec U x Z (wtOf Dw 0 (-4)) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by rw [← exZ_neg_eq, hneg]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, hi]
      idem_inv := by rw [hs', ← mul_assoc, hi]
      mul_inv := hss'
      cInf := C
      cInf_pos := hCpos
      norm_inf := fun σ z hz => (hnorm σ z hz).1
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-4)) s hks hU hpq (even_wtOf _ _) (hmono (-4)) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 4) s' hks hU hpq (even_wtOf _ _) (hmono 4)
          hsm' hsupp' hbd' (G + wtOf Dw 0 (-4)) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun _ => 0
      hi := fun w => 4 * B w
      lo_le := fun w v hv => by
        rw [hvs w v hv]; exact_mod_cast (hval w v (valOn_subset Z w hv)).1
      le_hi := fun w v hv => by
        rw [hvs w v hv]; exact (hval w v (valOn_subset Z w hv)).2
      finite_lo := by simp
      finite_hi := by
        refine (Set.finite_iUnion fun τ => finite_ord (embF c τ)).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, Set.mem_iUnion, not_exists, not_not] at hn
        apply hw
        simp [B, hn]
      pts := hP }
  exact ⟨t, fun _ => rfl, fun _ => rfl⟩

theorem exists_twSec_keyPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨ρ⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hpsi : Nat.card (Psi H) = Module.finrank ℚ E / 2 := GlobalTheory.PeriodCoord.card_cmType H
  have hCb : ∀ σ, Real.log (C σ) ≤ 2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi) :=
    fun σ => by rw [hpsi, hgE]; exact (abs_le.1 (hClog σ)).2
  refine ⟨⟨ρ⟩, fun Z m => ?_⟩
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := exists_twSec_key E H Dw l Xo c r U x Z K C hP ⟨ρ⟩ hU hpq hKmem hCpos hCeq hval
  induction m with
  | zero =>
    have h0 : (0 : WTZ E) = wtOf Dw 0 (-(4 * ((0 : ℕ) : ℤ))) := by simp [wtOf_zero]
    obtain ⟨-, h2, h3, -, -⟩ := TwSec.const_spec (x := x) hP 1 one_ne_zero
    refine ⟨(TwSec.const x hP 1 one_ne_zero).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ (TwSec.const x hP 1 one_ne_zero).lo w
      rw [h3]; simp [vAdd]
    · show Real.log ((TwSec.const x hP 1 one_ne_zero).cInf σ) ≤ _
      rw [h2]; simp
  | succ m ih =>
    obtain ⟨t, htlo, htc⟩ := ih
    have h0 : wtOf Dw 0 (-(4 * (m : ℤ))) + wtOf Dw 0 (-4) = wtOf Dw 0 (-(4 * ((m + 1 : ℕ) : ℤ))) := by
      rw [← wtOf_add, add_zero]; congr 1; push_cast; ring
    refine ⟨(t.mul t₁).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ t.lo w + t₁.lo w
      rw [ht₁lo]; linarith [htlo w]
    · show Real.log (t.cInf σ * t₁.cInf σ) ≤ _
      rw [Real.log_mul (t.cInf_pos σ).ne' (t₁.cInf_pos σ).ne', ht₁c]
      have h1 := htc σ
      have h2 := hCb σ
      push_cast at h1 h2 ⊢
      linarith

end GlobalTheory.KeyPowTw
