import Mathlib
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.Columns.LastRowColLevSym
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.ChainLawPhiTop
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceMStatement

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabTopLaw

set_option maxHeartbeats 4000000 in

theorem xiTop_stab_law : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hgS hTS hL hCh hsh hA hb hMd u p Y p' a hY hfix x
  have hm : R.m = m2 + 2 := hL.hm
  have hc : cst.Ok := hL.cst_ok
  have hn : TopNum R (m2 + 1) := topNum_of hm
  have hS : QSep Pr sel mu := qSep_of sel mu hPr hsel hgS
  have hU : QUnif sel mu := qUnif_of sel mu hX hPr hsel
  have hLaw := topLawG_sym Ch sel mu cst control_phi_law hX hPr hm hsh
  have hRow := lastRow_colLevSym Ch hm
  choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu =>
    frsF_smulQ sel mu u p' (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1)) a w
  rw [hfix] at hκ'
  have e0 : phiT X.K p.deco.1 p'.deco.1 (a.1.1.toLinearMap ∘ₗ x) = phiT X.K p.deco.1 p'.deco.1 x := by
    have h := phiT_smul X.K p.deco p'.deco 1 1 a.1 (a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) x
    have hd : (a • p').deco = (a.1, (a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco := rfl
    rw [← hd, hfix, ← Prod.one_eq_mk, one_smul] at h
    exact h

  rw [XiTop_eq, XiTop_eq, e0]

  have hsym : ∀ w z, (frsF sel mu p' w).symm (a.1.1 z) = (κ' w).1.symm ((frsF sel mu p' w).symm z) := by
    intro w z
    have h := hκ' w
    generalize frsF sel mu p' w = F' at h ⊢
    rw [LinearEquiv.symm_apply_eq]
    calc a.1.1 z = (a.1.1 * F' * (κ' w).1) ((κ' w).1.symm (F'.symm z)) := by
          simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      _ = F' ((κ' w).1.symm (F'.symm z)) := by rw [← h]
  have hF : ∀ w, inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x) =
      (κ' w).1.symm.toLinearMap ∘ₗ inFr (frsF sel mu p w) (frsF sel mu p' w) x := by
    intro w
    apply LinearMap.ext
    intro v
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hsym w _

  have hdet : ∀ w, ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) := by
    intro w
    have hd := congrArg (fun f => ((LinearEquiv.det f : X.Eˣ) : X.E)) (hκ' w)
    simp only [map_mul, Units.val_mul] at hd
    have hdF : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hdK : ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hAK : ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) = 1 := by
      have h2 : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) *
          (((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)) =
          ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) * 1 := by
        rw [mul_one]
        conv_rhs => rw [hd]
        ring
      exact mul_left_cancel₀ hdF h2
    have e1 : ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) = ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)⁻¹ := by
      show ((LinearEquiv.det ((κ' w).1)⁻¹ : X.Eˣ) : X.E) = _
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [e1]
    exact eq_inv_of_mul_eq_one_left hAK

  have hmu : ∀ w, muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) := by
    intro w
    rw [hdet w]
    have hun : IsUnit (redP w.1 ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E)) :=
      isUnit_reduction_of_integralAt_inv (intAt_det _ ((κ' w)⁻¹).2) (intAt_det_inv _ ((κ' w)⁻¹).2) (Units.ne_zero _)
    have e2 := GlobalTheory.TopLaw.rhoT_inv (Ch := Ch) (sel := sel) (mu := mu) (m2 + 1) w (κ' w)⁻¹
    rw [inv_inv] at e2
    rw [e2]
    unfold muAt rhoS
    rw [GlobalTheory.LastSteps.locChar_unit _ _ hun]

  have hchr : (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) := by
    rw [prod_uSG_dite hS
      (fun w => (((twLt Ch (m2 + 1 + 1) w).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
      (fun Q => (((twTt (R := R) sel mu (m2 + 1 + 1) Q).lam ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q,
        a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))]
    rw [Units.val_mul, levFam_chr_apply_coe]
    congr 1
    exact piChar_apply_coe' _ _ a.2.2

  have hper : ∀ w : rowSG Pr sel mu,
      muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x)) ((frsF sel mu p w).symm (repY Y)) =
      (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) := by
    intro w
    rw [hmu w, hF w]
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frsF_isFr sel mu p w _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [dif_pos hw]
      obtain ⟨hne, -, hqm⟩ := ybSet_props2 sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have key := topDat_law hc hn hLaw hRow w hw 1 ⟨(a.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩
        1 (κ' w) (fun z _ => by simp) (hκr' w hw) (ciQ_notMem_sq hX hPr hw)
        (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) ((frsF sel mu p w).symm (repY Y)) (by simp) hq
      have h1 : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det ((1 : ↥(GLint X.E (R.N (m2 + 1)) w.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) : X.Eˣ) : X.E) = 1 := by
        simp [rhoS, LocE.unitV, redP_one]
      rw [h1, one_mul, map_one, inv_one, Units.val_one, mul_one] at key
      exact key
    · rw [dif_neg hw]
      obtain ⟨hne, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : X.E) ^ cst.M) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have hQw := (Finset.mem_union.mp w.2).resolve_left hw
      have hc' : (κ' w)⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H := by
        rw [hκQ' w hw, inv_inv]
        exact a.2.2.2 _ (Set.mem_univ _)
      have key := GlobalTheory.T.twTt_k1Depth_twice_m Ch sel mu cst w hw (κ' w) hc' (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y))
        hm hc (hU w.1 hQw) (hL.depthQ w hw) hMd hq
      have e4 : (⟨(κ' w)⁻¹, hc'⟩ : ↥(twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H) =
          ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, hQw⟩, a.2.2.2 _ (Set.mem_univ _)⟩ :=
        Subtype.ext (by show (κ' w)⁻¹ = _; rw [hκQ' w hw, inv_inv])
      rw [e4] at key
      exact key
  rw [hchr]
  have := prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ (phiT X.K p.deco.1 p'.deco.1 x) hper
  linear_combination this

end GlobalTheory.StabTopLaw
