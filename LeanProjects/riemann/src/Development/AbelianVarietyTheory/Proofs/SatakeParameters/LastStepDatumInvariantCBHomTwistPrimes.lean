import Mathlib
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
