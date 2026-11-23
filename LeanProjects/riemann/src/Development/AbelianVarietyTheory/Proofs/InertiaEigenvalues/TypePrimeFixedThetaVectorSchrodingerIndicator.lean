import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReduction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ThPShape

variable {D : D7}

theorem eq_ite_of_top {κ : Type} [Zero κ] [One κ] {b a : ℕ} (M : Matrix (Fin b) (Fin a) κ) (h1 : LowZero a M)
    (h2 : topL a M = 1) (i : Fin b) (j : Fin a) : M i j = if i.val = j.val then 1 else 0 := by
  by_cases hi : i.val < a
  · have := congrFun (congrFun h2 ⟨i.val, hi⟩) j
    unfold topL at this
    rw [dif_pos ⟨i.2, j.2⟩, Matrix.one_apply] at this
    rw [this]
    simp only [Fin.ext_iff]
  · rw [h1 i j (by omega) j.2, if_neg (by omega)]

theorem dvd_of_red {v : FinPl D} {k : Type} [CommRing k] (r : OI v →+* k)
    (hr : ∀ x : OI v, r x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1) {ϖ : OI v} (hϖ : Irreducible ϖ) {x : OI v}
    (hx : r x = 0) : ∃ o : OI v, x = ϖ * o := by
  have h1 : x ∈ IsLocalRing.maximalIdeal (OI v) :=
    (IsLocalRing.residue_eq_zero_iff x).1 ((GlobalTheory.AdjVecLocal.red_eq_zero_iff r hr x).1 hx)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h1
  obtain ⟨o, ho⟩ := h1
  exact ⟨o, by rw [← ho, mul_comm]⟩

theorem red_irr {v : FinPl D} {k : Type} [CommRing k] (r : OI v →+* k)
    (hr : ∀ x : OI v, r x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1) {ϖ : OI v} (hϖ : Irreducible ϖ) : r ϖ = 0 :=
  (GlobalTheory.AdjVecLocal.red_eq_zero_iff r hr ϖ).2
    ((IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit))

theorem red_point (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e)
    {PP : Pl D.host.E} (hP : IsProjAt φ PP) (r : OI v →+* kP PP)
    (hr3 : ∀ (N : Formalism.IndefR.Datum.EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ N ∈ v.adicCompletionIntegers D.host.F,
        r ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ N, h⟩ = resS D.host.F PP ⟨N, hN⟩)
    {x : WO S T} (hx : IsHalf (cA D e) x)
    (hint : ∀ a b, adjCo φ S T (frCo φ βS) (frCo φ βT) x a b ∈ v.adicCompletionIntegers D.host.F) :
    IsIntM (frMapAdj S T βS βT x) ∧
      (∀ a b (h : adjCo φ S T (frCo φ βS) (frCo φ βT) x a b ∈ v.adicCompletionIntegers D.host.F),
        redM PP (frMapAdj S T βS βT x) a b = r ⟨_, h⟩) ∧
      ∀ PP', PP' ≠ PP → redM PP' (frMapAdj S T βS βT x) = 0 := by
  have hφ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).2.1
  have hco := GlobalTheory.AdjVecLocal.adjCo_eq S T βS βT φ hφ x
  have hN : ∀ a b, toEAf D e * frMapAdj S T βS βT x a b = frMapAdj S T βS βT x a b :=
    GlobalTheory.AdjVecLocal.frMapAdj_half S T βS βT hx
  have hI : IsIntM (frMapAdj S T βS βT x) := fun a b =>
    GlobalTheory.AdjVecLocal.mem_int_of_rdE he (hN a b) (by have := hint a b; rwa [hco] at this)
  refine ⟨hI, fun a b h => ?_, fun PP' hne => ?_⟩
  · obtain ⟨h', hh⟩ := hr3 _ (hI a b)
    simp only [redM, dif_pos (hI a b)]
    rw [← hh]
    congr 1
    exact Subtype.ext (congrFun (congrFun hco a) b).symm
  · obtain ⟨hid, -⟩ := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hP).2.2 e he
    obtain ⟨h1, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP hid
    ext a b
    simp only [redM, dif_pos (hI a b), Matrix.zero_apply]
    have e1 : (⟨frMapAdj S T βS βT x a b, hI a b⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        ⟨toEAf D e, h1⟩ * ⟨_, hI a b⟩ := Subtype.ext (hN a b).symm
    rw [e1, map_mul, GlobalTheory.TameProd.resS_idem_eq_zero hid (Ne.symm hne) h1, zero_mul]

theorem thPVec_shape : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ p : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ p → ∀ (PP : Pl D.host.E), PP ∈ Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ x₀ : WO S T, IsHalf (cA D e) x₀ → (∀ a b, adjCo φ S T (frCo φ βS) (frCo φ βT) x₀ a b = if a.val = b.val then 1 else 0) → Shape ψ S T e (halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ 1) x₀ p := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ p hS hT hfS hfT hvec PP hPP v φ e hP he ϖ hϖ x₀ hx₀ hx₀c
  classical
  obtain ⟨-, E, hE, ⟨⟨Tm, hTm⟩, hall⟩⟩ := hvec
  set Φ : WO S T → ℂ := fun x => if IsHalf (cA D E) x ∧ IsIntM (frMapAdj S T βS βT x) then
      omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
        omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0 with hΦdef
  have hp : p = Tm Φ := hall Tm hTm
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hE)
  have hSB : IsSBHalf (cA D E) (latO S T ΛS ΛT fun _ => True) Φ :=
    GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
      (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨hid, -⟩ := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hP).2.2 e he
  have hEe : E * e = e := GlobalTheory.DiagLiftFix.idemSum_mul hE (Finset.mem_union_left _ hPP) hid
  have hee : e * e = e := he.1.1
  have hcE : ∀ x : WO S T, IsHalf (cA D e) x → IsHalf (cA D E) x := fun x hx i j => by
    rw [← hx i j, ← mul_assoc, ← map_mul, hEe]
  obtain ⟨⟨r, -, hr0, -, hr3⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
  have hφ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).2.1
  refine ⟨fun z hz => ?_, fun y hy hyA => ?_⟩
  · obtain ⟨hzh, hzp⟩ := hz
    have hzi : ∀ a b, adjCo φ S T (frCo φ βS) (frCo φ βT) z a b ∈ v.adicCompletionIntegers D.host.F := fun a b => by
      obtain ⟨o, ho⟩ := hzp a b
      rw [ho, ValuationSubring.algebraMap_apply]
      exact (ϖ ^ 1 * o).2
    obtain ⟨hI, hred, hoff⟩ := red_point S T βS βT he hP r hr3 hzh hzi
    have hz0 : ∀ PP', redM PP' (frMapAdj S T βS βT z) = 0 := by
      intro PP'
      by_cases h : PP' = PP
      · subst h
        ext a b
        rw [hred a b (hzi a b), Matrix.zero_apply]
        obtain ⟨o, ho⟩ := hzp a b
        have : (⟨adjCo φ S T (frCo φ βS) (frCo φ βT) z a b, hzi a b⟩ : OI v) = ϖ ^ 1 * o :=
          Subtype.ext (by show adjCo φ S T (frCo φ βS) (frCo φ βT) z a b = _; rw [ho, ValuationSubring.algebraMap_apply])
        rw [this, map_mul, map_pow, red_irr r hr0 hϖ, zero_pow one_ne_zero, zero_mul]
      · exact hoff PP' h
    have hshift : (fun t => Φ (t + z)) = Φ := by
      funext t
      have hh : IsHalf (cA D E) (t + z) ↔ IsHalf (cA D E) t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have := hcE z hzh i j
        simp only [Matrix.add_apply, mul_add, this]
        exact add_left_inj _
      have hi2 : IsIntM (frMapAdj S T βS βT (t + z)) ↔ IsIntM (frMapAdj S T βS βT t) := by
        refine ⟨fun h i j => ?_, fun h => (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT t z h hI).1⟩
        have e1 := congrFun (congrFun (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT t z) i) j
        rw [Matrix.add_apply] at e1
        have : frMapAdj S T βS βT t i j = frMapAdj S T βS βT (t + z) i j - frMapAdj S T βS βT z i j := by
          rw [e1]; ring
        rw [this]
        exact sub_mem (h i j) (hI i j)
      simp only [hΦdef]
      by_cases ht : IsHalf (cA D E) t ∧ IsIntM (frMapAdj S T βS βT t)
      · rw [if_pos ⟨hh.2 ht.1, hi2.2 ht.2⟩, if_pos ht]
        have hr := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT t z ht.2 hI).2
        simp only [hr, hz0, add_zero]
      · rw [if_neg ht, if_neg fun h => ht ⟨hh.1 h.1, hi2.1 h.2⟩]
    rw [hp, ← hTm.trans Φ hSB z (hcE z hzh), hshift]
  · have hyE : IsHalf (cA D (cA D E)) y := fun i j => by
      rw [GlobalTheory.DualPairCheck.cA_cA, ← hy i j, ← mul_assoc, hEe]
    have hmod : (fun t => ψ (symplO S T t y) * Φ t) = ψ (symplO S T x₀ y) • Φ := by
      funext t
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases h0 : Φ t = 0
      · rw [h0, mul_zero, mul_zero]
      · congr 1
        have hc : IsHalf (cA D E) t ∧ IsIntM (frMapAdj S T βS βT t) := by
          by_contra h
          exact h0 (by simp only [hΦdef]; rw [if_neg h])
        have hK : omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT t)) ≠ 0 := by
          intro h
          apply h0
          simp only [hΦdef]
          rw [if_pos hc, h, zero_mul]
        have hK' : LowZero T.rank (redM PP (frMapAdj S T βS βT t)) ∧
            topL T.rank (redM PP (frMapAdj S T βS βT t)) = 1 := by
          unfold omegaK at hK
          split_ifs at hK with hk
          · exact hk PP hPP
          · exact absurd rfl hK
        have ht'h : IsHalf (cA D e) (cA D e • t) := fun i j => by
          show cA D e * (cA D e * t i j) = cA D e * t i j
          rw [← mul_assoc, ← map_mul, hee]
        have hco : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D e • t) = adjCo φ S T (frCo φ βS) (frCo φ βT) t := by
          rw [GlobalTheory.AdjVecLocal.adjCo_eq S T βS βT φ hφ, GlobalTheory.AdjVecLocal.adjCo_eq S T βS βT φ hφ,
            GlobalTheory.AdjVecLocal.frMapAdj_smul]
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hφ, he.2.2, one_mul]
        have hent : ∀ a b, ∃ h : adjCo φ S T (frCo φ βS) (frCo φ βT) t a b ∈ v.adicCompletionIntegers D.host.F,
            r ⟨_, h⟩ = if a.val = b.val then 1 else 0 := fun a b => by
          obtain ⟨h, hh⟩ := hr3 _ (hc.2 a b)
          have e2 : adjCo φ S T (frCo φ βS) (frCo φ βT) t a b = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (frMapAdj S T βS βT t a b) := by
            rw [GlobalTheory.AdjVecLocal.adjCo_eq S T βS βT φ hφ]; rfl
          refine ⟨e2 ▸ h, ?_⟩
          have e3 := eq_ite_of_top _ hK'.1 hK'.2 a b
          simp only [redM, dif_pos (hc.2 a b)] at e3
          rw [← e3, ← hh]
          congr 1
          exact Subtype.ext e2
        have hzA : cA D e • t - x₀ ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ 1 := by
          refine ⟨fun i j => ?_, fun a b => ?_⟩
          · simp only [Matrix.sub_apply, mul_sub]
            rw [ht'h i j, hx₀ i j]
          · have hadd : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D e • t - x₀) a b =
                adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D e • t) a b - adjCo φ S T (frCo φ βS) (frCo φ βT) x₀ a b := by
              have := congrArg (fun M => M a b) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (cA D e • t - x₀) x₀)
              simp only [sub_add_cancel, Matrix.add_apply] at this
              simp only [GlobalTheory.AdjVecLocal.adjCo_eq S T βS βT φ hφ, Matrix.map_apply, this, map_add]
              ring
            obtain ⟨h, hh⟩ := hent a b
            have hmem : adjCo φ S T (frCo φ βS) (frCo φ βT) t a b - (if a.val = b.val then 1 else 0) ∈
                v.adicCompletionIntegers D.host.F :=
              sub_mem h (by split_ifs; exacts [one_mem _, zero_mem _])
            have hr' : r ⟨_, hmem⟩ = 0 := by
              have : (⟨_, hmem⟩ : OI v) = ⟨_, h⟩ - (if a.val = b.val then 1 else 0) := by
                apply Subtype.ext
                split_ifs <;> simp
              rw [this, map_sub, hh]
              split_ifs <;> simp
            obtain ⟨o, ho⟩ := dvd_of_red r hr0 hϖ hr'
            refine ⟨o, ?_⟩
            rw [hadd, hco, hx₀c a b, pow_one, ← ho, ValuationSubring.algebraMap_apply]
        have hψ1 := hyA _ hzA
        have hsy : symplO S T t y = symplO S T (cA D e • t) y := by
          rw [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA, (GlobalTheory.SplitScalar.isHalf_iff e y).1 hy]
        have hsub : symplO S T (cA D e • t) y = symplO S T (cA D e • t - x₀) y + symplO S T x₀ y := by
          rw [GlobalTheory.SplitScalar.symplO_sub_left]; ring
        rw [hsy, hsub, AddChar.map_add_eq_mul, hψ1, one_mul]
    rw [hp, ← hTm.modul Φ hSB y hyE, hmod, map_smul]

end GlobalTheory.ThPShape

end
