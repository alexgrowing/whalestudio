import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.DualSep

variable {D : D7}

theorem algebraMap_OI {v : FinPl D} (o : OI v) : algebraMap (OI v) (Fv D.host.F v) o = (o : Fv D.host.F v) := rfl

theorem mem_pow_iff {v : FinPl D} (ϖ : OI v) (hϖ : (ϖ : Fv D.host.F v) ≠ 0) (N : ℕ) (x : Fv D.host.F v) :
    (∃ o : OI v, x = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)) ↔
      Valued.v x ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have ho : Valued.v (o : Fv D.host.F v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 o.2
    calc Valued.v (ϖ : Fv D.host.F v) ^ N * Valued.v (o : Fv D.host.F v)
        ≤ Valued.v (ϖ : Fv D.host.F v) ^ N * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ
    have hv : 0 < Valued.v ((ϖ : Fv D.host.F v) ^ N) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hp
    have hmem : x / (ϖ : Fv D.host.F v) ^ N ∈ v.adicCompletionIntegers D.host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hv, map_pow]
      exact h
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow]
    show x = (ϖ : Fv D.host.F v) ^ N * (x / (ϖ : Fv D.host.F v) ^ N)
    rw [mul_div_cancel₀ _ hp]

theorem adjCo_smul {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (s : AE D) (z : WO S T) :
    adjCo φ S T BS BT (cA D s • z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • adjCo φ S T BS BT z := by
  have h1 : ((cA D s • z : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      s • (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) := by
    ext i j
    simp [GlobalTheory.DualPairCheck.cA_cA]
  have h2 : ∀ (M : Matrix (Fin S.rank) (Fin T.rank) (AE D)),
      (s • M).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • M.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) := by
    intro M; ext i j; simp
  unfold adjCo
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.DownLift.GenSplit.DualSep

namespace GlobalTheory.DownLift.GenSplit

open DualSep in

theorem exists_sep_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ N x hx hxN
  obtain ⟨a, -, ha0, -, himg⟩ := (GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he).2
  have hα : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) ≠ 0 := by
    rw [← GlobalTheory.SplitProjChart.emb_apply]
    exact (map_ne_zero _).2 (star_ne_zero.2 ha0)
  have hϖ0 : (ϖ : Fv D.host.F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ0
  set c : Fv D.host.F v := GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) / (ϖ : Fv D.host.F v) ^ N with hcdef
  have hc : c ≠ 0 := div_ne_zero hα hp
  obtain ⟨s, hs⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.1 c
  have hcoef : ∀ z : WO S T, adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) =
      c • adjCo φ S T (frCo φ βS) (frCo φ βT) z := fun z => by rw [adjCo_smul, hs]
  have hval : ∀ m : Fv D.host.F v, Valued.v (c * m) ≤ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) ↔
      Valued.v m ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
    intro m
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = c * (ϖ : Fv D.host.F v) ^ N := by
      rw [hcdef, div_mul_cancel₀ _ hp]
    rw [e1, map_mul, map_mul, map_pow, mul_le_mul_iff_right₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
  have hinPow : ∀ z : WO S T, InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) ↔
      ∀ i j, Valued.v ((c • adjCo φ S T (frCo φ βS) (frCo φ βT) z) i j) ≤
        Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) := by
    intro z
    unfold InPow
    simp only [Matrix.smul_apply, smul_eq_mul, hval, mem_pow_iff ϖ hϖ0 N]
  have hhalf : ∀ z : WO S T, IsHalf (cA D e) z → IsHalf (cA D e) (cA D s • z) := by
    intro z hz
    rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hz]
  have hcoord := (GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)).1
  have hmem : ∀ z : WO S T, IsHalf (cA D e) z → InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) →
      cA D s • z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro z hz hzN
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) ∈ adjCo φ S T (frCo φ βS) (frCo φ βT) ''
        {t | t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
          IsHalf (cA D e) t} := by
      rw [himg, hcoef]
      exact (hinPow z).1 hzN
    obtain ⟨t, ⟨htΛ, htH⟩, hteq⟩ := h1
    have h2 : t = cA D s • z := hcoord.2.1.injOn htH (hhalf z hz) hteq
    rw [← h2]
    exact htΛ
  have hnot : cA D s • x ∉
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro hmx
    apply hxN
    rw [hinPow]
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤
          Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a))} := by
      rw [← himg]
      exact ⟨_, ⟨hmx, hhalf x hx⟩, rfl⟩
    rw [hcoef] at h1
    exact h1
  have hsd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hse := GlobalTheory.SplitScalar.isSplitIdem_conj he.1
  obtain ⟨l, hlΛ, hlH, hne⟩ := GlobalTheory.SplitScalar.exists_dual_half hse hsd
    (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1.1 u hu) (hhalf x hx) hnot
  rw [GlobalTheory.DualPairCheck.cA_cA] at hlH
  refine ⟨s • l, ?_, fun z hz => ?_, ?_⟩
  · rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hlH]
  · obtain ⟨hz1, hz2⟩ := hz
    have h1 := (hsd _ (GlobalTheory.SplitScalar.half_fin hse (hhalf z hz1))).1 (hmem z hz1 hz2) l hlΛ
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1
  · have h1 := GlobalTheory.SplitScalar.psi_skew_ne hne
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1

end GlobalTheory.DownLift.GenSplit

end
