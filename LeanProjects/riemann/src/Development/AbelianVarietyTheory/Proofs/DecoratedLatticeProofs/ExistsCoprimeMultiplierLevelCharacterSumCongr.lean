import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NPartConj

variable (I : Formalism.MainNotions.S.AutInst)

theorem nsmul_mL' {g k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem nsmul_Lf' {k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ I.Lf) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem mL_le_Lf' (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact nsmul_Lf' I hy)

theorem K_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : I.fmat x *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  have h : Formalism.L2.SG.HidaSetting.mL I g ≤
      (Formalism.L2.SG.HidaSetting.mL I g).comap (Formalism.L2.SG.Pf.unitaryCongruence.mvO I (I.fmat x)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      show I.fmat x *ᵥ ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y) ∈ Formalism.L2.SG.HidaSetting.mL I g
      rw [Matrix.mulVec_smul]
      exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hy))
  exact h hv

theorem K_sub_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : (I.fmat x - 1) *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (K_mL' I hx hv) hv

theorem hcn_of {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {n N N0 : Formalism.L2.SG.HidaSetting.VA I}
    (hN : I.fmat x *ᵥ N0 = N) {c : ℕ}
    (h : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0) ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g := by
  have e : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N =
      I.fmat x *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hN, smul_sub]
  rw [e]; exact K_mL' I hx h

theorem conj_sub (x m : I.Gf) (n : Formalism.L2.SG.HidaSetting.VA I) :
    (I.fmat (x⁻¹ * m * x) - 1) *ᵥ n = I.fmat x⁻¹ *ᵥ ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul, Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem term_cong {g : ℕ} {x m : I.Gf} (hx : x ∈ I.Kset) (hm : m ∈ I.Kset)
    {f F n N : Formalism.L2.SG.HidaSetting.VA I} (hf : f ∈ I.Lf) (hn : n ∈ I.Lf) (hFx : I.fmat x *ᵥ F = F) {c : ℕ}
    (hcf : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (f - F) ∈ Formalism.L2.SG.HidaSetting.mL I g)
    (hcn : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g) :
    Formalism.L2.SG.HidaSetting.ZMod' I g (((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N))) := by
  set C : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) with hC
  have e1 : Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) =
      Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ f) ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
    rw [conj_sub, PIW.NormChiNBi.hA_left_inv, inv_inv]
  have hsig : Formalism.L2.SG.HidaSetting.sigA I C = C := by rw [hC, map_natCast]
  have esc : ∀ u v : Formalism.L2.SG.HidaSetting.VA I, Formalism.L2.SG.HidaSetting.hA I (C • u) ((I.fmat m - 1) *ᵥ (C • v)) =
      C * C * Formalism.L2.SG.HidaSetting.hA I u ((I.fmat m - 1) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_smul, PIW.NormChiNBi.hA_smul_left, PIW.NormChiNBi.hA_smul_right, hsig]; ring
  have hδf : C • (I.fmat x *ᵥ f) - C • F ∈ Formalism.L2.SG.HidaSetting.mL I g := by
    have e : C • (I.fmat x *ᵥ f) - C • F = I.fmat x *ᵥ (C • (f - F)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hFx, smul_sub]
    rw [e]; exact K_mL' I hx hcf
  have hA'L : C • F ∈ I.Lf := by
    have e : C • F = C • f - C • (f - F) := by rw [smul_sub]; abel
    rw [e]; exact sub_mem (nsmul_Lf' I hf) (mL_le_Lf' I g hcf)
  have hBL : (I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n)) ∈ I.Lf :=
    Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv I hm (nsmul_Lf' I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hn))
  have key : ((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N)) =
      Formalism.L2.SG.HidaSetting.hA I (C • (I.fmat x *ᵥ f) - C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n))) +
      Formalism.L2.SG.HidaSetting.hA I (C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n) - C • N)) := by
    rw [PIW.NormChiNBi.hA_sub_left, Matrix.mulVec_sub, PIW.NormChiNBi.hA_sub_right, e1, esc, esc, esc, Nat.cast_mul]
    ring
  rw [key]
  obtain ⟨s, hs, hs'⟩ := PIW.NormChiNBi.hA_mL_left I g hδf hBL
  obtain ⟨t, ht, ht'⟩ := PIW.NormChiNBi.hA_mL_right I g (K_sub_mL' I hm hcn) hA'L
  exact ⟨s + t, add_mem hs ht, by rw [hs', ht', mul_add]⟩

end GlobalTheory.NPartConj

namespace GlobalTheory.NPartConj

theorem term_each (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf)
    (hm : m ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  obtain ⟨c1, hc1, h1⟩ := (X.basisApprox a).2
  have hFx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hx := X.xu_K u
  obtain ⟨c2, hc2, N0, hN0, h2⟩ : ∃ c2 : ℕ, Nat.Coprime c2 X.B.g ∧ ∃ N0 : VA X.B.I,
      X.B.I.fmat (X.xu u) *ᵥ N0 = incl X.B.I (nxt X.eR (X.zR u) a) ∧
      ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0)) ∈ mL X.B.I X.B.g := by
    unfold nxt
    split_ifs with h
    · obtain ⟨c2, hc2, h2⟩ := (X.basisApprox ⟨a.1 + 1, h⟩).1
      exact ⟨c2, hc2, _, (X.xu_fix u _).1, h2⟩
    · obtain ⟨c2, hc2, h2⟩ := X.xu_z u
      refine ⟨c2, hc2, X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u), ?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, PIW.NormChiNBi.fmat_mul_inv', Matrix.one_mulVec]
      · have h3 := neg_mem h2
        rwa [← smul_neg, neg_sub] at h3
  have hcop : Nat.Coprime (c1 * c2) X.B.g := Nat.Coprime.mul hc1 hc2
  refine ⟨(c1 * c2) * (c1 * c2), Nat.Coprime.mul hcop hcop, ?_⟩
  have hcf : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact nsmul_mL' X.B.I h1
  have hcN : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_smul]; exact nsmul_mL' X.B.I h2
  exact term_cong X.B.I hx hm (X.vectorsInLattice.1 a).2 (PIW.NormChiNBi.nxt_mem X a) hFx hcf
    (hcn_of X.B.I hx hN0 hcN)

theorem nsum_cong : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  intro D X u m hm
  choose c hc h using term_each D X u m hm
  refine ⟨∏ a, c a, Nat.Coprime.prod_left fun a _ => hc a, ?_⟩
  rw [Finset.mul_sum]
  refine Formalism.L2.SG.Pf.unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ a)
  rw [hk]
  have e : ∀ T : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      ((c a * k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T =
        (k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T) := by
    intro T; push_cast; ring
  rw [e]
  exact Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ k) (h a)

end GlobalTheory.NPartConj
