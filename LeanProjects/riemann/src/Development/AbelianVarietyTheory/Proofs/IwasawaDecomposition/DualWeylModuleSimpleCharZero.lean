import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodules
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeyl
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModuleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightModStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineFieldStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDominantHighestVectorOfLtStableStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanMapOfEvalMemOfNeZeroStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcZero

theorem eq_of_hcVal_eq_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν μ : Fin N → ℕ)
    (hν : Antitone ν) (hμ : Antitone μ) (hc : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩)
    (hv : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) : μ = ν := by
  have hZ : ∀ j, hcVal ℤ (fun i => (μ i : ℤ)) j = hcVal ℤ (fun i => (ν i : ℤ)) j := by
    intro j
    apply Int.cast_injective (α := k)
    have h1 := hcVal_map (Int.castRingHom k) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom k) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [← h1, ← h2]
    exact hv j
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (∑ i, ν i + N)
  haveI := Fact.mk hp
  apply eq_of_hcVal_eq p hp (ZMod p) N ν μ hν hμ
  · intro h
    refine ⟨(hc h).1, (hc h).2, ?_⟩
    have : ν ⟨0, h⟩ ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
    omega
  · intro j
    have h1 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [h1, h2, hZ j]

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.map φ (rowAct R (n := N) g f) = rowAct S (n := N) (g.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum, Matrix.map_apply]

theorem map_mem_span_map {S A : Type} [CommRing S] [CommRing A] (ψ : S →+* A) {σ : Type}
    (X : Set (MvPolynomial σ S)) (P : MvPolynomial σ S) (hP : P ∈ Submodule.span S X) :
    MvPolynomial.map ψ P ∈ Submodule.span A (MvPolynomial.map ψ '' X) := by
  induction hP using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem isGLSubmodule_of_stable (k : Type) [Field k] [Infinite k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k))
    (hG : ∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) : GlobalTheory.Published.IsGLSubmodule k N lam M := by
  intro A _ _ g f hf
  let S := MvPolynomial (Fin N × Fin N) k
  let Y : Matrix (Fin N) (Fin N) S := Matrix.mvPolynomialX (Fin N) (Fin N) k
  let P : MvPolynomial (Fin N × Fin N) S :=
    rowAct S (n := N) Y.transpose (MvPolynomial.map (algebraMap k S) f)
  have hP : P ∈ Submodule.span S (MvPolynomial.map (algebraMap k S) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    refine GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero k _ _ M Y.det (Matrix.det_mvPolynomialX_ne_zero _ _) P ?_
    intro y hy
    let m0 : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => y (i, j)
    have hm0 : Y.map (MvPolynomial.eval y) = m0 := by
      ext i j; simp [Y, m0, Matrix.mvPolynomialX]
    have hdet : m0.det ≠ 0 := by
      rw [← hm0]; rw [RingHom.map_det] at hy; exact hy
    let g0 : GL (Fin N) k := Matrix.nonsingInvUnit m0 (isUnit_iff_ne_zero.mpr hdet)
    have h1 := hG g0 f hf
    have hu : detPow k N g0 lam.detShift ≠ 0 := Units.ne_zero _
    rw [sqAct, Submodule.smul_mem_iff M hu] at h1
    have e1 : MvPolynomial.map (MvPolynomial.eval y) P = rowAct k (n := N) (m0.transpose) f := by
      simp only [P]
      rw [map_rowAct_eq, MvPolynomial.map_map]
      have : (MvPolynomial.eval y).comp (algebraMap k S) = RingHom.id k := by
        ext a; simp [S]
      rw [this, MvPolynomial.map_id, Matrix.transpose_map, hm0]
    rw [e1]
    exact h1
  let ψ : S →+* A := MvPolynomial.eval₂Hom (algebraMap k A) fun v => (g : Matrix (Fin N) (Fin N) A) v.1 v.2
  have e2 : MvPolynomial.map ψ P =
      rowAct A (n := N) (g : Matrix (Fin N) (Fin N) A).transpose (MvPolynomial.map (algebraMap k A) f) := by
    simp only [P]
    rw [map_rowAct_eq, MvPolynomial.map_map]
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    have h4 : (Y.transpose).map ψ = (g : Matrix (Fin N) (Fin N) A).transpose := by
      ext i j
      simp only [Y, ψ, Matrix.mvPolynomialX, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom]
      exact MvPolynomial.eval₂_X _ _ _
    rw [h3, h4]
  have h5 := map_mem_span_map ψ _ P hP
  rw [Set.image_image] at h5
  have h6 : (fun x : MvPolynomial (Fin N × Fin N) k => MvPolynomial.map ψ (MvPolynomial.map (algebraMap k S) x)) =
      ⇑(MvPolynomial.map (σ := Fin N × Fin N) (algebraMap k A)) := by
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    funext x
    rw [MvPolynomial.map_map, h3]
  rw [h6, e2] at h5
  rw [sqAct]
  exact Submodule.smul_mem _ _ h5

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem hw_mem_of_lt_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν)
    (hlast : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : Good M) (hM' : Good M') (hlt : M < M')
    (hle : M' ≤ dualWeyl k N N ν) : hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by
    rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ := by
    intro h
    refine ⟨hlast h, ?_⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := eq_of_hcVal_eq_charZero k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

theorem nablaSq_simple_charZero : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)),
    M ≤ nablaSq k N lam → (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) →
      M = ⊥ ∨ M = nablaSq k N lam := by
  intro k _ _ N lam M hM hG
  haveI : Infinite k := Infinite.of_injective _ Nat.cast_injective
  have hN := factNatW N lam
  by_contra hc
  push_neg at hc
  have hMg : Good M := good_of_isGLSubmodule k N lam M (isGLSubmodule_of_stable k N lam M hG)
  have key := hw_mem_of_lt_charZero k N lam.natW hN.1 hN.2.2
  have h1 := (key ⊥ M (good_top_bot k N N).2 hMg (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) hMg (good_nablaSq k N lam) (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.AlcZero
