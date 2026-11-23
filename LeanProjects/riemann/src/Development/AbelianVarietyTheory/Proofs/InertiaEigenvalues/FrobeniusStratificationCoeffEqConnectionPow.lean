import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorStrat

def idl (K : Type) [Field K] : Ideal K⟦X⟧⟦X⟧ := Ideal.span {C (X : K⟦X⟧), X}

theorem idl_ne_top (K : Type) [Field K] : idl K ≠ ⊤ := by
  intro h
  have hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧)) := by
    rw [idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp
  have h1 := hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)
  simp at h1

theorem eq_zero_of_forall_mem {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : ∀ m, g ∈ idl K ^ m) : g = 0 := by
  have := Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact h

theorem mem_idl_of_constantCoeff {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : constantCoeff g = 0) :
    g ∈ idl K := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.2 h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))

theorem taylor_eq_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (f : K⟦X⟧) (hf : PowerSeries.derivative K f = 0) : sh f = C f := by
  ext1 i
  rcases i with _ | i
  · simpa using hsh f 0
  · have h := hsh f (i + 1)
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 1).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [coeff_C, if_neg (by omega)]
    exact (mul_eq_zero.1 h).resolve_left hne

theorem taylor_X {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) :
    sh X = C X + X := by
  ext1 i
  rcases i with _ | _ | i
  · simpa using hsh X 0
  · simpa using hsh X 1
  · have h := hsh X (i + 2)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero,
      Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 2).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [map_add, coeff_C, coeff_X, if_neg (by omega), if_neg (by omega), add_zero]
    exact (mul_eq_zero.1 h).resolve_left hne

end GlobalTheory.TaylorStrat

namespace GlobalTheory.TaylorStrat

theorem map_idl_pow_le {K : Type} [Field K] (l : ℕ) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hshX : sh X = C X + X) (hC : φ₂ (C X) = C X ^ l) (hsh : φ₂ (sh X) = sh X ^ l)
    (m : ℕ) {g : K⟦X⟧⟦X⟧} (hg : g ∈ idl K ^ m) : φ₂ g ∈ idl K ^ (l * m) := by
  have hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have h1 : (idl K).map φ₂ ≤ idl K ^ l := by
    rw [Ideal.map_le_iff_le_comap, idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]
    · rw [hC]
      exact Ideal.pow_mem_pow hCm l
    · have hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l :=
        (congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans
          (by rw [map_sub, hsh, hC, hshX])
      rw [hφX]
      exact sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)
  have h2 := Ideal.mem_map_of_mem φ₂ hg
  rw [Ideal.map_pow] at h2
  rw [pow_mul]
  exact Ideal.pow_right_mono h1 m h2

theorem mul_mul_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] (J : Ideal R) (A N B : Matrix ι ι R)
    (hN : ∀ i j, N i j ∈ J) (i j : ι) : (A * N * B) i j ∈ J := by
  rw [Matrix.mul_apply]
  refine J.sum_mem fun k _ => J.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)

end GlobalTheory.TaylorStrat

open GlobalTheory.TaylorStrat in

theorem GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hshX := taylor_X sh hsh
  have hshC : ∀ c : K, sh (C c) = C (C c) := fun c => taylor_eq_C sh hsh _ (by simp)
  have hcc : ∀ f, constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hCX : φ₂ (C X) = C X ^ l := by rw [hφC, frob_X, map_pow]
  have hshl : φ₂ (sh X) = sh X ^ l := by rw [hφsh, frob_X, map_pow]
  have hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)
  let W : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => (P.xiMat τ)⁻¹ * P.mx τ
  let Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ
  let ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => (Y τ).map C * (W τ).map sh
  have hYW : ∀ τ, Y τ * W τ = 1 := by
    intro τ
    simp only [Y, W]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]
  have h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1 := by
    intro τ
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hYW τ) i) j
    simpa [ε₀, Matrix.mul_apply, hcc] using this
  have hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh =
      ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂ := by
    intro τ
    have F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφC]
    have F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφsh]
    have F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) =
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) := by
      intro M; ext1 p q; simp [hshC]
    have hM := P.mx_mul_xiMat τ
    rw [← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply] at hM
    have hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1 := by
      rw [← map_mul, hXi, map_one]
    have hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
      calc W τ = (P.xiMat τ)⁻¹ * (P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1))) *
            (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]
        _ = _ := by
          rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]
    have hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) *
        (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
      have h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) *
          (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
        rw [hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]
      show P.mxInv τ * P.xiMat τ = _
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]
    simp only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]
    rw [hW, hY]
    simp only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]
    rw [F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul,
      ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul,
      ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]
    have hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) *
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1 := by
      rw [← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]
    rw [hc, Matrix.one_mul]
  have hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1 := by
    intro τ
    rw [← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ *
      ((P.mxInv (τ - 1)).map (frob K l)).map sh := by
    intro τ
    have h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh =
        ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ := by
      rw [Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]
    calc ε τ - ε₀ τ = (ε τ - ε₀ τ) * (((P.mx (τ - 1)).map (frob K l)).map sh *
          ((P.mxInv (τ - 1)).map (frob K l)).map sh) := by rw [hinv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1]
  have hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro τ i j
      rw [zero_add, pow_one]
      apply mem_idl_of_constantCoeff
      have h1 := congrFun (congrFun (hε0 τ) i) j
      have h2 := congrFun (congrFun (h00 τ) i) j
      simp only [Matrix.map_apply] at h1 h2
      rw [Matrix.sub_apply, map_sub, h1, h2, sub_self]
    | succ m ih =>
      intro τ i j
      rw [hδ τ]
      apply mul_mul_mem
      intro p q
      rw [Matrix.map_apply]
      exact Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))
  have key : ε τ = ε₀ τ := by
    refine Matrix.ext fun i j => ?_
    exact sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))
  have hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1) := by
    ext1 τ
    rw [P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
    congr 1
    ext1 k
    simp [bas, Pi.single_apply]
  have hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) =
      P.xiExt (fun τ i => (PowerSeries.derivative K)^[n] (w τ i)) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, P.nabla_xiExt, ih]
      rfl
  rw [hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]
  show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) =
    (Y τ *ᵥ fun k => (PowerSeries.derivative K)^[n] ((W τ *ᵥ Pi.single j 1) k)) i
  rw [Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]
  rfl
