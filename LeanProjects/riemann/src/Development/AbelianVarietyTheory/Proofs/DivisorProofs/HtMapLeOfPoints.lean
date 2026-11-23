import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA

open Module NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.DescentFamily

open Formalism.HN

theorem numeric {a N mu muA ht mm P Λ ε t : ℝ} (ha : 0 < a) (haN : a ≤ N) (hN : N ≤ (1 + ε) * a)
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hht : ht ≤ 2 * P) (hmm : -(2 * Λ) ≤ mm) (ht' : t ≤ muA - 2 * P)
    (h : a * (muA - ht) + (N - a) * mm ≤ N * mu) : t - ε * (|t| + 2 * Λ) ≤ mu := by
  have hN0 : 0 < N := ha.trans_le haN
  have h1 : a * t ≤ a * (muA - ht) := mul_le_mul_of_nonneg_left (by linarith) ha.le
  have h2 : (N - a) * (-(2 * Λ)) ≤ (N - a) * mm := mul_le_mul_of_nonneg_left hmm (by linarith)
  have h3 : (N - a) * t ≤ (N - a) * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (by linarith)
  have h4 : N - a ≤ ε * N := by nlinarith
  have h5 : (N - a) * (|t| + 2 * Λ) ≤ ε * N * (|t| + 2 * Λ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  refine le_of_mul_le_mul_left ?_ hN0
  nlinarith

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem htMap_le_of_points (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (P : ℝ)
    (h : ∀ v f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ Real.exp P * Formalism.HermitianLatticesTheory.normAt b X v f) :
    htMap b X b' X' φ ≤ 2 * P := by
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have h1 : ∀ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * P := by
    intro v
    rw [Real.log_pow]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.log_le_iff_le_exp (PlaceOperatorNorms.opNormAt_pos b X b' X' hX hX' v φ hφ)]
    exact Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX φ v _ (Real.exp_pos _).le (h v)
  unfold htMap
  have h2 : ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ (nPl K : ℝ) * (2 * P) := by
    calc _ ≤ ∑ _v : InfinitePlace K, 2 * P := Finset.sum_le_sum fun v _ => h1 v
      _ = (nPl K : ℝ) * (2 * P) := by simp [nPl]
  calc 1 / (nPl K : ℝ) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
      ≤ 1 / (nPl K : ℝ) * ((nPl K : ℝ) * (2 * P)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * P := by field_simp

theorem normAt_pi_sq [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K)
    (x : Fin n → V) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x ^ 2 =
        ∑ j, Formalism.HermitianLatticesTheory.normAt b X v (x j) ^ 2 := by
  simp only [← Formalism.ExtensionFiltration.majAt_self_re]
  rw [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi b X hX, Complex.re_sum]

end

theorem descent : ∀ (K V W : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (NA : (K →+* ℂ) → V → ℝ) (NB : (K →+* ℂ) → W → ℝ) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (n : ℕ) (φ : Fin n → V →ₗ[K] W) (P Λ ε t : ℝ), HasGram NA → HasGram NB → A.FG → B.FG → A ≠ ⊥ → (∀ h, ∀ f ∈ A, φ h f ∈ B) → (∀ f, (∀ h, φ h f = 0) → f = 0) → (∀ σ f, ∑ h, NB σ (φ h f) ^ 2 ≤ Real.exp (2 * P) * NA σ f ^ 2) → (∃ s : Set W, s ⊆ (B : Set W) ∧ (∀ y ∈ s, ∀ σ, NB σ y ≤ Real.exp Λ) ∧ (B : Set W) ⊆ (Submodule.span K s : Set W)) → 0 ≤ Λ → 0 ≤ ε → (n : ℝ) * Formalism.HN.rkK B ≤ (1 + ε) * Formalism.HN.rkK A → t ≤ slope_sq NA A - 2 * P → t - ε * (|t| + 2 * Λ) ≤ slope_sq NB B := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ NA NB A B n φ P Λ ε t hA hB hAfg hBfg hA0 hint hinj hnorm hs hΛ hε hrk ht
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨p, ⟨b, X⟩, hGA⟩⟩ := hA
  obtain ⟨⟨q, ⟨b', X'⟩, hGB⟩⟩ := hB
  change IsGram b X NA at hGA
  change IsGram b' X' NB at hGB
  have hX : ∀ v, IsUnit (X v).det := fun v => (hGA v).1
  have hX' : ∀ v, IsUnit (X' v).det := fun v => (hGB v).1
  rw [slope_sq_eq hGA hAfg] at ht
  rw [slope_sq_eq hGB hBfg]
  obtain ⟨f0, hf0A, hf0⟩ := (Submodule.ne_bot_iff A).1 hA0
  obtain ⟨h0, hh0⟩ : ∃ h, φ h f0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf0 (hinj f0 hc)
  have hn : 0 < n := h0.pos
  have hB0 : B ≠ ⊥ := (Submodule.ne_bot_iff B).2 ⟨_, hint h0 f0 hf0A, hh0⟩
  obtain ⟨p1, p2, -⟩ := Formalism.BranchingDeterminantCap.power_slope_mu K W _ b' X' hX' B n hBfg hB0 hn
  set bn : Basis (Σ _ : Fin n, Fin q) K (Fin n → W) := Pi.basis fun _ : Fin n => b' with hbn
  set Xn : InfinitePlace K → Matrix (Σ _ : Fin n, Fin q) (Σ _ : Fin n, Fin q) ℂ :=
    fun v => Matrix.blockDiagonal' fun _ : Fin n => X' v with hXndef
  set Bn : Submodule (𝓞 K) (Fin n → W) := Submodule.pi Set.univ fun _ : Fin n => B with hBn
  have hXn : ∀ v, IsUnit (Xn v).det := fun v => Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det (X' v) (hX' v)
  have hBnfg : Bn.FG := Submodule.fg_pi fun _ => hBfg
  let Φ : V →ₗ[K] (Fin n → W) := LinearMap.pi φ
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    exact fun f hf => hinj f fun h => congrFun hf h
  have hΦle : A.map (Φ.restrictScalars (𝓞 K)) ≤ Bn := by
    rintro _ ⟨f, hf, rfl⟩ h -
    exact hint h f hf
  have hΦ0 : Φ ≠ 0 := fun h => hh0 (congrFun (LinearMap.congr_fun h f0) h0)
  have hBn0 : Bn ≠ ⊥ := (Submodule.ne_bot_iff Bn).2
    ⟨Φ f0, hΦle ⟨f0, hf0A, rfl⟩, fun h => hh0 (congrFun h h0)⟩
  have hht : htMap b X bn Xn Φ ≤ 2 * P := by
    refine htMap_le_of_points b X bn Xn hX hXn Φ hΦ0 P fun v f => ?_
    have n0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v f := Real.sqrt_nonneg _
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [hbn, hXndef, normAt_pi_sq b' X' hX', mul_pow, ← Real.exp_nat_mul, (hGA v).2]
    simp only [(hGB v).2]
    exact_mod_cast hnorm v.embedding f
  have hmm : -(2 * Λ) ≤ muMinDef bn Xn Bn := by
    obtain ⟨s, hsB, hsn, hsp⟩ := hs
    refine Formalism.ExtensionFiltration.spanMuMin K _ _ bn Xn hXn Bn Λ hBnfg hBn0
      ⟨⋃ i : Fin n, (fun y => (Pi.single i y : Fin n → W)) '' s, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hsB hy
      · simp [Pi.single_eq_of_ne hj]
    · intro x hx v
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      rw [hbn, hXndef, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.normAt_single b' X' hX', (hGB v).2]
      exact hsn y hy _
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : x i ∈ Submodule.span K s := hsp (hx i trivial)
      have h2 := Submodule.mem_map_of_mem (f := LinearMap.single K (fun _ : Fin n => W) i) h1
      rw [Submodule.map_span] at h2
      exact Submodule.span_mono (Set.subset_iUnion
        (fun i : Fin n => (fun y => (Pi.single i y : Fin n → W)) '' s) i) h2
  have hd := Formalism.ExtensionFiltration.descentSlope K V _ (Fin n → W) _ b X bn Xn hX hXn Φ A Bn hAfg hBnfg hA0 hΦinj hΦle
  rw [p2] at hd
  have hle : rkK A ≤ rkK Bn := by
    haveI : Module.Finite K (Fin n → W) := Module.Finite.of_basis bn
    rw [← Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_map Φ hΦinj A]
    exact Submodule.finrank_mono (Submodule.span_mono hΦle)
  have hpos : 0 < rkK A := Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0)
  refine numeric (a := rkK A) (N := rkK Bn) (by exact_mod_cast hpos) (by exact_mod_cast hle) ?_ hΛ hε hht hmm ht hd
  rw [p1]
  push_cast
  exact hrk

end GlobalTheory.DescentFamily
