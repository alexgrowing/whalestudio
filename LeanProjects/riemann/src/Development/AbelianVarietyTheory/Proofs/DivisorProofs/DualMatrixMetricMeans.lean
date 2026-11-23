import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.InfinitePlaceDepthSums
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.FreeLiftMetric

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

section Mat
open scoped Matrix.Norms.L2Operator

theorem opNorm_eq_of_gram {n p q : Type} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]
    [DecidableEq q] (B : Matrix n p ℂ) (B' : Matrix n q ℂ) (h : B * Bᴴ = B' * B'ᴴ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B')‖ := by
  change ‖B‖ = ‖B'‖
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self B'ᴴ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h1 h2
  rw [h, h2] at h1
  exact ((mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 h1).symm

end Mat

theorem frame_gram {n : Type} [Fintype n] [DecidableEq n] (X G : Matrix n n ℂ) (hX : IsUnit X.det)
    (h : (X⁻¹)ᴴ * X⁻¹ = G) : X * Xᴴ = G⁻¹ := by
  rw [← h, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hX, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hX]

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def SameMetric {a : ℕ} (X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) : Prop :=
  ∀ v, (X' v)⁻¹ = (dualFrame XM v)⁻¹

def dualMat {n a : ℕ} (vm : (Fin n → K) →ₗ[K] Module.Dual K (Fin a → K)) : Matrix (Fin a) (Fin n) K :=
  LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin a)).dualBasis vm

theorem ker_dualMat {n a : ℕ} (vm : (Fin n → K) →ₗ[K] Module.Dual K (Fin a → K)) :
    LinearMap.ker (dualMat vm).mulVecLin = LinearMap.ker vm := by
  ext x
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin a)).dualBasis vm x
  have hx : ⇑((Pi.basisFun K (Fin n)).repr x) = x := by funext i; simp
  rw [hx] at h
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, dualMat, h]
  constructor
  · intro h0
    have : (Pi.basisFun K (Fin a)).dualBasis.repr (vm x) = 0 := by
      ext i; exact congrFun h0 i
    exact (LinearEquiv.map_eq_zero_iff _).1 this
  · intro h0; rw [h0]; simp

theorem opNormAt_quot (hW : Df.WF) {a : ℕ} {X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ} (hX : SameMetric X' XM)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (vb : Matrix (Fin a) (Fin (Df.dQ Bs.μ0)) K) (hvb : vb * Df.Pq Bs.μ0 = dualMat vm) (v : InfinitePlace K) :
    opNormAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin a)) X' v (Matrix.mulVecLin vb) =
      opNormAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (formFrame (Df.HV Bs.μ0))
        (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v vm := by
  unfold opNormAt
  have e1 : LinearMap.toMatrix (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Pi.basisFun K (Fin a)) (Matrix.mulVecLin vb) = vb := by
    ext i j; simp [LinearMap.toMatrix_apply]
  have e2 : LinearMap.toMatrix (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (Pi.basisFun K (Fin a)).dualBasis vm =
      vb * Df.Pq Bs.μ0 := hvb.symm
  rw [e1, e2, ← hX v, Matrix.map_mul]
  obtain ⟨hQ, hQG⟩ := hW.XQ_quot Bs.μ0 v
  obtain ⟨hV, hVG⟩ := formFrame_spec (Df.HV Bs.μ0) v (hW.HV_pos Bs.μ0 v)
  have gQ := frame_gram _ _ hQ hQG
  have gV := frame_gram _ _ hV hVG
  set G := (Df.Pq Bs.μ0).map v.embedding * ((Df.HV Bs.μ0).map v.embedding)⁻¹ * ((Df.Pq Bs.μ0).map v.embedding)ᴴ
    with hG
  have hGu : IsUnit G.det := by
    have h1 : IsUnit G⁻¹ := by
      rw [← hQG]
      have := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)
      exact ((Matrix.isUnit_conjTranspose _).2 this).mul this
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_nonsing_inv_iff.1 h1)
  rw [Matrix.nonsing_inv_nonsing_inv _ hGu] at gQ
  apply opNorm_eq_of_gram
  set A := (X' v)⁻¹ * vb.map v.embedding
  set P := (Df.Pq Bs.μ0).map v.embedding
  set XV := formFrame (Df.HV Bs.μ0) v
  set XQ := Df.XQ Bs.μ0 v
  have e3 : (X' v)⁻¹ * (vb.map v.embedding * P) * XV = A * (P * XV) := by simp only [A, Matrix.mul_assoc]
  rw [e3]
  calc A * XQ * (A * XQ)ᴴ = A * (XQ * XQᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = A * (P * (XV * XVᴴ) * Pᴴ) * Aᴴ := by rw [gQ, gV]
    _ = A * (P * XV) * (A * (P * XV))ᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem meanInf_eq [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_mono {g g' : InfinitePlace K → ℝ} (h : ∀ v, g v ≤ g' v) : meanInf K g ≤ meanInf K g' :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => h v) (by positivity)

theorem meanInf_const [IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp

theorem htMap_quot [IsTotallyComplex K] (hW : Df.WF) {a : ℕ} {X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ}
    (hX : SameMetric X' XM) (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (vb : Matrix (Fin a) (Fin (Df.dQ Bs.μ0)) K) (hvb : vb * Df.Pq Bs.μ0 = dualMat vm) :
    htMap (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin a)) X' (Matrix.mulVecLin vb) =
      meanInf K (logNormV_sq Df XM vm) := by
  rw [meanInf_eq]
  unfold htMap logNormV_sq
  simp only [opNormAt_quot hW hX vm vb hvb]

theorem exists_induced_iff (hW : Df.WF) {a : ℕ} (M : Matrix (Fin a) (Fin (Df.nV Bs.μ0)) K) :
    (∃ vb : Matrix (Fin a) (Fin (Df.dQ Bs.μ0)) K, vb * Df.Pq Bs.μ0 = M) ↔
      Df.U Bs.μ0 ≤ LinearMap.ker M.mulVecLin := by
  constructor
  · rintro ⟨vb, rfl⟩ x hx
    have hx' : (Df.Pq Bs.μ0).mulVec x = 0 := hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [← Matrix.mulVec_mulVec, hx', Matrix.mulVec_zero]
  · intro h
    obtain ⟨σ, hσ⟩ := (Df.Pq Bs.μ0).mulVecLin.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (hW.Pq_surj Bs.μ0))
    refine ⟨M * LinearMap.toMatrix' σ, ?_⟩
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have hσx : (Df.Pq Bs.μ0).mulVec (σ ((Df.Pq Bs.μ0).mulVec x)) = (Df.Pq Bs.μ0).mulVec x :=
      LinearMap.congr_fun hσ _
    have hm : σ ((Df.Pq Bs.μ0).mulVec x) - x ∈ Df.U Bs.μ0 := by
      change (Df.Pq Bs.μ0).mulVec _ = 0
      rw [Matrix.mulVec_sub, hσx, sub_self]
    have h2 : M.mulVec (σ ((Df.Pq Bs.μ0).mulVec x) - x) = 0 := h hm
    rw [Matrix.mulVec_sub, sub_eq_zero] at h2
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, h2]

theorem exists_lower_iff (hW : Df.WF) (S : IndefRows Df) (c : ℝ) :
    (∃ g : InfinitePlace K → ℝ, (∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) ∧
      c ≤ meanInf K g) ↔ c ≤ meanInf K (lamMin hW S) := by
  classical
  constructor
  · rintro ⟨g, hg, hc⟩
    exact hc.trans (meanInf_mono fun v => le_lamMin hW S v _ (hg v))
  · intro h
    refine ⟨lamMin hW S, fun v p hp => ?_, h⟩
    exact Finset.inf'_le (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) (by simpa [occurring] using hp)

def LinTie (O : FunData K Df) (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K)) : Prop :=
  SameMetric O.X' XM ∧ O.vmu Bs.μ0 = dualMat vm

theorem testMap_iff (O : FunData K Df) {XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ}
    {vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K)} (h : LinTie O XM vm) :
    TestMap Df XM vm ↔ (∀ v, IsUnit (O.X' v).det) ∧ LeafKer O := by
  unfold TestMap LeafKer
  rw [h.2, ker_dualMat]
  refine and_congr_left fun _ => forall_congr' fun v => ?_
  have h1 := h.1 v
  rw [← Matrix.isUnit_iff_isUnit_det (O.X' v), ← Matrix.isUnit_nonsing_inv_iff, h1, Matrix.isUnit_nonsing_inv_iff,
    dualFrame, Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]

theorem infinitePlaceBound_iff [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df)
    {XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ}
    {vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K)} (h : LinTie O XM vm) (C b : ℝ) :
    LeafIP S.toIndefData O C b ↔
      (Df.U Bs.μ0 ≤ LinearMap.ker vm → MeanNormBound Df XM vm C O.f O.m O.N b (Real.log b) (O.Sig0 C b)) ∧
        -(3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * Real.log b) ≤ meanInf K (lamMin hW S) := by
  unfold LeafIP
  refine and_congr ?_ (exists_lower_iff hW S _)
  rw [h.2, ← ker_dualMat, ← exists_induced_iff hW]
  unfold MeanNormBound FunData.bIPa
  constructor
  · rintro H ⟨vb, hvb⟩
    rw [← htMap_quot hW h.1 vm vb hvb]
    exact H vb hvb
  · intro H vb hvb
    rw [htMap_quot hW h.1 vm vb hvb]
    exact H ⟨vb, hvb⟩

theorem scalarLowerBound_iff [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (C f m N L La : ℝ) :
    ScalarLowerBound hW S C f m N L La ↔
      C * f * m * N ^ 2 * La ≤ 3 * C * f * m * N ^ 2 * L ∧ ∀ v, -(C * f * m * N ^ 2 * La) ≤ lamMin hW S v := by
  unfold ScalarLowerBound
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨by linarith, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨?_, by linarith, h3⟩
    have := meanInf_mono (K := K) h3
    rwa [meanInf_const] at this

def NumTie (O : FunData K Df) (E : Type) [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (C b : ℝ) : Prop :=
  O.f = numF E ∧ O.m = Fintype.card Bs.J ∧
    ∃ φ : O.Sq → HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      Set.BijOn φ O.S0 S0 ∧ ∀ q ∈ O.S0, O.qq q = Ideal.absNorm (φ q).asIdeal ∧ e (φ q) = O.ee C b q

theorem NumTie.sig {O : FunData K Df} {E : Type} [Field E] [NumberField E]
    {S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))}
    {e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ} {C b : ℝ} (h : NumTie O E S0 e C b) :
    depthSum S0 e = O.Sig0 C b := by
  obtain ⟨-, -, φ, hφ, hq⟩ := h
  unfold depthSum FunData.Sig0
  symm
  refine Finset.sum_nbij φ (fun q hq' => hφ.mapsTo hq') hφ.injOn hφ.surjOn fun q hq' => ?_
  rw [(hq q hq').1, (hq q hq').2]

theorem log_numB (x ε : ℝ) : Real.log (numB x ε) = numL x ε := Real.log_exp _

theorem meanBounds_iff [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df)
    (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (C x ε : ℝ)
    (hl : LinTie O XM vm) (hn : NumTie O E S0 e C (numB x ε)) :
    MeanBounds C hW S XM vm E S0 e O.k O.tt x ε ↔
      (1 ≤ x → (∀ v, IsUnit (O.X' v).det) ∧ LeafKer O →
        LeafIP S.toIndefData O C (numB x ε) ∧
          C * O.f * O.m * (O.N : ℝ) ^ 2 * numLa E x ε ≤ 3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * numL x ε ∧
          ∀ v, -(C * O.f * O.m * (O.N : ℝ) ^ 2 * numLa E x ε) ≤ lamMin hW S v) := by
  unfold MeanBounds
  rw [← testMap_iff O hl, infinitePlaceBound_iff hW S O hl, log_numB, hn.sig, ← hn.1, ← hn.2.1]
  change (1 ≤ x → TestMap Df XM vm → MeanNormBound Df XM vm C O.f O.m O.N _ _ _ ∧
    ScalarLowerBound hW S C O.f O.m O.N _ _) ↔ _
  refine forall_congr' fun _ => forall_congr' fun hT => ?_
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨⟨fun _ => ha, hb.2.1.trans hb.1⟩, (scalarLowerBound_iff hW S _ _ _ _ _ _).1 hb⟩
  · rintro ⟨⟨ha, -⟩, hb⟩
    exact ⟨ha hT.2.ge, (scalarLowerBound_iff hW S _ _ _ _ _ _).2 hb⟩

theorem infinitePlaceBound_of_meanBounds [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df)
    (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (C₀ C x ε : ℝ) (hC : C₀ ≤ C)
    (hl : LinTie O XM vm) (hn : NumTie O E S0 e C (numB x ε)) (hx : 1 ≤ x)
    (hX : ∀ v, IsUnit (O.X' v).det) (hk : LeafKer O)
    (h : MeanBounds C₀ hW S XM vm E S0 e O.k O.tt x ε) : LeafIP S.toIndefData O C (numB x ε) := by
  obtain ⟨ha, hb⟩ := h hx ((testMap_iff O hl).2 ⟨hX, hk⟩)
  rw [hn.sig, ← hn.1, ← hn.2.1] at ha
  rw [← hn.1, ← hn.2.1] at hb
  change MeanNormBound Df XM vm C₀ O.f O.m O.N _ _ _ at ha
  change ScalarLowerBound hW S C₀ O.f O.m O.N _ _ at hb
  rw [infinitePlaceBound_iff hW S O hl, log_numB]
  have hL : 0 ≤ numL x ε := Real.rpow_nonneg (by linarith) _
  have hb0 : 0 ≤ numB x ε := (Real.exp_pos _).le
  have hS := Sig0_nonneg O C (numB x ε)
  refine ⟨fun _ => le_trans ha ?_, le_trans ?_ (hb.2.1.trans hb.1)⟩
  · have h1 : 0 ≤ (C - C₀) * ((O.f : ℝ) * O.m * O.N * numB x ε * numL x ε) := mul_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ (C - C₀) * ((O.m : ℝ) ^ 2 * (O.N : ℝ) ^ 2 * O.Sig0 C (numB x ε)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  · have h1 : 0 ≤ (C - C₀) * ((O.f : ℝ) * O.m * (O.N : ℝ) ^ 2 * numL x ε) := mul_nonneg (by linarith) (by positivity)
    linarith

theorem numL_add_le (E : Type) [Field E] [NumberField E] {x : ℝ} (ε : ℝ) (hx : 0 < x) :
    numL x ε + Real.log x ≤ numLa E x ε := by
  rw [numLa_eq E ε hx]
  have : 1 ≤ rootDiscr E := by
    refine Real.one_le_rpow ?_ (by positivity)
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  linarith [Real.log_nonneg this]

theorem mean_of_leafIP [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df)
    (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K))
    (E : Type) [Field E] [NumberField E] (C x ε : ℝ) (hC : 0 ≤ C)
    (hl : LinTie O XM vm) (hx : 1 ≤ x) (hT : TestMap Df XM vm) (h : LeafIP S.toIndefData O C (numB x ε)) :
    MeanNormBound Df XM vm C O.f O.m O.N (numB x ε) (numL x ε) (O.Sig0 C (numB x ε)) ∧
      -((3 * C) * O.f * O.m * (O.N : ℝ) ^ 2 * numLa E x ε) ≤ meanInf K (lamMin hW S) := by
  rw [infinitePlaceBound_iff hW S O hl, log_numB] at h
  refine ⟨h.1 hT.2.ge, le_trans ?_ h.2⟩
  have h1 := numL_add_le E ε (by linarith : 0 < x)
  have h2 := Real.log_nonneg hx
  have h3 : 0 ≤ (3 * C * O.f * O.m * (O.N : ℝ) ^ 2) * (numLa E x ε - numL x ε) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem tie_of_record (O : FunData K Df) :
    LinTie O (dualFrame O.X')
      (Matrix.toLin (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (Pi.basisFun K (Fin O.n)).dualBasis (O.vmu Bs.μ0)) := by
  refine ⟨fun v => ?_, ?_⟩
  · simp only [dualFrame, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.inv_inv_inv]
  · rw [dualMat, LinearMap.toMatrix_toLin]

open Classical in

def recordOf (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (E : Type) [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))) (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (k t g₁ g₂ p p' : ℕ) : FunData K Df where
  n := a
  X' := dualFrame XM
  M := ⊥
  vmu := Function.update (fun _ => 0) Bs.μ0 (dualMat vm)
  Tf := ∅
  dF := 0
  m := Fintype.card Bs.J
  rq := fun _ _ => 1
  dl := 0
  Sd := ∅
  Se := ∅
  N0 := 0
  zA := 0
  zA' := 0
  zT := 0
  zTd := 0
  gT := 0
  ch := fun _ => true
  dd := 0
  hd := 0
  yy := 0
  Sq := HeightOneSpectrum (𝓞 (maximalRealSubfield E))
  S0 := S0
  sv0 := v₀
  cc := 0
  qq := fun v => Ideal.absNorm v.asIdeal
  f := numF E
  k := k
  tt := t
  cl := 0
  g1 := g₁
  g2 := g₂
  pd := p
  pd' := p'
  dE := discr E
  Bw := 0

theorem tie_recordOf (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (E : Type) [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))) (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (k t g₁ g₂ p p' : ℕ) (C b : ℝ) :
    LinTie (recordOf Df XM vm E S0 v₀ k t g₁ g₂ p p') XM vm ∧
      NumTie (recordOf Df XM vm E S0 v₀ k t g₁ g₂ p p') E S0
        ((recordOf Df XM vm E S0 v₀ k t g₁ g₂ p p').ee C b) C b := by
  classical
  refine ⟨⟨fun _ => rfl, ?_⟩, rfl, rfl, id, Set.bijOn_id _, fun _ _ => ⟨rfl, rfl⟩⟩
  simp [recordOf]

theorem not_equiv [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df)
    (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hl : LinTie O XM vm) (hf : O.f = numF E) (hm : O.m = Fintype.card Bs.J) (hm0 : 0 < O.m) (hT : TestMap Df XM vm) :
    ∃ C x ε : ℝ, 0 < C ∧ 1 ≤ x ∧ LeafIP S.toIndefData O C (numB x ε) ∧
      ∀ S0 e, ¬ MeanBounds C hW S XM vm E S0 e O.k O.tt x ε := by
  have hf1 : (1 : ℝ) ≤ O.f := by
    rw [hf]; exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ (maximalRealSubfield E))
  have hm1 : (1 : ℝ) ≤ O.m := by exact_mod_cast hm0
  have hN1 : (1 : ℝ) ≤ O.N := by
    have : 1 ≤ O.N := le_add_left (Nat.mul_pos hm0 (Nat.succ_pos _))
    exact_mod_cast this
  set A := meanInf K (logNormV_sq Df XM vm)
  set B := meanInf K (lamMin hW S)
  set C : ℝ := 1 + |A| + |B| with hC
  have hC1 : 1 ≤ C := by have := abs_nonneg A; have := abs_nonneg B; linarith
  have hL : numL (Real.exp 3) 0 = 1 := Real.rpow_zero _
  have hb1 : 1 ≤ numB (Real.exp 3) 0 := Real.one_le_exp (by rw [hL]; norm_num)
  have hx : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hP : (1 : ℝ) ≤ O.f * O.m * (O.N : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hm1) (one_le_pow₀ hN1)
  have hCP : C ≤ C * (O.f * O.m * (O.N : ℝ) ^ 2) := le_mul_of_one_le_right (by linarith) hP
  refine ⟨C, Real.exp 3, 0, by linarith, hx, ?_, fun S0 e h => ?_⟩
  · rw [infinitePlaceBound_iff hW S O hl, log_numB, hL]
    refine ⟨fun _ => ?_, ?_⟩
    · have hQ : (1 : ℝ) ≤ O.f * O.m * O.N * numB (Real.exp 3) 0 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hf1 hm1) hN1) hb1
      have h1 : C ≤ C * (O.f * O.m * O.N * numB (Real.exp 3) 0) := le_mul_of_one_le_right (by linarith) hQ
      have hS := Sig0_nonneg O C (numB (Real.exp 3) 0)
      have h2 : 0 ≤ C * (O.m : ℝ) ^ 2 * (O.N : ℝ) ^ 2 * O.Sig0 C (numB (Real.exp 3) 0) := by positivity
      change A ≤ _
      linarith [le_abs_self A, abs_nonneg B]
    · linarith [neg_abs_le B, abs_nonneg A]
  · have h2 := (h hx hT).2.2.1
    rw [← hf, ← hm, hL] at h2
    change -(3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * 1) ≤ -(C * O.f * O.m * (O.N : ℝ) ^ 2 * _) at h2
    have h3 := numL_add_le E 0 (Real.exp_pos 3)
    rw [hL, Real.log_exp] at h3
    have h4 : 0 ≤ C * (O.f * O.m * (O.N : ℝ) ^ 2) * (numLa E (Real.exp 3) 0 - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

theorem pointwise_not_implied (hW : Df.WF) (S : IndefRows Df) (O : FunData K Df) (C b : ℝ) [Nonempty Bs.J]
    {v₁ v₂ : InfinitePlace K} (hv : v₁ ≠ v₂) (h : LeafIP S.toIndefData O C b) (c : ℝ) :
    ∃ S' : IndefRows Df, LeafIP S'.toIndefData O C b ∧ lamMin hW S' v₁ < c := by
  classical
  obtain ⟨ha, g, hg, hm⟩ := h
  obtain ⟨p, hp⟩ := occurring_nonempty hW S.pos
  set T : ℝ := |∑ j, Real.log (S.lam j Bs.μ0 p v₁) - c| + 1 with hT
  set u : InfinitePlace K → ℝ := Pi.single v₂ T - Pi.single v₁ T with hu
  have hu1 : u v₁ = -T := by simp [hu, hv]
  have hus : ∑ v, u v = 0 := by simp [hu, Finset.sum_sub_distrib]
  have hsum : ∀ q v, ∑ j, Real.log (Real.exp (u v) * S.lam j Bs.μ0 q v) =
      (Fintype.card Bs.J : ℝ) * u v + ∑ j, Real.log (S.lam j Bs.μ0 q v) := by
    intro q v
    rw [Finset.sum_congr rfl fun j _ => Real.log_mul (Real.exp_pos _).ne' (S.l1c.2.2.2.1 j Bs.μ0 q v).ne',
      Finset.sum_add_distrib, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨GlobalTheory.RowSlopeProbe.rescale S (fun v => Real.exp (u v)) fun v => Real.exp_pos _,
    ⟨ha, fun v => (Fintype.card Bs.J : ℝ) * u v + g v, fun v q hq => ?_, ?_⟩, ?_⟩
  · change _ ≤ ∑ j, Real.log (Real.exp (u v) * S.lam j Bs.μ0 q v)
    rw [hsum]; linarith [hg v q hq]
  · unfold meanInf at hm ⊢
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hus, mul_zero, zero_add]
    exact hm
  · refine lt_of_le_of_lt (Finset.inf'_le _ hp) ?_
    change ∑ j, Real.log (Real.exp (u v₁) * S.lam j Bs.μ0 p v₁) < c
    rw [hsum, hu1]
    have hJ : (1 : ℝ) ≤ Fintype.card Bs.J := by exact_mod_cast Fintype.card_pos
    have hT0 : 0 ≤ T := by positivity
    have := mul_le_mul_of_nonneg_right hJ hT0
    linarith [le_abs_self (∑ j, Real.log (S.lam j Bs.μ0 p v₁) - c)]

theorem testMap_proj (Df : DefSide Bs) :
    TestMap Df (fun _ => (1 : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ))
      (Matrix.toLin (Pi.basisFun K _) (Pi.basisFun K (Fin (Df.dQ Bs.μ0))).dualBasis (Df.Pq Bs.μ0)) := by
  refine ⟨fun _ => by simp, ?_⟩
  rw [← ker_dualMat, dualMat, LinearMap.toMatrix_toLin]
  rfl

theorem sample_not_equiv (v0 : InfinitePlace Examples₂.K3) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (w : HeightOneSpectrum (𝓞 Examples₂.K3)) :
    ∃ (hW : (Examples₂.two.df Examples₂.K3 v0).WF) (S : IndefRows (Examples₂.two.df Examples₂.K3 v0))
      (O : FunData Examples₂.K3 (Examples₂.two.df Examples₂.K3 v0)) (XM : _) (vm : _) (e : _) (C x ε : ℝ),
      LinTie O XM vm ∧ NumTie O E {v₀} e C (numB x ε) ∧ TestMap _ XM vm ∧ 1 ≤ x ∧
        LeafIP S.toIndefData O C (numB x ε) ∧ ¬ MeanBounds C hW S XM vm E {v₀} e O.k O.tt x ε := by
  let S : IndefRows (Examples₂.two.df Examples₂.K3 v0) := Examples₂.two.what₂ (a := 3) (kap := fun _ => 2) (l := fun _ => 5)
    (Examples₂.pairSet_conj w) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  have wf := Examples₂.two.wf Examples₂.K3 v0 (Examples₂.conjAt v0)
  have hT := testMap_proj (Examples₂.two.df Examples₂.K3 v0)
  have ht := fun C b => tie_recordOf (Examples₂.two.df Examples₂.K3 v0) (fun _ => 1)
    (Matrix.toLin (Pi.basisFun Examples₂.K3 _) (Pi.basisFun Examples₂.K3 _).dualBasis
      ((Examples₂.two.df Examples₂.K3 v0).Pq (Examples₂.two.base Examples₂.K3 v0).μ0)) E {v₀} v₀ 6 1 5 7 11 13 C b
  obtain ⟨C, x, ε, -, hx, h1, h2⟩ := not_equiv wf S _ _ _ E (ht 0 0).1 rfl rfl
    (Fintype.card_pos_iff.2 ⟨()⟩) hT
  exact ⟨wf, S, _, _, _, _, C, x, ε, (ht 0 0).1, (ht C (numB x ε)).2, hT, hx, h1, h2 _ _⟩

example : IsCMField (CyclotomicField 3 ℚ) := IsCyclotomicExtension.Rat.isCMField (S := {3}) _ ⟨3, rfl, by norm_num⟩

end GlobalTheory.Proof.DualMatrixMetricMeans
