import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpectralPartsAnticommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerFockOmegaActionAdjointLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeOmActKronBlockDiagonalLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockLoweringPartEqSubFockOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.HarmCoeff

section Analysis

theorem eq_zero_of_family {κ : Type} (D : κ → ℝ → ℂ) (σ : κ → κ)
    (han : ∀ k, AnalyticOnNhd ℝ (D k) Set.univ) (hd : ∀ k t, HasDerivAt (D k) (D (σ k) t) t)
    (h0 : ∀ k, D k 0 = 0) (k : κ) (t : ℝ) : D k t = 0 := by
  have hit : ∀ (n : ℕ) k, iteratedDeriv n (D k) = D (σ^[n] k) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [iteratedDeriv_succ']
      have : deriv (D v) = D (σ v) := by
        ext s
        exact (hd v s).deriv
      rw [this, ih]
      rfl
  have htop : analyticOrderAt (D k) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han k 0 trivial)]
    intro i _
    rw [hit, h0]
  exact (han k).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)

variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {ι : V →ₗ[ℂ] H} {u : ℝ → V →ₗ[ℂ] H} {A : Module.End ℂ V}

theorem hasDerivAt_coeff (hder : ∀ P t, HasDerivAt (fun t => u t P) (u t (A P)) t) (x : H) (P : V)
    (t : ℝ) : HasDerivAt (fun t => inner ℂ x (u t P)) (inner ℂ x (u t (A P))) t :=
  ((innerSL ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hder P t)

theorem intertwine (h0 : u 0 = ι) (han : ∀ P, AnalyticOnNhd ℝ (fun t => u t P) Set.univ)
    (hder : ∀ P t, HasDerivAt (fun t => u t P) (u t (A P)) t) (B B' : Module.End ℂ V) (μ : ℝ)
    (hB : A * B - B * A = (μ : ℂ) • B)
    (hadj : ∀ x y, inner ℂ (ι (B' x)) (ι y) = inner ℂ (ι x) (ι (B y))) (Q P : V) (t : ℝ) :
    inner ℂ (ι (B' Q)) (u t P) = (Real.exp (-μ * t) : ℂ) * inner ℂ (ι Q) (u t (B P)) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_family
    (fun P t => inner ℂ (ι (B' Q)) (u t P) - (Real.exp (-μ * t) : ℂ) * inner ℂ (ι Q) (u t (B P)))
    A (fun P x hx => ?_) (fun P t => ?_) (fun P => ?_) P t
  · have h1 : ∀ (y : H) P, AnalyticAt ℝ (fun t => inner ℂ y (u t P)) x := fun y P =>
      (((innerSL ℂ y).restrictScalars ℝ).analyticAt _).comp (han P x hx)
    have h2 : AnalyticAt ℝ (fun t : ℝ => (Real.exp (-μ * t) : ℂ)) x :=
      (Complex.ofRealCLM.analyticAt _).comp (f := fun t : ℝ => Real.exp (-μ * t)) (by fun_prop)
    exact (h1 _ _).sub (h2.mul (h1 _ _))
  · have h2 : HasDerivAt (fun t : ℝ => (Real.exp (-μ * t) : ℂ))
        ((Real.exp (-μ * t) * (-μ * 1) : ℝ) : ℂ) t :=
      (((hasDerivAt_id' t).const_mul (-μ)).exp).ofReal_comp
    have h3 := (hasDerivAt_coeff hder (ι (B' Q)) P t).sub
      (h2.mul (hasDerivAt_coeff hder (ι Q) (B P) t))
    refine h3.congr_deriv ?_
    have e : A (B P) = B (A P) + (μ : ℂ) • B P := by
      have := LinearMap.congr_fun hB P
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [← this]; abel
    rw [e, map_add, map_smul, inner_add_right, inner_smul_right]
    push_cast
    ring
  · simp [h0, hadj]

theorem odd_coeff (h0 : u 0 = ι) (han : ∀ P, AnalyticOnNhd ℝ (fun t => u t P) Set.univ)
    (hder : ∀ P t, HasDerivAt (fun t => u t P) (u t (A P)) t) (N S K : Module.End ℂ V) (ν : ℝ)
    (hN : A * N = N * A) (hS : A * S - S * A = (-2 * ν : ℂ) • K)
    (hK : A * K - K * A = (-2 * ν : ℂ) • S)
    (aN : ∀ x y, inner ℂ (ι (N x)) (ι y) = -inner ℂ (ι x) (ι (N y)))
    (aS : ∀ x y, inner ℂ (ι (S x)) (ι y) = inner ℂ (ι x) (ι (S y)))
    (aK : ∀ x y, inner ℂ (ι (K x)) (ι y) = inner ℂ (ι x) (ι (K y)))
    (Q P : V) (hQ : N Q = S Q) (hP : N P = S P) (t : ℝ) :
    inner ℂ (ι Q) (u t (N P)) =
      ((-(Real.sinh (2 * ν * t) / (1 + Real.cosh (2 * ν * t))) : ℝ) : ℂ) *
        inner ℂ (ι Q) (u t (K P)) := by
  have e1 := intertwine h0 han hder N (-N) 0 (by simp [hN]) (fun x y => by simp [aN]) Q P t
  have e2 := intertwine h0 han hder (S + K) (S + K) (-2 * ν) (by
    push_cast
    rw [mul_add, add_mul, smul_add, ← hS, ← hK]; abel)
    (fun x y => by simp [aS, aK]) Q P t
  have e3 := intertwine h0 han hder (S - K) (S - K) (2 * ν) (by
    push_cast
    have : (2 * ν : ℂ) • (S - K) = (-2 * ν : ℂ) • K - (-2 * ν : ℂ) • S := by module
    rw [this, mul_sub, sub_mul, ← hS, ← hK]; abel)
    (fun x y => by simp [aS, aK]) Q P t
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, map_add, map_sub,
    map_neg, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    ← hQ, ← hP, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] at e1 e2 e3
  have hc : (1 + Real.cosh (2 * ν * t)) ≠ 0 := by
    have := Real.cosh_pos (2 * ν * t); positivity
  have hc' : ((1 + Real.cosh (2 * ν * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have a1 : Real.exp (-(-2 * ν) * t) = Real.cosh (2 * ν * t) + Real.sinh (2 * ν * t) := by
    rw [Real.cosh_add_sinh]; congr 1; ring
  have a2 : Real.exp (-(2 * ν) * t) = Real.cosh (2 * ν * t) - Real.sinh (2 * ν * t) := by
    rw [Real.cosh_sub_sinh]; congr 1; ring
  rw [a1] at e2
  rw [a2] at e3
  rw [Complex.ofReal_neg, Complex.ofReal_div]
  rw [Complex.ofReal_add] at e2 hc' ⊢
  rw [Complex.ofReal_sub] at e3
  rw [Complex.ofReal_one] at hc' ⊢
  field_simp
  linear_combination (-1 / 2 : ℂ) * e2 + (-1 / 2 : ℂ) * e3 - e1

theorem coeff_eigen (h0 : u 0 = ι) (han : ∀ P, AnalyticOnNhd ℝ (fun t => u t P) Set.univ)
    (hder : ∀ P t, HasDerivAt (fun t => u t P) (u t (A P)) t) (s : Finset ℝ)
    (N S K : ℝ → Module.End ℂ V) (hA : A = ∑ ν ∈ s, (ν : ℂ) • N ν)
    (hN : ∀ ν, A * N ν = N ν * A) (hS : ∀ ν, A * S ν - S ν * A = (-2 * ν : ℂ) • K ν)
    (hK : ∀ ν, A * K ν - K ν * A = (-2 * ν : ℂ) • S ν)
    (aN : ∀ ν x y, inner ℂ (ι (N ν x)) (ι y) = -inner ℂ (ι x) (ι (N ν y)))
    (aS : ∀ ν x y, inner ℂ (ι (S ν x)) (ι y) = inner ℂ (ι x) (ι (S ν y)))
    (aK : ∀ ν x y, inner ℂ (ι (K ν x)) (ι y) = inner ℂ (ι x) (ι (K ν y)))
    (P : V) (hP : ∀ ν, N ν P = S ν P) (m : ℝ → ℝ) (hm : ∀ ν, K ν P = (m ν : ℂ) • P) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q, (∀ ν, N ν Q = S ν Q) →
      inner ℂ (ι Q) (u 1 P) = (c : ℂ) * inner ℂ (ι Q) (ι P) := by
  let φ : ℝ → ℝ := fun t => ∑ ν ∈ s, m ν / 2 * Real.log (1 + Real.cosh (2 * ν * t))
  let ψ : ℝ → ℝ := fun t => ∑ ν ∈ s, ν * m ν * (Real.sinh (2 * ν * t) / (1 + Real.cosh (2 * ν * t)))
  have hφ : ∀ t, HasDerivAt φ (ψ t) t := fun t => by
    refine HasDerivAt.fun_sum fun ν _ => ?_
    have hc : (1 + Real.cosh (2 * ν * t)) ≠ 0 := by
      have := Real.cosh_pos (2 * ν * t); positivity
    have := ((((hasDerivAt_id' t).const_mul (2 * ν)).cosh.const_add 1).log hc).const_mul (m ν / 2)
    refine this.congr_deriv ?_
    ring
  refine ⟨Real.exp (φ 0 - φ 1), Real.exp_pos _, fun Q hQ => ?_⟩
  have hg : ∀ t, HasDerivAt (fun t => (Real.exp (φ t) : ℂ) * inner ℂ (ι Q) (u t P)) 0 t := fun t => by
    have h1 := ((hφ t).exp.ofReal_comp).mul (hasDerivAt_coeff hder (ι Q) P t)
    refine h1.congr_deriv ?_
    have e : inner ℂ (ι Q) (u t (A P)) = -(ψ t : ℂ) * inner ℂ (ι Q) (u t P) := by
      conv_lhs => rw [hA]
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, inner_sum,
        inner_smul_right, Complex.ofReal_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [odd_coeff h0 han hder (N ν) (S ν) (K ν) ν (hN ν) (hS ν) (hK ν) (aN ν) (aS ν) (aK ν) Q P
        (hQ ν) (hP ν) t, hm, map_smul, inner_smul_right]
      simp only [Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [e, Complex.ofReal_mul]
    ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [h0] at hc
  rw [Real.exp_sub, Complex.ofReal_div, div_mul_eq_mul_div, ← hc]
  have : ((Real.exp (φ 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  field_simp

end Analysis

open Matrix Kronecker

theorem Jm_mul_Jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jm_ct (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isPC_iff {p q : ℕ} (Z : Mat p q) : IsPC Z ↔ Jm p q * Z = -(Z * Jm p q) := by
  rw [Jm_diag, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.sameBlock, eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero]

theorem isKC_of {p q : ℕ} (Z : Mat p q) (h : Jm p q * Z = Z * Jm p q) : IsKC Z := by
  rw [Jm_diag, ← Matrix.ext_iff] at h
  intro a b hab
  have := h a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.BasicNotions.TH.sameBlock, eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero] at this hab ⊢ <;>
    exact this

theorem sub_kron {m n : Type} (A B : Matrix m m ℂ) (C : Matrix n n ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext a b; simp [sub_mul]

theorem neg_kron {m n : Type} (A : Matrix m m ℂ) (C : Matrix n n ℂ) :
    (-A) ⊗ₖ C = -(A ⊗ₖ C) := by
  ext a b; simp

theorem inner_exp_jointHarm_pos : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Y ∈ pR p q, ∀ P ∈ jointHarm p q r s, P ≠ 0 → (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).im = 0 ∧ 0 < (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).re := by
  intro p q r s T0 T1 T2 F Y hY P hP hP0
  have hJY : Jm p q * Y = -(Y * Jm p q) := (isPC_iff Y).1 hY.2
  have hJ := Jm_mul_Jm p q
  have hJ2 := Jm_mul_Jm r s
  have hJ' : ∀ Z : Mat p q, Z * Jm p q * Jm p q = Z := fun Z => by
    rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  have hYh : Y.IsHermitian := by
    have h1 : Yᴴ * Jm p q + Jm p q * Y = 0 := hY.1
    rw [hJY, ← sub_eq_add_neg, sub_eq_zero] at h1
    have := congrArg (· * Jm p q) h1
    simp only [hJ'] at this
    exact this
  obtain ⟨s₀, N, E, hsum, hNE, hEE⟩ := GlobalTheory.T.hermitian_spectral_projections_anticommute _ Y (Jm p q) hYh hJY
  have lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).1
  have adj := GlobalTheory.T.inner_fockOmegaAction_adjoint_lines p q r s F.H F.ι (isFockIsometry_of_fockData F)
  set ω := omAct p q r s with hω
  set J := Jm p q with hJdef
  set J₂ := Jm r s with hJ2def
  have hJh : Jᴴ = J := Jm_ct p q
  have hJ2h : J₂ᴴ = J₂ := Jm_ct r s
  have hYJ : Y * J = -(J * Y) := by rw [hJY, neg_neg]

  let U : ℝ → F.H →L[ℂ] F.H := fun t => F.π (T1.expt (t • Y), 1)
  have hU : ∀ a b, U (a + b) = U a * U b := fun a b => by
    simp only [U, T1.expt_add Y hY.1, ← map_mul, Prod.mk_mul_mk, mul_one]
  let u : ℝ → Pol p q r s →ₗ[ℂ] F.H := fun t => (U t : F.H →ₗ[ℂ] F.H) ∘ₗ F.ι
  have h0 : u 0 = F.ι := by
    refine LinearMap.ext fun x => ?_
    have : ((1 : T1.G), (1 : T2.G)) = 1 := rfl
    simp [u, U, T1.expt_zero, this]
  have hder : ∀ P t, HasDerivAt (fun t => u t P) (u t (ω (Y ⊗ₖ (1 : Mat r s)) P)) t := fun P t =>
    GlobalTheory.OrbitAnalytic.hasDerivAt_orbit U hU _ _
      ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1 Y hY.1 P) t
  have han : ∀ P, AnalyticOnNhd ℝ (fun t => u t P) Set.univ := fun P a _ => by
    set Z : Matrix (Ln p q r s) (Ln p q r s) ℂ := Y ⊗ₖ (1 : Mat r s)
    set S : ℝ := 4 * ∑ l, ∑ l', ‖Z l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    have := GlobalTheory.OrbitAnalytic.analyticAt_of_bound (fun k t => u t ((ω Z ^ k) P))
      (fun k t => by simpa only [pow_succ', Module.End.mul_apply] using hder ((ω Z ^ k) P) t)
      ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    · simpa using this
    have hb := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Z P.totalDegree k P le_rfl).2
    have e : ‖u t ((ω Z ^ k) P)‖ = ‖F.ι ((ω Z ^ k) P)‖ := F.isom _ _
    rw [e]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring

  let L : Mat p q → Matrix (Ln p q r s) (Ln p q r s) ℂ :=
    fun Z => Z ⊗ₖ (1 : Mat r s) - (J * Z) ⊗ₖ J₂
  let W : Submodule ℂ (Pol p q r s) :=
    (⨅ Z : Mat p q, ⨅ _ : J * Z = -(Z * J), LinearMap.ker (ω (L Z))) ⊓
      restrictTotalDegree (Ln p q r s) ℂ P.totalDegree
  have memW : ∀ w, w ∈ W ↔ (∀ Z : Mat p q, J * Z = -(Z * J) → ω (L Z) w = 0) ∧
      w.totalDegree ≤ P.totalDegree := fun w => by
    simp [W, Submodule.mem_iInf, mem_restrictTotalDegree]
  have hfin : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have hPW : P ∈ W := (memW P).2 ⟨fun Z hZ => by
    have hZ' := (isPC_iff Z).2 hZ
    have := GlobalTheory.T.fockLoweringPart_eq_sub_fockOperators p q r s Z hZ' P
    rw [hP.1 Z hZ', smul_zero] at this
    simpa only [L, map_sub, LinearMap.sub_apply] using this, le_rfl⟩
  have aK : ∀ ν x y, inner ℂ (F.ι (ω ((J * E ν) ⊗ₖ J₂) x)) (F.ι y) =
      inner ℂ (F.ι x) (F.ι (ω ((J * E ν) ⊗ₖ J₂) y)) := fun ν x y => by
    rw [adj, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, conjTranspose_mul,
      (hNE ν).2.1.eq, hJh, hJ2h, hJ2, Matrix.one_mul, ← Matrix.mul_assoc, hJ']
  have hNS : ∀ w ∈ W, ∀ ν, ω (N ν ⊗ₖ (1 : Mat r s)) w = ω ((J * N ν) ⊗ₖ J₂) w := fun w hw ν => by
    have := ((memW w).1 hw).1 (N ν) (hNE ν).2.2.2.2.2.2.1
    simpa only [L, map_sub, LinearMap.sub_apply, sub_eq_zero] using this
  have key := GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors _ F.H F.ι F.ι_inj W hfin ℝ (fun ν => ω ((J * E ν) ⊗ₖ J₂))
    (fun ν w hw => ?_) aK (fun ν ν' => ?_) (u 1) (fun m y hy hm => ?_) P hPW hP0
  · simpa [u, U] using key
  · obtain ⟨h1, h2⟩ := (memW w).1 hw
    have hE : J * E ν = E ν * J := (hNE ν).2.2.2.2.2.2.2
    refine (memW _).2 ⟨fun Z hZ => ?_, GlobalTheory.T.totalDegree_omAct_kron_blockDiagonal_le p q r s _ (isKC_of _ ?_) _ w h2⟩
    · have hZ' : Z * J = -(J * Z) := by rw [hZ, neg_neg]
      have e : L Z * ((J * E ν) ⊗ₖ J₂) - ((J * E ν) ⊗ₖ J₂) * L Z = L (Z * E ν + E ν * Z) := by
        have e1 : Z * (J * E ν) = -(J * (Z * E ν)) := by
          rw [← Matrix.mul_assoc, hZ', Matrix.neg_mul, Matrix.mul_assoc]
        have e2 : J * Z * (J * E ν) = -(Z * E ν) := by
          rw [Matrix.mul_assoc, e1, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
        have e3 : J * E ν * (J * Z) = E ν * Z := by
          rw [hE, ← Matrix.mul_assoc, hJ']
        simp only [L, Matrix.sub_mul, Matrix.mul_sub, ← mul_kronecker_mul, e1, e2, e3, hJ2,
          Matrix.one_mul, Matrix.mul_one, Matrix.mul_add, add_kronecker, neg_kron,
          Matrix.mul_assoc J (E ν) Z]
        abel
      have e' := LinearMap.congr_fun (lie (L Z) ((J * E ν) ⊗ₖ J₂)) w
      rw [e, h1 _ ?_] at e'
      · simp only [LinearMap.sub_apply, Module.End.mul_apply, h1 Z hZ, map_zero, sub_zero] at e'
        exact e'.symm
      · rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hZ, hE,
          Matrix.mul_assoc (E ν), hZ, Matrix.mul_assoc Z (E ν), ← hE]
        simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, neg_add]
    · rw [← hJdef, Matrix.mul_assoc, ← hE]
  · have e1 : ∀ a b, J * E a * (J * E b) = E a * E b := fun a b => by
      rw [(hNE a).2.2.2.2.2.2.2, ← Matrix.mul_assoc, hJ']
    rw [← sub_eq_zero, ← lie, ← mul_kronecker_mul, ← mul_kronecker_mul, e1, e1, hEE, sub_self,
      map_zero]
  · refine Exists.imp (fun c h => ⟨h.1, fun x hx => h.2 x (hNS x hx)⟩) <| coeff_eigen h0 han hder s₀
      (fun ν => ω (N ν ⊗ₖ (1 : Mat r s)))
      (fun ν => ω ((J * N ν) ⊗ₖ J₂)) (fun ν => ω ((J * E ν) ⊗ₖ J₂)) ?_ (fun ν => ?_) (fun ν => ?_)
      (fun ν => ?_) (fun ν x y => ?_) (fun ν x y => ?_) aK y (hNS y hy) m hm
    · have e : Y ⊗ₖ (1 : Mat r s) = ∑ ν ∈ s₀, (ν : ℂ) • N ν ⊗ₖ (1 : Mat r s) := by
        conv_lhs => rw [hsum]
        ext a b
        simp [Matrix.sum_apply, Finset.sum_mul, mul_assoc]
      rw [e, map_sum]
      simp only [map_smul]
    · rw [← sub_eq_zero, ← lie, ← mul_kronecker_mul, ← mul_kronecker_mul, (hNE ν).2.2.1,
        (hNE ν).2.2.2.1, sub_self, map_zero]
    · rw [← lie, ← mul_kronecker_mul, ← mul_kronecker_mul, ← map_smul, Matrix.one_mul,
        Matrix.mul_one, ← sub_kron, ← smul_kronecker, ← Matrix.mul_assoc, hYJ, Matrix.neg_mul,
        Matrix.mul_assoc, Matrix.mul_assoc, (hNE ν).2.2.1, (hNE ν).2.2.2.1, Matrix.mul_smul]
      congr 2
      module
    · rw [← lie, ← mul_kronecker_mul, ← mul_kronecker_mul, ← map_smul, Matrix.one_mul,
        Matrix.mul_one, ← sub_kron, ← smul_kronecker, ← Matrix.mul_assoc, hYJ, Matrix.neg_mul,
        Matrix.mul_assoc, Matrix.mul_assoc, (hNE ν).2.2.2.2.1, (hNE ν).2.2.2.2.2.1, Matrix.mul_smul]
      congr 2
      module
    · rw [adj, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
        (hNE ν).1.eq, conjTranspose_one, Matrix.mul_one, hJ2, (hNE ν).2.2.2.2.2.2.1,
        Matrix.neg_mul, hJ', neg_kron, map_neg, LinearMap.neg_apply, map_neg, inner_neg_right]
    · rw [adj, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, conjTranspose_mul,
        (hNE ν).1.eq, hJh, hJ2h, hJ2, Matrix.one_mul, ← Matrix.mul_assoc, hJ']

end GlobalTheory.HarmCoeff
