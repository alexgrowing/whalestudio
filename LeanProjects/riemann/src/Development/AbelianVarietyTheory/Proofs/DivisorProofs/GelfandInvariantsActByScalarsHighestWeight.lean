import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.GelfScalar

section Algebra

variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]

def opM (ρ : Mt n →ₗ[ℂ] A) (p q : Mt n) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => ρ (p * Matrix.single a b 1 * q)

private theorem single_one_mul_single_one' (p q : Mt n) (a b : Fin n) :
    p * Matrix.single a b 1 * q = ∑ i, ∑ j, (p i a * q b j) • Matrix.single i j (1 : ℂ) := by
  ext x y
  have hl : (p * Matrix.single a b 1 * q : Mt n) x y = p x a * q b y := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, mul_ite]
  rw [hl, Matrix.sum_apply, Fintype.sum_eq_single x (fun c hc => by
      rw [Matrix.sum_apply]; simp [Matrix.single_apply, hc]),
    Matrix.sum_apply, Fintype.sum_eq_single y (fun c hc => by simp [Matrix.single_apply, hc])]
  simp

private theorem mul_inv_mul_eq_mul_inv_mul_of_factorizations (c d : ℂ) (x : A) :
    algebraMap ℂ A c * x * algebraMap ℂ A d = (c * d) • x := by
  rw [mul_assoc, ← Algebra.commutes d x, ← mul_assoc, ← map_mul, ← Algebra.smul_def]

theorem opM_eq (ρ : Mt n →ₗ[ℂ] A) (p q : Mt n) :
    opM ρ p q = (pᵀ).map (algebraMap ℂ A) * opM ρ 1 1 * (qᵀ).map (algebraMap ℂ A) := by
  ext a b
  simp only [opM, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, one_mul, mul_one,
    single_one_mul_single_one', map_sum, map_smul, Finset.sum_mul, mul_inv_mul_eq_mul_inv_mul_of_factorizations]
  rw [Finset.sum_comm]

theorem trace_map_mul (x : Mt n) (M : Matrix (Fin n) (Fin n) A) :
    (x.map (algebraMap ℂ A) * M).trace = (M * x.map (algebraMap ℂ A)).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  simp only [Algebra.commutes]

private theorem pow_succ_conj_of_mul_eq_one {P O Q : Matrix (Fin n) (Fin n) A} (h : Q * P = 1) (m : ℕ) :
    (P * O * Q) ^ (m + 1) = P * O ^ (m + 1) * Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ O (m + 1)]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h, one_mul]

theorem trace_opM_pow (ρ : Mt n →ₗ[ℂ] A) {p q : Mt n} (h : p * q = 1) (m : ℕ) :
    (opM ρ p q ^ m).trace = (opM ρ 1 1 ^ m).trace := by
  rcases m with _ | m
  · simp
  rw [opM_eq ρ p q]
  have hQP : (qᵀ).map (algebraMap ℂ A) * (pᵀ).map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.transpose_mul, h, Matrix.transpose_one]
    first
    | simp
    | exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [pow_succ_conj_of_mul_eq_one hQP, mul_assoc, trace_map_mul, mul_assoc, hQP, mul_one]

theorem glRel_opM (ρ : Mt n →ₗ[ℂ] A) (hρ : ∀ Z Z', ρ (Z * Z' - Z' * Z) = ρ Z * ρ Z' - ρ Z' * ρ Z)
    {p q : Mt n} (h : q * p = 1) : GlobalTheory.Mem.Gelf.GlRel (opM ρ p q) := by
  intro a b c d
  have e : ∀ X Y : Mt n, p * X * q * (p * Y * q) = p * (X * Y) * q := by
    intro X Y
    simp only [mul_assoc]
    rw [← mul_assoc q p, h, one_mul]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    have hz : ∀ i j k l : Fin n, j ≠ k → Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = 0 := by
      intro i j k l hjk
      apply Matrix.single_mul_single_of_ne
      exact hjk
    by_cases hbc : b = c <;> by_cases hda : d = a
    · subst hbc; subst hda; simp [Matrix.single_mul_single_same]
    · subst hbc; simp [Matrix.single_mul_single_same, hz _ _ _ _ hda, hda]
    · subst hda; simp [Matrix.single_mul_single_same, hz _ _ _ _ hbc, hbc]
    · simp [hz _ _ _ _ hbc, hz _ _ _ _ hda, hbc, hda]
  simp only [opM, Matrix.of_apply]
  rw [← hρ, e, e, ← sub_mul, ← mul_sub, hm]
  split_ifs <;> simp [mul_sub, sub_mul]

theorem pow_intertwine {E F : Matrix (Fin n) (Fin n) A} {T : A} (h : ∀ a b, T * E a b = F a b * T) (m : ℕ)
    (a b : Fin n) : T * (E ^ m) a b = (F ^ m) a b * T := by
  induction m generalizing a b with
  | zero =>
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  | succ m ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

end Algebra

theorem pow_adjoint {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : Submodule ℂ H}
    {E F : Matrix (Fin n) (Fin n) (Module.End ℂ S)}
    (h : ∀ a b (v v' : S), ⟪(E a b v : H), (v' : H)⟫_ℂ = ⟪(v : H), (F b a v' : H)⟫_ℂ) (m : ℕ) (a b : Fin n)
    (v v' : S) : ⟪((E ^ m) a b v : H), (v' : H)⟫_ℂ = ⟪(v : H), ((F ^ m) b a v' : H)⟫_ℂ := by
  induction m generalizing a b v v' with
  | zero =>
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]
  | succ m ih =>
    rw [pow_succ, pow_succ', Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
      Submodule.coe_sum, Submodule.coe_sum, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, ih, h]

section Rep

variable {n : ℕ} {Hm : Mt n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mt n → (H →L[ℂ] H)}

open GlobalTheory.SmVec (smSub)

def dEnd (hh : Hm.IsHermitian) (hd : Hm.det ≠ 0) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) :
    Mt n →ₗ[ℂ] Module.End ℂ (smSub Hm σ) where
  toFun Z :=
    { toFun := fun v => ⟨dRepC Hm σ Z v.1,
        GlobalTheory.SmVec.dRepC_mem ((Matrix.isUnit_iff_isUnit_det Hm).2 hd.isUnit) hh hσ Z v.2⟩
      map_add' := fun v v' => Subtype.ext (by
        simpa using ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 v'.1 v.2 v'.2).1 1 Z Z).2.1)
      map_smul' := fun c v => Subtype.ext (by
        have h0 := ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ 0 0 (smSub Hm σ).zero_mem (smSub Hm σ).zero_mem).1 1 Z Z).2.1
        have h1 := ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 0 v.2 (smSub Hm σ).zero_mem).1 c Z Z).2.1
        simp only [one_smul, add_zero, left_eq_add] at h0
        simpa [h0] using h1) }
  map_add' Z Z' := LinearMap.ext fun v => Subtype.ext (by
    simpa using ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 v.1 v.2 v.2).1 1 Z Z').1)
  map_smul' c Z := LinearMap.ext fun v => Subtype.ext (by
    have h0 := ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 v.1 v.2 v.2).1 1 0 0).1
    have h1 := ((GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 v.1 v.2 v.2).1 c Z 0).1
    simp only [one_smul, add_zero, left_eq_add] at h0
    simpa [h0] using h1)

theorem dEnd_coe (hh : Hm.IsHermitian) (hd : Hm.det ≠ 0) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (Z : Mt n)
    (v : smSub Hm σ) : (dEnd hh hd hσ Z v : H) = dRepC Hm σ Z v.1 := rfl

theorem foldr_eq {S : Submodule ℂ H} (l : List (Mt n)) (f : Mt n → H → H) (F : Mt n → Module.End ℂ S)
    (h : ∀ Z (v : S), (F Z v : H) = f Z v) (v : S) :
    (l.map f).foldr (fun f acc => f acc) (v : H) = ((l.map F).prod v : S) := by
  induction l with
  | nil => simp
  | cons Z l ih => simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply, ih, h]

private theorem pow_succ_apply_eq_sum_path_prod {R : Type} [Ring R] (E : Matrix (Fin n) (Fin n) R) (m : ℕ) (i j : Fin n) :
    (E ^ (m + 1)) i j = ∑ idx : Fin m → Fin n,
      (List.ofFn fun a : Fin (m + 1) =>
        E ((Fin.cons i idx : Fin (m + 1) → Fin n) a) ((Fin.snoc idx j : Fin (m + 1) → Fin n) a)).prod := by
  induction m generalizing i with
  | zero => simp [List.ofFn_succ, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin n), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun idx _ => ?_
    show _ = (List.ofFn fun a : Fin (m + 1 + 1) =>
      E ((Fin.cons i (Fin.cons c idx : Fin (m + 1) → Fin n) : Fin (m + 1 + 1) → Fin n) a)
        ((Fin.snoc (Fin.cons c idx : Fin (m + 1) → Fin n) j : Fin (m + 1 + 1) → Fin n) a)).prod
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]

private theorem false_of_cdist_between_both_ways {R : Type} [Ring R] (E : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n, (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).prod =
      (E ^ (k + 1)).trace := by
  have hs : ∀ (i : Fin n) (idx : Fin k → Fin n) (a : Fin (k + 1)),
      (Fin.cons i idx : Fin (k + 1) → Fin n) (a + 1) = (Fin.snoc idx i : Fin (k + 1) → Fin n) a := by
    intro i idx a
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp [Fin.last_add_one]
    · rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]
  simp only [Matrix.trace, Matrix.diag, pow_succ_apply_eq_sum_path_prod]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin n), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun idx _ => ?_
  show (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons i idx : Fin (k + 1) → Fin n) a) ((Fin.cons i idx : Fin (k + 1) → Fin n) (a + 1))).prod = _
  simp only [hs]

theorem gelfRep_eq (hh : Hm.IsHermitian) (hd : Hm.det ≠ 0) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (k : ℕ)
    (v : smSub Hm σ) : gelfRep Hm σ k v = ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace v : smSub Hm σ) := by
  rw [← false_of_cdist_between_both_ways, LinearMap.sum_apply, Submodule.coe_sum]
  unfold gelfRep
  refine Finset.sum_congr rfl fun idx _ => ?_
  have e1 : (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)) =
      (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)).map (dRepC Hm σ) := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun a : Fin (k + 1) => opM (dEnd hh hd hσ) 1 1 (idx a) (idx (a + 1))) =
      (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)).map (dEnd hh hd hσ) := by
    rw [List.map_ofFn]; simp [opM, Function.comp_def]
  rw [e1, e2]
  exact foldr_eq _ _ _ (fun Z w => dEnd_coe hh hd hσ Z w) v

omit [CompleteSpace H] in

theorem eq_zero_of_inner_orbit (hd : Hm.det ≠ 0) (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ)
    (hi : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ) {v₀ : H} (h0 : v₀ ≠ 0) {y : H}
    (hy : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ⟪y, σ g v₀⟫_ℂ = 0) : y = 0 := by
  obtain ⟨⟨hσ1, hσmul⟩, -, -⟩ := hσ
  have hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ h ∈ Formalism.QuantumDeterminants.UH Hm, g * h ∈ Formalism.QuantumDeterminants.UH Hm := by
    intro g hg h hh'
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh' ⊢
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hm * (g * h) = hᴴ * (gᴴ * Hm * g) * h := by simp only [mul_assoc]
      _ = Hm := by rw [hg, hh']
  have h1 : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by simp [Formalism.QuantumDeterminants.UH]
  let S : Submodule ℂ H := (Submodule.span ℂ ((fun g => σ g v₀) '' Formalism.QuantumDeterminants.UH Hm)).topologicalClosure
  have hv₀S : v₀ ∈ S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, h1, by simp [hσ1]⟩)
  have hinv : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ v ∈ S, σ g v ∈ S := by
    intro g hg
    have hle : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      apply Submodule.topologicalClosure_minimal
      · rw [Submodule.span_le]
        rintro _ ⟨h, hh', rfl⟩
        show σ g (σ h v₀) ∈ S
        rw [← ContinuousLinearMap.comp_apply, ← hσmul g hg h hh']
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g * h, hmul g hg h hh', rfl⟩)
      · exact (Submodule.isClosed_topologicalClosure _).preimage (σ g).continuous
    exact fun v hv => hle hv
  rcases hi S (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
  · rw [hbot, Submodule.mem_bot] at hv₀S
    exact absurd hv₀S h0
  · have hle : S ≤ LinearMap.ker (innerSL ℂ y : H →ₗ[ℂ] ℂ) := by
      apply Submodule.topologicalClosure_minimal
      · rw [Submodule.span_le]
        rintro _ ⟨g, hg, rfl⟩
        simp [hy g hg]
      · exact ContinuousLinearMap.isClosed_ker (innerSL ℂ y)
    have hyS : y ∈ S := by rw [htop]; exact Submodule.mem_top
    have := hle hyS
    simpa using this

end Rep

theorem orthFr_facts {n : ℕ} {Hm : Mt n} {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀) :
    Hm.IsHermitian ∧ Hm.det ≠ 0 ∧ x₀.det ≠ 0 := by
  obtain ⟨-, h⟩ := h
  have hD : ∀ a : Fin n, -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal] at hdet
  have hprod : ∏ a : Fin n, -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => hD a
  have hHd : Hm.det ≠ 0 := by
    intro h0; apply hprod; rw [← hdet, h0]; simp
  have hxd : x₀.det ≠ 0 := by
    intro h0; apply hprod; rw [← hdet, h0]; simp
  refine ⟨?_, hHd, hxd⟩
  have hxu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).2 hxd.isUnit
  have hxu' : IsUnit x₀ᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_conjTranspose]; exact (star_ne_zero.2 hxd).isUnit)
  have h2 := congrArg Matrix.conjTranspose h
  rw [Matrix.diagonal_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] at h2
  have hstar : star (fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) =
      fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) := by
    funext a; simp
  rw [hstar, ← h, ← mul_assoc] at h2
  exact hxu'.mul_left_cancel (hxu.mul_right_cancel h2)

theorem gelfRep_scalar : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n) (w : Fin n → ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), OrthFr Hm q x₀ → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v₀, v₀ ≠ 0 → SmoothVec (lieH Hm) σ v₀ → (∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v₀ = if a = c then (w a : ℂ) • v₀ else 0) → ∀ k, ∃ c : ℂ, ∀ v, SmoothVec (lieH Hm) σ v → gelfRep Hm σ k v = c • v := by
  intro n Hm q x₀ w H _ _ _ σ hfr hσ hi v₀ hv₀ hsm hw k
  obtain ⟨hh, hd, hdx⟩ := orthFr_facts hfr
  have hHu : IsUnit Hm := (Matrix.isUnit_iff_isUnit_det Hm).2 hd.isUnit
  obtain ⟨v₀s, rfl⟩ : ∃ u : GlobalTheory.SmVec.smSub Hm σ, (u : H) = v₀ := ⟨⟨v₀, hsm⟩, rfl⟩
  have hI := fun (v v' : GlobalTheory.SmVec.smSub Hm σ) => GlobalTheory.T.complexifiedDerivedAction_isLieAction n Hm H σ hh hd hσ v.1 v'.1 v.2 v'.2
  have hc : ∀ Z (v : GlobalTheory.SmVec.smSub Hm σ), (dEnd hh hd hσ Z v : H) = dRepC Hm σ Z v :=
    fun Z v => dEnd_coe hh hd hσ Z v
  have hcomm : ∀ Z Z', dEnd hh hd hσ (Z * Z' - Z' * Z) =
      dEnd hh hd hσ Z * dEnd hh hd hσ Z' - dEnd hh hd hσ Z' * dEnd hh hd hσ Z := by
    intro Z Z'
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hc]
    exact ((hI v v).1 1 Z Z').2.2
  have hxinv : x₀⁻¹ * x₀ = 1 := Matrix.nonsing_inv_mul x₀ hdx.isUnit
  have hxinv' : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv x₀ hdx.isUnit
  have hgl := glRel_opM (dEnd hh hd hσ) hcomm hxinv
  have hEv : ∀ a c, (opM (dEnd hh hd hσ) x₀ x₀⁻¹ a c v₀s : H) =
      dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v₀s := by
    intro a c; simp only [opM, Matrix.of_apply, hc]
  have hup : ∀ a c, a < c → opM (dEnd hh hd hσ) x₀ x₀⁻¹ a c v₀s = 0 := by
    intro a c hac
    apply Subtype.ext
    rw [hEv, hw a c hac.le, if_neg hac.ne, Submodule.coe_zero]
  have hdiag : ∀ a, opM (dEnd hh hd hσ) x₀ x₀⁻¹ a a v₀s = ((w a : ℂ)) • v₀s := by
    intro a
    apply Subtype.ext
    rw [hEv, hw a a le_rfl, if_pos rfl, Submodule.coe_smul]
  have htr := GlobalTheory.Mem.GelfCheck.trace_pow_apply (μ := fun a => (w a : ℂ)) hgl hdiag hup (k + 1)
  rw [trace_opM_pow _ hxinv'] at htr
  set c := GlobalTheory.Mem.Gelf.gelfC (fun a => (w a : ℂ)) (k + 1) with hcdef
  have hTv₀ : ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace v₀s : H) = c • (v₀s : H) := by
    rw [htr, Submodule.coe_smul]
  have hadj : ∀ u u' : GlobalTheory.SmVec.smSub Hm σ,
      ⟪((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace u : H), (u' : H)⟫_ℂ =
        ⟪(u : H), ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace u' : H)⟫_ℂ := by
    have hF : ∀ a b (v v' : GlobalTheory.SmVec.smSub Hm σ), ⟪(opM (dEnd hh hd hσ) 1 1 a b v : H), (v' : H)⟫_ℂ =
        ⟪(v : H), (opM (dEnd hh hd hσ) Hm⁻¹ Hm b a v' : H)⟫_ℂ := by
      intro a b v v'
      have hst : (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
        ext i j
        simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
        by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
      have hcj : conjH Hm (Matrix.single a b 1) = (-1 : ℂ) • (Hm⁻¹ * Matrix.single b a 1 * Hm) := by
        rw [conjH, hst, neg_one_smul]
      simp only [opM, Matrix.of_apply, one_mul, mul_one]
      rw [hc, (hI v v').2.2.2, ← hc, hcj, map_smul, LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right]
      ring
    intro u u'
    conv_rhs => rw [← trace_opM_pow (dEnd hh hd hσ) (Matrix.nonsing_inv_mul Hm hd.isUnit) (k + 1)]
    simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, Submodule.coe_sum, sum_inner, inner_sum]
    exact Finset.sum_congr rfl fun a _ => pow_adjoint hF (k + 1) a a u u'
  have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ (u : GlobalTheory.SmVec.smSub Hm σ) (hu : σ g (u : H) ∈ GlobalTheory.SmVec.smSub Hm σ),
      σ g ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace u : H) =
        ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace ⟨σ g u, hu⟩ : H) := by
    intro g hg u hu
    have hgu : IsUnit g := GlobalTheory.SmVec.isUnit_of_mem_UH hHu hg
    have hmem : ∀ x ∈ GlobalTheory.SmVec.smSub Hm σ, (σ g : H →ₗ[ℂ] H) x ∈ GlobalTheory.SmVec.smSub Hm σ :=
      fun x hx => GlobalTheory.SmVec.rep_mem hHu hσ hx hg
    let Tg : Module.End ℂ (GlobalTheory.SmVec.smSub Hm σ) := (σ g : H →ₗ[ℂ] H).restrict hmem
    have hTg : ∀ v, (Tg v : H) = σ g (v : H) := fun v => rfl
    have hE : ∀ a b, Tg * opM (dEnd hh hd hσ) 1 1 a b = opM (dEnd hh hd hσ) g g⁻¹ a b * Tg := by
      intro a b
      refine LinearMap.ext fun v => Subtype.ext ?_
      simp only [Module.End.mul_apply, opM, Matrix.of_apply, one_mul, mul_one, hTg, hc]
      exact (hI v v).2.2.1 g hg (Matrix.single a b 1)
    have hT : Tg * (opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace =
        (opM (dEnd hh hd hσ) g g⁻¹ ^ (k + 1)).trace * Tg := by
      simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, pow_intertwine hE]
    rw [trace_opM_pow _ (Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).1 hgu))] at hT
    calc σ g ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace u : H)
        = ((Tg * (opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace) u : H) := rfl
      _ = (((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace * Tg) u : H) := by rw [hT]
      _ = ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace ⟨σ g u, hu⟩ : H) := rfl
  refine ⟨(starRingEnd ℂ) c, fun v hv => ?_⟩
  have hvs : v ∈ GlobalTheory.SmVec.smSub Hm σ := hv
  rw [← sub_eq_zero]
  apply eq_zero_of_inner_orbit hd hσ hi hv₀
  intro g hg
  have hgs : σ g (v₀s : H) ∈ GlobalTheory.SmVec.smSub Hm σ := GlobalTheory.SmVec.rep_mem hHu hσ v₀s.2 hg
  have e1 : gelfRep Hm σ k v = ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace ⟨v, hvs⟩ : H) :=
    gelfRep_eq hh hd hσ k ⟨v, hvs⟩
  have e2 : ⟪((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace ⟨v, hvs⟩ : H), σ g (v₀s : H)⟫_ℂ =
      ⟪v, ((opM (dEnd hh hd hσ) 1 1 ^ (k + 1)).trace ⟨σ g v₀s, hgs⟩ : H)⟫_ℂ :=
    hadj ⟨v, hvs⟩ ⟨σ g v₀s, hgs⟩
  have e3 := hint g hg v₀s hgs
  rw [inner_sub_left, e1, e2, ← e3, hTv₀, map_smul, inner_smul_right, inner_smul_left, Complex.conj_conj, sub_self]

end GlobalTheory.HolDict.GelfScalar

end
