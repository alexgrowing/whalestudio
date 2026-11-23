import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticSmooth

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem iteratedLineDerivOp_apply_apply {k : ℕ} (w : Fin k → E) (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    (∂^{w} u) φ = (-1 : ℂ) ^ k * u (∂^{w ∘ Fin.rev} φ) := by
  induction k generalizing u φ with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, TemperedDistribution.lineDerivOp_apply_apply, map_neg, ih,
      iteratedLineDerivOp_succ_right (w ∘ Fin.rev), pow_succ]
    have e1 : Fin.init (w ∘ Fin.rev) = Fin.tail w ∘ Fin.rev := by
      ext j; simp [Fin.init, Fin.tail, Fin.rev_castSucc]
    have e2 : (w ∘ Fin.rev) (Fin.last k) = w 0 := by simp
    rw [e1, e2]
    ring

theorem iteratedLineDerivOpCLM_congr {k k' : ℕ} (h : k = k') (w : Fin k' → E) :
    iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w ∘ Fin.cast h) = iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w := by
  subst h; rfl

theorem contDiff_mul_of_tsupport {Ω : Set E} (hΩ : IsOpen Ω) {a χ : E → ℂ}
    (ha : ContDiffOn ℝ ∞ a Ω) (hχ : ContDiff ℝ ∞ χ) (hχΩ : tsupport χ ⊆ Ω) :
    ContDiff ℝ ∞ (fun x ↦ χ x * a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact hχ.contDiffAt.mul (ha.contDiffAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h ↦ hx (hχΩ h)
    have hev : (fun y ↦ χ y * a y) =ᶠ[nhds x] fun _ ↦ (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      rw [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

def cutMul {Ω : Set E} (hΩ : IsOpen Ω) {a : E → ℂ} (ha : ContDiffOn ℝ ∞ a Ω) (χ : 𝓢(E, ℂ))
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x ↦ χ x * a x) (hχc.mul_right)
    (contDiff_mul_of_tsupport hΩ ha χ.smooth' hχΩ)

theorem cutMul_apply {Ω : Set E} (hΩ : IsOpen Ω) {a : E → ℂ} (ha : ContDiffOn ℝ ∞ a Ω)
    (χ : 𝓢(E, ℂ)) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) (x : E) :
    cutMul hΩ ha χ hχc hχΩ x = χ x * a x := rfl

end General

section MultiIndex

variable {n : ℕ}

def mabs (α : Fin n → ℕ) : ℕ := ∑ i, α i

def mdirList (α : Fin n → ℕ) : List (EuclideanSpace ℝ (Fin n)) :=
  (List.finRange n).flatMap fun i ↦ List.replicate (α i) (EuclideanSpace.single i 1)

theorem length_mdirList (α : Fin n → ℕ) : (mdirList α).length = mabs α := by
  simp [mdirList, List.length_flatMap, mabs, Fin.sum_univ_def]

def mdir (α : Fin n → ℕ) : Fin (mabs α) → EuclideanSpace ℝ (Fin n) :=
  fun j ↦ (mdirList α).get (Fin.cast (length_mdirList α).symm j)

def mpow (α : Fin n → ℕ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ := ∏ i, ξ i ^ α i

theorem prod_get_eq {M : Type*} [CommMonoid M] {X : Type*} (f : X → M) (L : List X) :
    ∏ k : Fin L.length, f (L.get k) = (L.map f).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    show ∏ k : Fin (L.length + 1), f ((x :: L).get k) = _
    rw [Fin.prod_univ_succ]
    rfl

theorem prod_flatMap_eq {M : Type*} [CommMonoid M] {X Y : Type*} (L : List X) (g : X → List Y)
    (f : Y → M) : ((L.flatMap g).map f).prod = (L.map fun x ↦ ((g x).map f).prod).prod := by
  induction L with
  | nil => simp
  | cons x L ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih]; simp

theorem prod_inner_mdir (α : Fin n → ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∏ j, inner ℝ ξ (mdir α j) = mpow α ξ := by
  have h1 : ∏ j, inner ℝ ξ (mdir α j) = ∏ k : Fin (mdirList α).length, inner ℝ ξ ((mdirList α).get k) :=
    Fintype.prod_equiv (finCongr (length_mdirList α).symm) _ _ fun j ↦ rfl
  rw [h1, prod_get_eq, mdirList, prod_flatMap_eq, mpow, Fin.prod_univ_def]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  rw [List.map_replicate, List.prod_replicate, EuclideanSpace.inner_single_right]
  simp

theorem prod_inner_mdir_rev (α : Fin n → ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∏ j, inner ℝ ξ ((mdir α ∘ Fin.rev) j) = mpow α ξ := by
  rw [← prod_inner_mdir]
  exact Fintype.prod_equiv Fin.revPerm _ _ fun j ↦ rfl

def pderiv (α : Fin n → ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  iteratedFDeriv ℝ (mabs α) f x (mdir α)

theorem iteratedLineDerivOp_mdir_apply (α : Fin n → ℕ) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) : (∂^{mdir α} φ) x = pderiv α φ x :=
  SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

end MultiIndex

section OpS

variable {n : ℕ}

def opS (A : Finset (Fin n → ℕ)) (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  ∑ α ∈ A, smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
    iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) (mdir α ∘ Fin.rev)

def opST (A : Finset (Fin n → ℕ)) (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  ∑ α ∈ A, ((-1 : ℂ) ^ mabs α) • (iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
    (mdir α ∘ Fin.rev) ∘L smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ))

theorem comp_rev_rev {X : Type*} {k : ℕ} (w : Fin k → X) : (w ∘ Fin.rev) ∘ Fin.rev = w := by
  ext j; simp

theorem opST_apply_apply (A : Finset (Fin n → ℕ)) (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    opST A b u φ = u (∑ α ∈ A,
      SchwartzMap.smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) (∂^{mdir α} φ)) := by
  simp only [opST, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    iteratedLineDerivOpCLM_apply, smulLeftCLM_apply_apply, iteratedLineDerivOp_apply_apply,
    comp_rev_rev, map_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end OpS

section Elliptic

variable {n : ℕ}

theorem hasOrder_smulLeft_iteratedLineDeriv (χ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) {m : ℝ} (hk : (k : ℝ) ≤ m) :
    HasOrder (smulLeftCLM ℂ (χ : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
      iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) w) m :=
  ((hasOrder_smulLeft χ).comp (hasOrder_iteratedLineDeriv w)).mono (by linarith)

theorem isLocal_smulLeft_iteratedLineDeriv (χ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    IsLocal (smulLeftCLM ℂ (χ : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
      iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) w) :=
  (isLocal_smulLeft χ.hasTemperateGrowth).comp (isLocal_iteratedLineDeriv w)

theorem exists_prinOp_eq {m : ℕ} (S : Finset (Fin n → ℕ)) (hS : ∀ α ∈ S, mabs α = m)
    (c : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (k : ℕ) (a' : Fin k → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (w' : Fin k → Fin m → EuclideanSpace ℝ (Fin n)),
      prinOp a' w' = ∑ α ∈ S, smulLeftCLM ℂ (c α : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
        iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) (mdir α ∘ Fin.rev) ∧
      ∀ (y ξ : EuclideanSpace ℝ (Fin n)), prinSymb (fun i ↦ a' i y) w' ξ =
        ∑ α ∈ S, c α y * (mpow α ξ : ℂ) := by
  classical
  set e := S.equivFin
  have hm : ∀ i : Fin S.card, mabs (e.symm i).1 = m := fun i ↦ hS _ (e.symm i).2
  refine ⟨S.card, fun i ↦ c (e.symm i).1,
    fun i ↦ (mdir (e.symm i).1 ∘ Fin.rev) ∘ Fin.cast (hm i).symm, ?_, fun y ξ ↦ ?_⟩
  · rw [prinOp]
    simp_rw [iteratedLineDerivOpCLM_congr]
    rw [← Finset.sum_coe_sort S]
    exact e.symm.sum_comp (fun x : S ↦ smulLeftCLM ℂ (c x.1 : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
      iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) (mdir x.1 ∘ Fin.rev))
  · rw [prinSymb, ← Finset.sum_coe_sort S]
    refine (e.symm.sum_comp (fun x : S ↦ c x.1 y * (mpow x.1 ξ : ℂ))).symm ▸ ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [← prod_inner_mdir_rev, Complex.ofReal_prod]
    exact (Fintype.prod_equiv (finCongr (hm i).symm) _ _ fun j ↦ rfl)

theorem isEllipticAt_opS {m : ℕ} (A : Finset (Fin n → ℕ))
    (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hA : ∀ α ∈ A, mabs α ≤ m)
    (y : EuclideanSpace ℝ (Fin n))
    (hsymb : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 →
      ∑ α ∈ A with mabs α = m, b α y * (mpow α ξ : ℂ) ≠ 0) :
    IsEllipticAt (opS A b) m y := by
  classical
  obtain ⟨k, a', w', hP, hσ⟩ := exists_prinOp_eq (m := m) (A.filter fun α ↦ mabs α = m)
    (fun α hα ↦ (Finset.mem_filter.1 hα).2) b
  refine ⟨k, a', w', ∑ α ∈ A with ¬ mabs α = m, smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) ∘L
    iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) (mdir α ∘ Fin.rev), ?_, ?_, ?_, ?_⟩
  · rw [hP, opS, Finset.sum_filter_add_sum_filter_not]
  · refine HasOrder.sum _ fun α hα ↦ hasOrder_smulLeft_iteratedLineDeriv _ _ ?_
    obtain ⟨hαA, hne⟩ := Finset.mem_filter.1 hα
    have : mabs α + 1 ≤ m := by have := hA α hαA; omega
    have : ((mabs α + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast this
    push_cast at this; linarith
  · exact IsLocal.sum _ fun α _ ↦ isLocal_smulLeft_iteratedLineDeriv _ _
  · intro ξ hξ; rw [hσ]; exact hsymb ξ hξ

end Elliptic

section EllipticT

variable {n : ℕ}

theorem isLocal_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} (hT : IsLocal T)
    (ψ : 𝓢(E, ℂ)) : IsLocal (comm T ψ) :=
  (hT.comp (isLocal_smulLeft ψ.hasTemperateGrowth)).sub
    ((isLocal_smulLeft ψ.hasTemperateGrowth).comp hT)

theorem isEllipticAt_opST {m : ℕ} (A : Finset (Fin n → ℕ))
    (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hA : ∀ α ∈ A, mabs α ≤ m)
    (y : EuclideanSpace ℝ (Fin n))
    (hsymb : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 →
      ∑ α ∈ A with mabs α = m, b α y * (mpow α ξ : ℂ) ≠ 0) :
    IsEllipticAt (opST A b) m y := by
  classical
  set b' : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := fun α ↦ ((-1 : ℂ) ^ mabs α) • b α
  have hS : IsEllipticAt (opS A b') m y := by
    refine isEllipticAt_opS A b' hA y fun ξ hξ ↦ ?_
    have e : ∑ α ∈ A with mabs α = m, b' α y * (mpow α ξ : ℂ) =
        (-1 : ℂ) ^ m * ∑ α ∈ A with mabs α = m, b α y * (mpow α ξ : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα ↦ ?_
      simp only [b', smul_apply, smul_eq_mul]
      rw [(Finset.mem_filter.1 hα).2]
      ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hsymb ξ hξ)
  have e : opST A b = opS A b' + ∑ α ∈ A, ((-1 : ℂ) ^ mabs α) •
      comm (iteratedLineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) (mdir α ∘ Fin.rev)) (b α) := by
    rw [opST, opS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    ext1 u
    simp only [b', add_apply, smul_apply, ContinuousLinearMap.comp_apply, comm_apply]
    rw [show (((-1 : ℂ) ^ mabs α • b α : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
        EuclideanSpace ℝ (Fin n) → ℂ) = (-1 : ℂ) ^ mabs α • (b α : EuclideanSpace ℝ (Fin n) → ℂ) from rfl,
      smulLeftCLM_smul (b α).hasTemperateGrowth, smul_apply]
    rw [← smul_add]
    congr 1
    abel
  rw [e]
  refine hS.add ?_ ?_
  · refine HasOrder.sum _ fun α hα ↦ ?_
    refine ((hasOrder_comm_iteratedLineDeriv _ (b α)).smul _).mono ?_
    have := hA α hα
    have : (mabs α : ℝ) ≤ m := by exact_mod_cast this
    linarith
  · exact IsLocal.sum _ fun α _ ↦ (isLocal_comm (isLocal_iteratedLineDeriv _) _).smul _

end EllipticT

section DiffOp

variable {n : ℕ}

def diffOp (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A, a α x * pderiv α f x

def diffOpT (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A, (-1 : ℂ) ^ mabs α * pderiv α (fun y ↦ a α y * φ y) x

def prinSymbol (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ) (m : ℕ)
    (x ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A with mabs α = m, a α x * (mpow α ξ : ℂ)

theorem exists_schwartz_coeff {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ∀ α ∈ A, ContDiffOn ℝ ∞ (a α) Ω) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, Metric.closedBall x₀ (2 * r) ⊆ Ω ∧ ∃ b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ α ∈ A, ∀ y ∈ Metric.closedBall x₀ r, b α y = a α y := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  have hr : 0 < ε / 4 := by positivity
  have hsub : Metric.closedBall x₀ (2 * (ε / 4)) ⊆ Ω := fun y hy ↦ hball (by
    rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith)
  have hχΩ : tsupport (bump x₀ hr : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ Ω :=
    (tsupport_bump x₀ hr).trans hsub
  have hχc : HasCompactSupport (bump x₀ hr : EuclideanSpace ℝ (Fin n) → ℂ) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x₀ _) (isClosed_tsupport _)
      (tsupport_bump x₀ hr)
  refine ⟨ε / 4, hr, hsub, fun α ↦ if h : α ∈ A then cutMul hΩ (ha α h) (bump x₀ hr) hχc hχΩ else 0,
    fun α hα y hy ↦ ?_⟩
  simp only [dif_pos hα]
  rw [cutMul_apply, bump_eq_one x₀ hr hy, one_mul]

theorem sum_smulLeft_apply_eq_diffOp (A : Finset (Fin n → ℕ))
    (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ)
    (b : (Fin n → ℕ) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    {x : EuclideanSpace ℝ (Fin n)} (hb : ∀ α ∈ A, b α x = a α x) :
    (∑ α ∈ A, SchwartzMap.smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) (∂^{mdir α} φ)) x =
      diffOp A a φ x := by
  rw [diffOp, sum_apply]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  rw [SchwartzMap.smulLeftCLM_apply_apply (b α).hasTemperateGrowth, smul_eq_mul,
    iteratedLineDerivOp_mdir_apply, hb α hα]

end DiffOp

end

end GroundTheory.Automorphic.Sobolev
