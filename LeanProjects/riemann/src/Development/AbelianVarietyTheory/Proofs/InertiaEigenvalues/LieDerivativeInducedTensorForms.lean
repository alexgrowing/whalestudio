import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.LieTensor

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

theorem exists_curve {a : ℕ} (Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL Z) 0 ∧
      (Z.conjTranspose = -Z → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • Z)).unit, Units.ext (by simp), ?_, fun hZ t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hZ, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem lie_skew_mem_span {N : ℕ} (ψ : Sm E N)
    (hψ : ψ ∈ finVec (cptRep E N)) (S : Matrix (Fin N) (Fin N) (Cinf E)) (hS : S.conjTranspose = -S) :
    lie E N (toL S) ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ) := by
  obtain ⟨c, h0, hc, hu⟩ := exists_curve S
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)
  have hf : FiniteDimensional ℂ W := hψ
  let W' : Submodule ℂ (GA E N → ℂ) := W.map (Sm E N).subtype
  have hcl : IsClosed (W' : Set (GA E N → ℂ)) := W'.closed_of_finiteDimensional
  let F : ℝ → GA E N → ℂ := fun t g => ψ.1 (g * infGL E N (c t))
  have hF : ∀ t, F t ∈ W' := fun t =>
    ⟨cptRep E N ⟨(c t).val, hu hS t⟩ ψ, Submodule.subset_span ⟨_, rfl⟩, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E N) = c t := Units.ext rfl
      change ψ.1 (g * infGL E N (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope F 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD (toL S) ψ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve ψ g c (toL S) h0 hc)
  have hm : lieD (toL S) ψ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hF t) (hF 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E N (toL S) ψ = w from Subtype.ext e.symm]

theorem map_leviEmb {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {c N : ℕ} {n : Fin c → ℕ}
    (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) R) :
    Matrix.GeneralLinearGroup.map p (leviEmb R e x) = leviEmb S e fun i => Matrix.GeneralLinearGroup.map p (x i) := by
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
  change p ((leviEmb R e x).val _ _) = _
  by_cases h : i = j
  · subst h
    rw [leviEmb_apply_same, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne _ _ _ h, leviEmb_apply_ne _ _ _ h, map_zero]

theorem infGL_leviEmb {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) e x) = leviEmb (Ad E) e fun i => infGL E (n i) (x i) := by
  refine ga_ext ?_ ?_
  · simp only [map_leviEmb, pInf_infGL]
  · simp only [map_leviEmb, pFin_infGL]
    exact (map_one (leviEmb (Af E) e)).symm

theorem exists_deriv_tensorForms {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i))
    (γ : ∀ i, ℝ → GL (Fin (n i)) (Cinf E)) (Z : ∀ i, Lie E (n i)) (h0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i, HasDerivAt (fun t => toL (γ i t).val) (Z i) 0) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ G ∈ tensorForms π, ∀ m, HasDerivAt (fun t => F fun i => m i * infGL E (n i) (γ i t)) (G m) 0 := by
  classical
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine ⟨∑ i, fun m => ∏ j, (Function.update φ i ⟨_, (π i).stable (.lie (Z i)) _ (φ i).2⟩ j).1.1 (m j),
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩, fun m => ?_⟩
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
      fun i _ => hasDerivAt_curve (φ i).1 (m i) (γ i) (Z i) (h0 i) (hγ i)
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), h0, map_one, mul_one]
  | zero => exact ⟨0, zero_mem _, fun m => hasDerivAt_const _ _⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨G, hG, h⟩ := hF
    obtain ⟨G', hG', h'⟩ := hF'
    exact ⟨G + G', add_mem hG hG', fun m => (h m).add (h' m)⟩
  | smul z F _ hF =>
    obtain ⟨G, hG, h⟩ := hF
    exact ⟨z • G, Submodule.smul_mem _ z hG, fun m => (h m).const_mul z⟩

theorem lie_block_tensor {c N : ℕ} (n : Fin c → ℕ)
    (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E)) :
    (fun m => (lie E N (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) ψ).1 (leviEmb (Ad E) e m))
      ∈ tensorForms π := by
  choose γ h0 hγ _ using fun i => exists_curve (Z i)
  obtain ⟨G, hG, h⟩ := exists_deriv_tensorForms π γ (fun i => toL (Z i)) h0 hγ hψ
  have hc : HasDerivAt (fun t => toL (leviEmb (Cinf E) e fun i => γ i t).val)
      (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
    change HasDerivAt (fun t => (leviEmb (Cinf E) e fun i => γ i t).val (e ⟨i, a⟩) (e ⟨j, b⟩))
      (Matrix.reindex e e (Matrix.blockDiagonal' Z) (e ⟨i, a⟩) (e ⟨j, b⟩)) 0
    by_cases hij : i = j
    · subst hij
      simp only [leviEmb_apply_same, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_eq]
      exact hasDerivAt_pi.1 (hasDerivAt_pi.1 (hγ i) a) b
    · simp only [leviEmb_apply_ne _ _ _ hij, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hij]
      exact hasDerivAt_const _ _
  convert hG using 1
  funext m
  have h1 := hasDerivAt_curve ψ (leviEmb (Ad E) e m) (fun t => leviEmb (Cinf E) e fun i => γ i t) _
    (by simp only [h0]; exact map_one _) hc
  refine h1.unique ?_
  simp only [infGL_leviEmb, ← map_mul]
  exact h m

omit [IsTotallyComplex E] in

theorem exists_decomp {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)
    (Y : Matrix (Fin N) (Fin N) (Cinf E)) :
    ∃ (S : Matrix (Fin N) (Fin N) (Cinf E)) (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E))
      (U : Matrix (Fin N) (Fin N) (Cinf E)),
      S.conjTranspose = -S ∧ (∀ p q, ¬ blk e p < blk e q → U p q = 0) ∧
      Y = S + Matrix.reindex e e (Matrix.blockDiagonal' Z) + U := by
  let L : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.of fun p q => if blk e q < blk e p then Y p q else 0
  let S := L - L.conjTranspose
  let Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E) := fun i => Matrix.of fun a b => (Y - S) (e ⟨i, a⟩) (e ⟨i, b⟩)
  refine ⟨S, Z, Y - S - Matrix.reindex e e (Matrix.blockDiagonal' Z), ?_, ?_, by abel⟩
  · simp only [S, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]
  · intro p q hpq
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective q
    simp only [blk_apply, not_lt] at hpq
    rcases hpq.lt_or_eq with h | h
    · have hij : i ≠ j := h.ne'
      simp [S, L, Z, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply, hij, h, not_lt_of_gt h]
    · subst h
      simp [Z, Matrix.blockDiagonal'_apply]

def LeviTensor {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (A : Matrix (Fin N) (Fin N) (Cinf E)) : Prop :=
  (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) ∈ tensorForms π

theorem leviTensor_zero {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) : LeviTensor e π ψ 0 := by
  have : (fun m => (lie E N (toL (0 : Matrix (Fin N) (Fin N) (Cinf E))) ψ).1 (leviEmb (Ad E) e m)) = 0 := by
    funext m
    rw [show toL (0 : Matrix (Fin N) (Fin N) (Cinf E)) = 0 from rfl, map_zero]
    rfl
  unfold LeviTensor
  rw [this]
  exact zero_mem _

theorem leviTensor_add {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {A B : Matrix (Fin N) (Fin N) (Cinf E)} (hA : LeviTensor e π ψ A) (hB : LeviTensor e π ψ B) :
    LeviTensor e π ψ (A + B) := by
  have : (fun m => (lie E N (toL (A + B)) ψ).1 (leviEmb (Ad E) e m)) =
      (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) + (fun m => (lie E N (toL B) ψ).1 (leviEmb (Ad E) e m)) := by
    funext m
    rw [show toL (A + B) = toL A + toL B from rfl, map_add]
    rfl
  unfold LeviTensor
  rw [this]
  exact add_mem hA hB

theorem leviTensor_sum {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) (Cinf E))
    (h : ∀ i ∈ s, LeviTensor e π ψ (A i)) : LeviTensor e π ψ (∑ i ∈ s, A i) :=
  Finset.sum_induction A (LeviTensor e π ψ) (fun _ _ => leviTensor_add) (leviTensor_zero e π ψ) h

theorem leviTensor_all {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) (h1 : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g)
    (h2 : ∀ w ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ),
      (fun m => w.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (h3 : ψ ∈ finVec (cptRep E N)) (Y : Matrix (Fin N) (Fin N) (Cinf E)) : LeviTensor e π ψ Y := by
  obtain ⟨S, Z, U, hS, hU, rfl⟩ := exists_decomp e Y
  refine leviTensor_add (leviTensor_add ?_ ?_) ?_
  · exact h2 _ (lie_skew_mem_span ψ h3 S hS)
  · exact lie_block_tensor n e π ψ (h2 ψ (Submodule.subset_span ⟨1, by simp⟩)) Z
  · rw [Matrix.matrix_eq_sum_single U]
    refine leviTensor_sum _ _ fun p _ => leviTensor_sum _ _ fun q _ => ?_
    by_cases hpq : blk e p < blk e q
    · have : (fun m => (lie E N (toL (Matrix.single p q (U p q))) ψ).1 (leviEmb (Ad E) e m)) = 0 :=
        funext fun m => GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E n e ψ h1 p q hpq (U p q) m
      unfold LeviTensor
      rw [this]
      exact zero_mem _
    · rw [hU p q hpq, Matrix.single_zero]
      exact leviTensor_zero e π ψ

theorem lie_tensorForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π →
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g)))
        ∈ tensorForms π := by
  intro E _ _ _ c N n h π X φ hφ k g
  have hφ' := fin_mem_indForms hφ g
  set ψ' : Sm E N := act (.fin g) φ with hψ'
  set y := Unitary.toUnits k with hy
  set ψ : Sm E N := rt E N (infGL E N y) ψ' with hψ
  have key : ∀ x, (lie E N X φ).1 (x * (infGL E N y * finGL E N g)) =
      (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 x := by
    intro x
    have h1 := congrArg (fun f : Module.End ℂ (Sm E N) => (f ψ').1 x) (GlobalTheory.CapAdInv.rt_lie (E := E) y (Matrix.of X))
    have h2 := congrArg (fun f : Module.End ℂ (Sm E N) => (f φ).1 (x * infGL E N y)) (lie_rt_fin (E := E) X g)
    simp only [Module.End.mul_apply, rt_apply] at h1 h2
    rw [← mul_assoc, ← h2]
    exact h1
  have hfun : (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N y * finGL E N g))) =
      fun m => (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) :=
    funext fun m => key _
  rw [hfun]
  have hψv : ∀ x, ψ.1 x = φ.1 (x * (infGL E N y * finGL E N g)) := fun x => by
    rw [← mul_assoc]; rfl
  refine leviTensor_all (stdBlocks n h) π ψ (fun u hu x => ?_) (fun w hw => ?_) ?_ _
  · rw [hψv, hψv, mul_assoc, hφ.1 u hu]
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k', rfl⟩ := hw
      have := hφ.2.2.2 (k' * k) g
      convert this using 2 with m
      change ψ.1 (_ * infGL E N (Unitary.toUnits k')) = _
      rw [hψv, map_mul, map_mul, mul_assoc, mul_assoc]
    | zero => exact zero_mem _
    | add w w' _ _ hw hw' => exact add_mem hw hw'
    | smul z w _ hw => exact Submodule.smul_mem _ z hw
  · have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ')) := hφ'.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ'))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨k' * k, ?_⟩
    show cptRep E N (k' * k) ψ' = cptRep E N k' ψ
    rw [map_mul]
    rfl

end GlobalTheory.LieTensor
