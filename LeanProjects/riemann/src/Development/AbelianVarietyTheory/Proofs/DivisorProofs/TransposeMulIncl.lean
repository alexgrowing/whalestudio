import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.GLSlice

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

variable (R) in

def incl (f : Fin b ↪ Fin a) : Matrix (Fin a) (Fin b) R := Matrix.of fun i p => if f p = i then 1 else 0

theorem transpose_mul_incl (f : Fin b ↪ Fin a) : (incl R f)ᵀ * incl R f = 1 := by
  ext p q
  simp only [Matrix.mul_apply, incl, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f p)]
  · simp [eq_comm]
  · intro i _ hi
    rw [if_neg (Ne.symm hi), zero_mul]
  · simp

variable (R) in

def extN (f : Fin b ↪ Fin a) : Matrix (Fin b) (Fin b) R →ₙ+* Matrix (Fin a) (Fin a) R where
  toFun X := incl R f * X * (incl R f)ᵀ
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl R f)ᵀ, transpose_mul_incl, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem extN_apply (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) :
    extN R f X = incl R f * X * (incl R f)ᵀ := rfl

theorem extN_apply_apply (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) (p q : Fin b) :
    extN R f X (f p) (f q) = X p q := by
  simp [extN_apply, Matrix.mul_apply, incl]

theorem extN_apply_left (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) {i : Fin a} (hi : ∀ p, f p ≠ i)
    (j : Fin a) : extN R f X i j = 0 := by
  simp [extN_apply, Matrix.mul_apply, incl, hi]

theorem extN_apply_right (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) (i : Fin a) {j : Fin a}
    (hj : ∀ p, f p ≠ j) : extN R f X i j = 0 := by
  simp [extN_apply, Matrix.mul_apply, incl, hj]

theorem extN_single (f : Fin b ↪ Fin a) (p q : Fin b) (x : R) :
    extN R f (Matrix.single p q x) = Matrix.single (f p) (f q) x := by
  ext i j
  by_cases hi : ∃ p', f p' = i
  · obtain ⟨p', rfl⟩ := hi
    by_cases hj : ∃ q', f q' = j
    · obtain ⟨q', rfl⟩ := hj
      simp [extN_apply_apply, Matrix.single_apply]
    · push Not at hj
      rw [extN_apply_right f _ _ hj, Matrix.single_apply, if_neg fun h => hj q h.2]
  · push Not at hi
    rw [extN_apply_left f _ hi, Matrix.single_apply, if_neg fun h => hi p h.1]

theorem map_extN (f : Fin b ↪ Fin a) (φ : R →+* S) (X : Matrix (Fin b) (Fin b) R) :
    (extN R f X).map φ = extN S f (X.map φ) := by
  have h : (incl R f).map φ = incl S f := by
    ext i p; simp [incl, apply_ite φ]
  rw [extN_apply, extN_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, h]

def embGL (f : Fin b ↪ Fin a) : GL (Fin b) R →* GL (Fin a) R := Units.map (corner (extN R f))

theorem embGL_val (f : Fin b ↪ Fin a) (y : GL (Fin b) R) :
    (embGL f y : Matrix (Fin a) (Fin a) R) = 1 - extN R f 1 + extN R f y := rfl

theorem map_embGL (f : Fin b ↪ Fin a) (φ : R →+* S) (y : GL (Fin b) R) :
    GeneralLinearGroup.map φ (embGL f y) = embGL f (GeneralLinearGroup.map φ y) := by
  apply Units.ext
  change φ.mapMatrix (1 - extN R f 1 + extN R f y) = 1 - extN S f 1 + extN S f ((y : Matrix _ _ R).map φ)
  rw [map_add, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_extN, map_extN,
    Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem continuous_embGL [TopologicalSpace R] [IsTopologicalRing R] (f : Fin b ↪ Fin a) :
    Continuous (embGL f : GL (Fin b) R → GL (Fin a) R) :=
  Continuous.units_map _ (continuous_const.add ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
    Continuous fun X : Matrix (Fin b) (Fin b) R => incl R f * X * (incl R f)ᵀ))

theorem star_extN [StarRing R] (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) :
    star (extN R f X) = extN R f (star X) := by
  have h : (incl R f)ᴴ = (incl R f)ᵀ := by
    ext p i; simp [incl, apply_ite star]
  have h' : ((incl R f)ᵀ)ᴴ = incl R f := by rw [← h, Matrix.conjTranspose_conjTranspose]
  simp only [extN_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, h, h', Matrix.mul_assoc]

open GlobalTheory.LeviGA

def fstIx {r : ℕ} (h : r ≤ a) : Fin r ↪ Fin a := Function.Embedding.inl.trans (blkEquiv h).toEmbedding

def sndIx {r : ℕ} (h : r ≤ a) : Fin (a - r) ↪ Fin a := Function.Embedding.inr.trans (blkEquiv h).toEmbedding

theorem fstIx_apply {r : ℕ} (h : r ≤ a) (p : Fin r) : fstIx h p = blkEquiv h (Sum.inl p) := rfl

theorem sndIx_apply {r : ℕ} (h : r ≤ a) (p : Fin (a - r)) : sndIx h p = blkEquiv h (Sum.inr p) := rfl

theorem blkGL_fst {r : ℕ} (h : r ≤ a) (m : GL (Fin r) R) : blkGL h (m, 1) = embGL (fstIx h) m := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  have hn : ∀ (q : Fin (a - r)) p, fstIx h p ≠ blkEquiv h (Sum.inr q) := fun q p e => by
    simpa [fstIx_apply] using e
  rw [blkGL_apply, embGL_val, Matrix.add_apply, Matrix.sub_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [← fstIx_apply, extN_apply_apply]; simp [Matrix.one_apply]
  · simp only [extN_apply_right _ _ _ (hn j)]; simp [Matrix.one_apply]
  · simp only [extN_apply_left _ _ (hn i)]; simp [Matrix.one_apply]
  · simp only [extN_apply_left _ _ (hn i)]; simp [Matrix.one_apply]

theorem blkGL_snd {r : ℕ} (h : r ≤ a) (m : GL (Fin (a - r)) R) : blkGL h (1, m) = embGL (sndIx h) m := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  have hn : ∀ (q : Fin r) p, sndIx h p ≠ blkEquiv h (Sum.inl q) := fun q p e => by
    simpa [sndIx_apply] using e
  rw [blkGL_apply, embGL_val, Matrix.add_apply, Matrix.sub_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [extN_apply_left _ _ (hn i)]; simp [Matrix.one_apply]
  · simp only [extN_apply_left _ _ (hn i)]; simp [Matrix.one_apply]
  · simp only [extN_apply_right _ _ _ (hn j)]; simp [Matrix.one_apply]
  · simp only [← sndIx_apply, extN_apply_apply]; simp [Matrix.one_apply]

theorem blkGL_eq_fst {r : ℕ} (h : r ≤ a) (m₁ : GL (Fin r) R) (m₂ : GL (Fin (a - r)) R) :
    blkGL h (m₁, m₂) = blkGL h (1, m₂) * embGL (fstIx h) m₁ := by
  rw [← blkGL_fst, ← map_mul]; simp

theorem blkGL_eq_snd {r : ℕ} (h : r ≤ a) (m₁ : GL (Fin r) R) (m₂ : GL (Fin (a - r)) R) :
    blkGL h (m₁, m₂) = blkGL h (m₁, 1) * embGL (sndIx h) m₂ := by
  rw [← blkGL_snd, ← map_mul]; simp

theorem blkGL_mul_unip {r : ℕ} (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (y : BlockIx a r → R) :
    ∃ y' : BlockIx a r → R, blkGL h p * unip y = unip y' * blkGL h p := by
  let Z : Matrix (Fin a) (Fin a) R := (blkGL h p).val * nilM y * (blkGL h p⁻¹).val
  refine ⟨fun q => Z q.1.1 q.1.2, ?_⟩
  have hZ : nilM (fun q : BlockIx a r => Z q.1.1 q.1.2) = Z := by
    ext i j
    simp only [nilM, Matrix.of_apply]
    split_ifs with hij
    · rfl
    · symm
      simp only [Z, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases blkGL_block h p⁻¹ l j with h2 | h2
      · rw [Finset.sum_eq_zero, zero_mul]
        intro k _
        rcases blkGL_block h p i k with h1 | h1
        · simp only [nilM, Matrix.of_apply]
          rw [dif_neg (fun hh => hij (by omega)), mul_zero]
        · rw [h1, zero_mul]
      · rw [h2, mul_zero]
  apply Units.ext
  change (blkGL h p).val * (1 + nilM y) = (1 + nilM fun q : BlockIx a r => Z q.1.1 q.1.2) * (blkGL h p).val
  rw [hZ, mul_add, add_mul, mul_one, one_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one, mul_one]

end Ring

section Rel

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem rel_aeval_qdet (Γ : Submodule ℂ (M × N)) {n : ℕ} (A : Fin n → Fin n → Module.End ℂ M)
    (B : Fin n → Fin n → Module.End ℂ N) (h : ∀ i j, ∀ x ∈ Γ, (A i j x.1, B i j x.2) ∈ Γ) (u : ℂ)
    (P : Polynomial ℂ) : ∀ x ∈ Γ, (Polynomial.aeval (Formalism.REAL.qdet A u) P x.1,
      Polynomial.aeval (Formalism.REAL.qdet B u) P x.2) ∈ Γ := by
  let T : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {z | ∀ x ∈ Γ, (z.1 x.1, z.2 x.2) ∈ Γ}
      mul_mem' := fun hz hw x hx => hz _ (hw x hx)
      add_mem' := fun hz hw x hx => Γ.add_mem (hz x hx) (hw x hx)
      algebraMap_mem' := fun c x hx => Γ.smul_mem c hx }
  have h1 : Formalism.REAL.qdet (fun i j => (A i j, B i j)) u ∈ T := GlobalTheory.LeviHC.MidBlock.qdet_mem T h u
  have h2 : Polynomial.aeval (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P ∈ T :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h1) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  have e1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ M) (Module.End ℂ N))
    (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P
  have e2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ M) (Module.End ℂ N))
    (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P
  rw [map_qdet] at e1 e2
  intro x hx
  have h3 := h2 x hx
  change ((AlgHom.fst ℂ _ _ _ : Module.End ℂ M) x.1, (AlgHom.snd ℂ _ _ _ : Module.End ℂ N) x.2) ∈ Γ at h3
  rw [← e1, ← e2] at h3
  exact h3

end Rel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ} (f : Fin b ↪ Fin a)

theorem embGL_infGL (y : GL (Fin b) (Cinf E)) : embGL f (infGL E b y) = infGL E a (embGL f y) :=
  ga_ext (by simp [map_embGL]) (by simp [map_embGL])

theorem embGL_finGL (k : GL (Fin b) (Af E)) : embGL f (finGL E b k) = finGL E a (embGL f k) :=
  ga_ext (by simp [map_embGL]) (by simp [map_embGL])

omit [NumberField E] [IsTotallyComplex E] in

def embK (k : Kinf E b) : Kinf E a :=
  ⟨(embGL f (Unitary.toUnits k)).val, Matrix.mem_unitaryGroup_iff.2 (by
    have e : star (embGL f (Unitary.toUnits k)).val = (embGL f (Unitary.toUnits k)⁻¹).val := by
      rw [embGL_val, embGL_val, star_add, star_sub, star_extN, star_extN, star_one, star_one]; rfl
    rw [e, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])⟩

omit [NumberField E] [IsTotallyComplex E] in
theorem toUnits_embK (k : Kinf E b) : Unitary.toUnits (embK f k) = embGL f (Unitary.toUnits k) := Units.ext rfl

omit [IsTotallyComplex E] in
variable (E) in

def extL : Lie E b →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (extN (Cinf E) f (Matrix.of X))
      map_add' := fun X Y => map_add (extN (Cinf E) f) (Matrix.of X) (Matrix.of Y)
      map_smul' := fun c X => by
        change extN (Cinf E) f (c • Matrix.of X) = c • extN (Cinf E) f (Matrix.of X)
        rw [extN_apply, extN_apply, Matrix.mul_smul, Matrix.smul_mul] }

omit [IsTotallyComplex E] in
theorem toL_embGL (y : GL (Fin b) (Cinf E)) :
    toL (embGL f y).val = toL (1 - extN (Cinf E) f 1) + extL E f (toL y.val) := rfl

omit [IsTotallyComplex E] in
theorem height_embGL : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin b) (Cinf E), height (embGL f y) ≤ B * height y := by
  refine ⟨1 + 2 * ‖toL (1 - extN (Cinf E) f 1)‖ + ‖extL E f‖, by positivity, fun y => ?_⟩
  unfold height
  rw [← map_inv, toL_embGL, toL_embGL]
  have h1 := (norm_add_le (toL (1 - extN (Cinf E) f 1)) _).trans (add_le_add_right ((extL E f).le_opNorm (toL y.val)) _)
  have h2 := (norm_add_le (toL (1 - extN (Cinf E) f 1)) _).trans
    (add_le_add_right ((extL E f).le_opNorm (toL (y⁻¹).val)) _)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (toL (1 - extN (Cinf E) f 1))
  have n4 := norm_nonneg (extL E f)
  nlinarith [mul_nonneg n1 n3, mul_nonneg n2 n3]

theorem chart_slice (ψ : GA E a → ℂ) (g : GA E a) (m : GA E b) {x : Lie E b} (hx : x ∈ invSet E b) :
    toL (1 - extN (Cinf E) f 1) + extL E f x ∈ invSet E a ∧
      chart (fun m => ψ (g * embGL f m)) m x = chart ψ (g * embGL f m) (toL (1 - extN (Cinf E) f 1) + extL E f x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [← toL_embGL, chart_val, chart_val, map_mul, embGL_infGL, mul_assoc]
  exact ⟨val_mem_invSet _, rfl⟩

def slice (g : GA E a) : Sm E a →ₗ[ℂ] Sm E b where
  toFun ψ := ⟨fun m => ψ.1 (g * embGL f m), fun m =>
    ((ψ.2 (g * embGL f m)).comp (contDiff_const.add (extL E f).contDiff).contDiffOn
      fun _ hx => (chart_slice f ψ.1 g m hx).1).congr fun _ hx => (chart_slice f ψ.1 g m hx).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem slice_apply (g : GA E a) (ψ : Sm E a) (m : GA E b) : (slice f g ψ).1 m = ψ.1 (g * embGL f m) := rfl

theorem lie_slice (g : GA E a) (ψ : Sm E a) (X : Lie E b) :
    lie E b X (slice f g ψ) = slice f g (lie E a (extL E f X) ψ) := by
  refine Subtype.ext (funext fun m => ?_)
  have e : chart (slice f g ψ).1 m =ᶠ[𝓝 (oneL E b)]
      chart ψ.1 (g * embGL f m) ∘ fun x => toL (1 - extN (Cinf E) f 1) + extL E f x :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_slice f ψ.1 g m hx).2
  have e1 : toL (1 - extN (Cinf E) f 1) + extL E f (oneL E b) = oneL E a := sub_add_cancel _ _
  have h1 : HasFDerivAt (chart ψ.1 (g * embGL f m)) (fderiv ℝ (chart ψ.1 (g * embGL f m)) (oneL E a))
      (toL (1 - extN (Cinf E) f 1) + extL E f (oneL E b)) := by
    rw [e1]; exact (differentiableAt_chart ψ.2 _).hasFDerivAt
  have h2 := h1.comp (oneL E b) ((extL E f).hasFDerivAt.const_add (toL (1 - extN (Cinf E) f 1)))
  change fderiv ℝ (chart (slice f g ψ).1 m) (oneL E b) X = _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

theorem Eop_slice (g : GA E a) (ψ : Sm E a) (τ : E →+* ℂ) (p q : Fin b) :
    Eop τ p q (slice f g ψ) = slice f g (Eop τ (f p) (f q) ψ) := by
  have e : ∀ x : Cinf E, extL E f (toL (Matrix.single p q x)) = toL (Matrix.single (f p) (f q) x) := fun x =>
    congrArg toL (extN_single f p q x)
  have h1 := lie_slice f g ψ (toL (Matrix.single p q (atEmb τ 1)))
  have h2 := lie_slice f g ψ (toL (Matrix.single p q (atEmb τ Complex.I)))
  rw [e] at h1 h2
  refine Subtype.ext (funext fun m => ?_)
  exact congrArg₂ (fun s t : ℂ => (1 / 2 : ℂ) * (s - Complex.I * t)) (congrFun (congrArg Subtype.val h1) m)
    (congrFun (congrArg Subtype.val h2) m)

theorem aeval_qdet_slice (g : GA E a) (ψ : Sm E a) (τ : E →+* ℂ) (u : ℂ) (P : Polynomial ℂ) :
    Polynomial.aeval (Formalism.REAL.qdet (Eop (a := b) τ) u) P (slice f g ψ) =
      slice f g (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin b => Eop (a := a) τ (f p) (f q)) u) P ψ) :=
  rel_aeval_qdet (LinearMap.graph (slice f g)) (fun p q => Eop τ (f p) (f q)) (Eop τ)
    (fun p q x hx => by
      have hx' : x.2 = slice f g x.1 := hx
      change Eop τ p q x.2 = _
      rw [hx', Eop_slice]) u P (ψ, slice f g ψ) rfl

theorem growth_slice (g : GA E a) (ψ : Sm E a)
    (h : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) :
    ∀ m, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(slice f g ψ).1 (m * infGL E b y)‖ ≤ C * height y ^ N := by
  intro m
  obtain ⟨C, N, hC⟩ := h (g * embGL f m)
  obtain ⟨B, -, hB⟩ := height_embGL (E := E) f
  refine ⟨|C| * B ^ N, N, fun y => ?_⟩
  rw [slice_apply, map_mul, embGL_infGL, ← mul_assoc]
  have h0 : 0 ≤ height (embGL f y) := zero_le_one.trans (one_le_height _)
  refine (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)).trans ?_)
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB y) N) (abs_nonneg C)

end GlobalTheory.GLSlice

end
