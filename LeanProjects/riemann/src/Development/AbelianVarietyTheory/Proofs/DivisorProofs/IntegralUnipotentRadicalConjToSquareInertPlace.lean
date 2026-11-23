import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertConjSq

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def atV (v : Pl F) (x : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x)

theorem evFin_atV (v : Pl F) (x : Fv F v) : evFin F v (atV v x) = x := by
  show RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x v = x
  exact RestrictedProduct.single_eq_same _ _ _

theorem mul_atV (v : Pl F) (a : AF F) (x : Fv F v) : a * atV v x = atV v (evFin F v a * x) := by
  refine Prod.ext (mul_zero _) ?_
  have key : ∀ f : RestrictedProduct (fun w : Pl F => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite,
      f * RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x =
        RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v (f v * x) := by
    intro f
    apply RestrictedProduct.ext
    intro w
    rw [RestrictedProduct.mul_apply]
    by_cases h : w = v
    · subst h; simp [RestrictedProduct.single_eq_same]
    · simp [RestrictedProduct.single_eq_of_ne _ _ h]
  exact key a.2

theorem atV_add (v : Pl F) (x y : Fv F v) : atV v (x + y) = atV v x + atV v y :=
  Prod.ext (add_zero _).symm (RestrictedProduct.single_add _ _ _ _)

theorem atV_sub (v : Pl F) (x y : Fv F v) : atV v (x - y) = atV v x - atV v y :=
  Prod.ext (sub_zero _).symm (RestrictedProduct.single_sub _ _ _ _)

theorem atV_zero (v : Pl F) : atV v 0 = 0 :=
  Prod.ext rfl (RestrictedProduct.single_zero _ _)

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem scalar_ids (σ : E →ₐ[F] E) (X Y e h bq cq : AF F) (A : AE F E)
    (he : e * e = e) (hX : e * X = X) (hY : e * Y = Y) (hN : X * X - bq * X * Y + cq * Y * Y = h * e)
    (h2 : 2 * h = 1) (hA : A * A + algebraMap (AF F) (AE F E) bq * A + algebraMap (AF F) (AE F E) cq = 0)
    (hcA : cA σ A = -algebraMap (AF F) (AE F E) bq - A) :
    let ι := algebraMap (AF F) (AE F E)
    let Z := ι X + ι Y * A
    let α := 1 - ι e + 3 * ι h * Z
    let β := -(ι h * Z)
    α * cA σ α - β * cA σ β = 1 ∧ α * cA σ β = β * cA σ α ∧ (α - β) - 2 * (α + β) = ι e - 1 := by
  intro ι Z α β
  have cι : ∀ r, cA σ (ι r) = ι r := fun r => (cA σ).commutes r
  have hZ' : cA σ Z = ι X + ι Y * (-ι bq - A) := by
    simp only [Z, map_add, map_mul, cι, hcA]; rfl
  set Z' := cA σ Z with hZ'def
  have hα : cA σ α = 1 - ι e + 3 * ι h * Z' := by
    simp only [α, map_add, map_sub, map_mul, map_one, map_ofNat, cι, Z']
  have hβ : cA σ β = -(ι h * Z') := by
    simp only [β, map_neg, map_mul, cι, Z']
  have hE : ι e * ι e = ι e := by rw [← map_mul, he]
  have hEZ : ι e * Z = Z := by
    simp only [Z]; rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, hX, hY]
  have hEZ' : ι e * Z' = Z' := by
    rw [hZ']; rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, hX, hY]
  have hN' : Z * Z' = ι h * ι e := by
    rw [hZ']
    have := congrArg ι hN
    simp only [map_add, map_sub, map_mul] at this
    simp only [Z]
    linear_combination this - ι Y * ι Y * hA
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι h2
    rw [map_mul, map_ofNat, map_one] at this; exact this
  rw [hα, hβ]
  refine ⟨?_, ?_, ?_⟩
  · simp only [α, β]
    linear_combination hE - 3 * ι h * hEZ - 3 * ι h * hEZ' + 8 * ι h ^ 2 * hN' + ι e * (4 * ι h ^ 2 + 2 * ι h + 1) * h2'
  · simp only [α, β]
    linear_combination ι h * hEZ' - ι h * hEZ
  · simp only [α, β]
    ring

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def blk (d : ℕ) (x y : AE F E) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  fromBlocks (x • 1) (y • 1) (y • 1) (x • 1)

theorem blk_mul (d : ℕ) (x y x' y' : AE F E) :
    blk d x y * blk d x' y' = blk d (x * x' + y * y') (x * y' + y * x') := by
  simp only [blk, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

theorem blk_one (d : ℕ) : blk d (F := F) (E := E) 1 0 = 1 := by
  simp [blk, fromBlocks_one]

theorem blk_transpose (d : ℕ) (x y : AE F E) : (blk d x y)ᵀ = blk d x y := by
  simp [blk, fromBlocks_transpose]

theorem smul_one_map (d : ℕ) (f : AE F E →ₐ[AF F] AE F E) (x : AE F E) :
    ((x • 1 : Matrix (Fin d) (Fin d) (AE F E))).map f = f x • 1 := by
  ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp

theorem blk_map (d : ℕ) (f : AE F E →ₐ[AF F] AE F E) (x y : AE F E) : (blk d x y).map f = blk d (f x) (f y) := by
  simp [blk, fromBlocks_map, smul_one_map]

theorem blk_unitary (d : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) (AE F E)) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α) :
    (blk d α β)ᵀ * dbl J * (blk d α β).map (cA σ) = dbl J := by
  rw [blk_transpose, blk_map, dbl, blk, blk, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, smul_smul, smul_neg]
  congr 1
  all_goals
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Matrix.zero_apply]
    first
      | linear_combination (J i j) * h1
      | linear_combination (J i j) * h2
      | linear_combination -(J i j) * h2
      | linear_combination -(J i j) * h1

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem blk_mul_fromRows (d : ℕ) (x y : AE F E) (X Y : Matrix (Fin d) (Fin d) (AE F E)) :
    blk d x y * fromRows X Y = fromRows (x • X + y • Y) (y • X + x • Y) := by
  ext (i | i) j <;> simp [blk, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem blk_diag (d : ℕ) (x y : AE F E) :
    blk d x y * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((x + y) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  rw [diagCols, blk_mul_fromRows]
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, add_smul, add_comm]

theorem blk_anti (d : ℕ) (x y : AE F E) :
    blk d x y * (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((x - y) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  rw [antiCols, blk_mul_fromRows]
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, sub_smul] <;> ring

theorem cols_ext (d : ℕ) (X Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (h1 : X * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      Y * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)))
    (h2 : X * (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = Y * antiCols (F := F) (E := E) d) : X = Y := by
  set c : AE F E := algebraMap (AF F) (AE F E) (⅟(2 : AF F))
  have hc : c + c = 1 := by
    simp only [c]; rw [← map_add, invOf_two_add_invOf_two, map_one]
  have hP : fromCols (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) (antiCols (F := F) (E := E) d) *
      (c • fromBlocks 1 1 1 (-1)) = 1 := by
    rw [diagCols, antiCols, fromCols_fromRows_eq_fromBlocks, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul,
      ← fromBlocks_one]
    simp [← add_smul, hc]
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)
  set K : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := antiCols (F := F) (E := E) d
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := c • fromBlocks 1 1 1 (-1)
  have eX : X = fromCols (X * D) (X * K) * Q := by
    rw [← Matrix.mul_fromCols, Matrix.mul_assoc, hP, Matrix.mul_one]
  have eY : Y = fromCols (Y * D) (Y * K) * Q := by
    rw [← Matrix.mul_fromCols, Matrix.mul_assoc, hP, Matrix.mul_one]
  rw [eX, h1, h2]
  exact eY.symm

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mkS (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (α β : AE F E) (h1 : α * cA σ α - β * cA σ β = 1)
    (h2 : α * cA σ β = β * cA σ α) : UD σ W :=
  ⟨⟨blk d α β, blk d (cA σ α) (-cA σ β),
    by rw [blk_mul, ← blk_one d]; congr 1 <;> first | linear_combination h1 | linear_combination -h2 | linear_combination h2,
    by rw [blk_mul, ← blk_one d]; congr 1 <;> first | linear_combination h1 | linear_combination -h2 | linear_combination h2⟩,
    blk_unitary d σ (incM F W.J) α β h1 h2⟩

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem antiCols_transpose_mul (d : ℕ) :
    (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ * antiCols (F := F) (E := E) d = (1 : Matrix (Fin d) (Fin d) (AE F E)) + 1 := by
  simp [antiCols, transpose_fromRows, fromCols_mul_fromRows]

theorem at_b {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} (n : UD σ W) (hK : At (evFin F v) (matD n - 1))
    (b : Matrix (Fin d) (Fin d) (AE F E))
    (hb : matD n * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = diagCols (Fin d) + antiCols (F := F) (E := E) d * b) :
    At (evFin F v) b := by
  intro u hu
  have h0 : u • (matD n - 1) = 0 := hK u hu
  have e : b + b = (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ *
      ((matD n - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))) := by
    rw [Matrix.sub_mul, hb, Matrix.one_mul, add_sub_cancel_left, ← Matrix.mul_assoc, antiCols_transpose_mul,
      Matrix.add_mul, Matrix.one_mul]
  have e2 : u • (b + b) = 0 := by
    rw [e, ← Matrix.mul_smul, ← Matrix.smul_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  set c : AE F E := algebraMap (AF F) (AE F E) (⅟(2 : AF F))
  have hc : c + c = 1 := by
    simp only [c]; rw [← map_add, invOf_two_add_invOf_two, map_one]
  calc u • b = (c + c) • (u • b) := by rw [hc, one_smul]
    _ = c • (u • (b + b)) := by rw [add_smul, ← smul_add, ← smul_add]
    _ = 0 := by rw [e2, smul_zero]

theorem mkS_conj (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α) (n : UD σ W) (hn : n ∈ NabD σ W v)
    (hkey : ∀ b : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) b → (α - β) • b = (2 * (α + β)) • b) :
    mkS σ W α β h1 h2 * n * (mkS σ W α β h1 h2)⁻¹ = n * n := by
  obtain ⟨hK, hA, b, hb⟩ := hn
  set N := matD n
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)
  set K : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := antiCols (F := F) (E := E) d
  have hA' : N * K = K := hA
  have hb' : N * D = D + K * b := hb
  have hbAt := at_b n hK.1 b hb'
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext; apply Units.ext
  show blk d α β * N = N * N * blk d α β
  apply cols_ext
  · have eL : blk d α β * N * D = (α + β) • D + (2 * (α + β)) • (K * b) := by
      rw [Matrix.mul_assoc, hb', Matrix.mul_add, blk_diag, ← Matrix.mul_assoc, blk_anti, Matrix.mul_assoc,
        Matrix.smul_mul, Matrix.one_mul, hkey b hbAt, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    have eR : N * N * blk d α β * D = (α + β) • (D + K * b + K * b) := by
      rw [Matrix.mul_assoc, blk_diag, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc, hb',
        Matrix.mul_add, hb', ← Matrix.mul_assoc, hA']
    rw [eL, eR]
    simp only [smul_add, two_mul, add_smul]
    abel
  · rw [Matrix.mul_assoc, hA', Matrix.mul_assoc, blk_anti, ← Matrix.mul_assoc, Matrix.mul_assoc N N K, hA', hA']

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem blk_mulVec_inl (d : ℕ) (x y : AE F E) (z : Fin d ⊕ Fin d → AE F E) :
    (fun i => (blk d x y *ᵥ z) (Sum.inl i)) = x • (fun i => z (Sum.inl i)) + y • (fun i => z (Sum.inr i)) := by
  funext i; simp [blk, fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Function.comp_def]

theorem blk_mulVec_inr (d : ℕ) (x y : AE F E) (z : Fin d ⊕ Fin d → AE F E) :
    (fun i => (blk d x y *ᵥ z) (Sum.inr i)) = y • (fun i => z (Sum.inl i)) + x • (fun i => z (Sum.inr i)) := by
  funext i; simp [blk, fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Function.comp_def]

theorem blk_mulVec_mem {d : ℕ} {W : Spc F E d} {v : Pl F} (x y : AE F E)
    (hx : ∀ z ∈ GlobalTheory.InertSph.latAt W v, x • z ∈ GlobalTheory.InertSph.latAt W v)
    (hy : ∀ z ∈ GlobalTheory.InertSph.latAt W v, y • z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAtD W v, blk d x y *ᵥ z ∈ latAtD W v := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨?_, ?_⟩
  · rw [blk_mulVec_inl]; exact add_mem (hx _ h1) (hy _ h2)
  · rw [blk_mulVec_inr]; exact add_mem (hy _ h1) (hx _ h2)

theorem blk_sub_one (d : ℕ) (x y : AE F E) : blk d x y - 1 = blk d (x - 1) y := by
  ext (i | i) (j | j) <;> simp [blk, Matrix.one_apply] <;> split_ifs <;> simp

theorem smul_blk (d : ℕ) (u : AF F) (x y : AE F E) : u • blk d x y = blk d (u • x) (u • y) := by
  simp [blk, fromBlocks_smul, smul_assoc]

theorem mkS_mem_ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α)
    (hAt : ∀ u : AF F, evFin F v u = 0 → u • (α - 1) = 0 ∧ u • β = 0)
    (hL : ∀ r ∈ ({α, β, cA σ α, -cA σ β} : Set (AE F E)), ∀ z ∈ GlobalTheory.InertSph.latAt W v, r • z ∈ GlobalTheory.InertSph.latAt W v) :
    mkS σ W α β h1 h2 ∈ ParD σ W v := by
  refine ⟨⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · show u • (blk d α β - 1) = 0
    rw [blk_sub_one, smul_blk, (hAt u hu).1, (hAt u hu).2]
    simp [blk, fromBlocks_zero]
  · exact blk_mulVec_mem α β (hL α (by simp)) (hL β (by simp)) z hz
  · exact blk_mulVec_mem (cA σ α) (-cA σ β) (hL _ (by simp)) (hL _ (by simp)) z hz
  · refine ⟨⟨(α + β) • 1, (cA σ α - cA σ β) • 1, ?_, ?_⟩, ?_⟩
    · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      convert one_smul (AE F E) (1 : Matrix (Fin d) (Fin d) (AE F E)) using 2
      linear_combination h1 - h2
    · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      convert one_smul (AE F E) (1 : Matrix (Fin d) (Fin d) (AE F E)) using 2
      linear_combination h1 - h2
    · exact blk_diag d α β

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_latAt {d : ℕ} {W : Spc F E d} {v : Pl F} (p q : AF F)
    (hp : evFin F v p ∈ v.adicCompletionIntegers F) (hq : evFin F v q ∈ v.adicCompletionIntegers F) (a₀ : 𝓞 E) :
    ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) • z ∈
        GlobalTheory.InertSph.latAt W v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    have gen : ∀ (r : AF F) (y' : Fin d → E), At (evFin F v) a → evFin F v r ∈ v.adicCompletionIntegers F →
        y' ∈ W.L → (r * a) • (fun i => inclR (F := F) (AF F) (y' i)) ∈ GlobalTheory.InertSph.latAt W v := by
      intro r y' ha hr hy'
      refine AddSubgroup.subset_closure ⟨r * a, fun u hu => ?_, ?_, y', hy', rfl⟩
      · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul]; exact mul_mem hr hai
    have e : (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) •
        (a • fun i => inclR (F := F) (AF F) (y i)) =
        (p * a) • (fun i => inclR (F := F) (AF F) (y i)) +
          (q * a) • (fun i => inclR (F := F) (AF F) ((a₀ • y) i)) := by
      funext i
      show (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) *
          (a • inclR (F := F) (AF F) (y i)) =
        (p * a) • inclR (F := F) (AF F) (y i) + (q * a) • inclR (F := F) (AF F) (a₀ • y i)
      rw [Algebra.smul_def (A := E), map_mul]
      simp only [Algebra.smul_def, map_mul]
      have : inclR (F := F) (AF F) (algebraMap (𝓞 E) E a₀) = inclR (F := F) (AF F) (a₀ : E) := rfl
      rw [this]
      ring
    rw [e]
    exact add_mem (gen p y ha hp hy) (gen q _ ha hq (W.L.smul_mem a₀ hy))
  | zero => rw [smul_zero]; exact zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg z _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl IsDedekindDomain.HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_evFin_half (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (evFin F v (⅟(2 : AF F))) = 1 := by
  have e2 : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2 : v.adicCompletionIntegers F) : Fv F v) = 2 := by
    rw [GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers]
    first | (push_cast; exact map_ofNat _ 2) | (norm_num) | (exact_mod_cast map_ofNat (algebraMap F (Fv F v)) 2) | (simp [map_ofNat])
  have hle : Valued.v (2 : Fv F v) ≤ 1 := by
    rw [← e2]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2).2
  have hnlt : ¬ Valued.v (2 : Fv F v) < 1 := by
    rw [← e2, ← GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one, GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff]
    exact h2
  have hv2 : Valued.v (2 : Fv F v) = 1 := le_antisymm hle (not_lt.mp hnlt)
  have hm : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have := congrArg Valued.v hm
  rwa [map_mul, hv2, mul_one, map_one] at this

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl IsDedekindDomain.HeightOneSpectrum

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem conj_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  intro F E _ _ _ _ _ σ B hB d W v w hvw n hn
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hB.cm v hp
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  have hU : Valued.v (evFin F v (⅟(2 : AF F))) = 1 := valued_evFin_half v h2
  obtain ⟨x, y, hxy⟩ := GlobalTheory.InertUnitNorm.exists_int_sol v b c h2 hroot ⟨_, hU.le⟩ hU
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y + algebraMap F (Fv F v) (c : F) * y ^ 2 =
      evFin F v (⅟(2 : AF F)) := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers] at this
    exact this
  have hev : ∀ t : F, evFin F v (algebraMap F (AF F) t) = algebraMap F (Fv F v) t := fun t => (evFin F v).commutes t
  have he : atV v 1 * atV v 1 = atV v 1 := by rw [mul_atV, evFin_atV, mul_one]
  have hX : atV v 1 * atV v (x : Fv F v) = atV v (x : Fv F v) := by rw [mul_atV, evFin_atV, one_mul]
  have hY : atV v 1 * atV v (y : Fv F v) = atV v (y : Fv F v) := by rw [mul_atV, evFin_atV, one_mul]
  have hN : atV v (x : Fv F v) * atV v (x : Fv F v) - algebraMap F (AF F) (b : F) * atV v (x : Fv F v) * atV v (y : Fv F v) +
      algebraMap F (AF F) (c : F) * atV v (y : Fv F v) * atV v (y : Fv F v) = ⅟(2 : AF F) * atV v 1 := by
    simp only [mul_assoc, mul_atV, evFin_atV, hev]
    rw [← atV_sub, ← atV_add, mul_one, ← hK]
    congr 1
    ring
  have h2' : (2 : AF F) * ⅟2 = 1 := mul_invOf_self 2
  have hιF : ∀ t : F, inclR (F := F) (AF F) (algebraMap F E t) =
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) t) := fun t => by
    show Algebra.TensorProduct.includeRight (algebraMap F E t) = _
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hA : inclR (F := F) (AF F) (a : E) * inclR (F := F) (AF F) (a : E) +
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) (b : F)) * inclR (F := F) (AF F) (a : E) +
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) (c : F)) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hq
    simp only [map_add, map_mul, map_pow, map_zero, hιF] at this
    linear_combination this
  have hcA : cA σ (inclR (F := F) (AF F) (a : E)) =
      -algebraMap (AF F) (AE F E) (algebraMap F (AF F) (b : F)) - inclR (F := F) (AF F) (a : E) := by
    have e1 : cA σ (inclR (F := F) (AF F) (a : E)) = inclR (F := F) (AF F) (σ (a : E)) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] (a : E)) = (1 : AF F) ⊗ₜ[F] σ (a : E)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [e1, hconj, map_sub, map_neg, hιF]
  have R := scalar_ids σ (atV v (x : Fv F v)) (atV v (y : Fv F v)) (atV v 1) (⅟(2 : AF F))
    (algebraMap F (AF F) (b : F)) (algebraMap F (AF F) (c : F)) (inclR (F := F) (AF F) (a : E)) he hX hY hN
    (by rw [mul_comm]; exact invOf_mul_self 2) hA hcA
  obtain ⟨R1, R2, R3⟩ := R
  have hO3 : (3 : Fv F v) ∈ v.adicCompletionIntegers F := by
    have h1 : (1 : Fv F v) ∈ v.adicCompletionIntegers F := one_mem _
    have : (3 : Fv F v) = 1 + 1 + 1 := by norm_num
    rw [this]; exact add_mem (add_mem h1 h1) h1
  have hOU : evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := hU.le
  have hOx : (x : Fv F v) ∈ v.adicCompletionIntegers F := x.2
  have hOy : (y : Fv F v) ∈ v.adicCompletionIntegers F := y.2
  have hOb : algebraMap F (Fv F v) (b : F) ∈ v.adicCompletionIntegers F := by
    rw [← GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) b).2
  have key : ∀ p q : AF F, evFin F v p ∈ v.adicCompletionIntegers F → evFin F v q ∈ v.adicCompletionIntegers F →
      ∀ r, r = algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a : E) →
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, r • z ∈ GlobalTheory.InertSph.latAt W v := by
    rintro p q hp hq r rfl
    exact smul_latAt p q hp hq a
  refine ⟨mkS σ W _ _ R1 R2, mkS_mem_ParD σ W v _ _ R1 R2 ?_ ?_, mkS_conj σ W v _ _ R1 R2 n hn ?_⟩
  · intro u hu
    have hu0 : ∀ t, algebraMap (AF F) (AE F E) u * algebraMap (AF F) (AE F E) (atV v t) = 0 := fun t => by
      rw [← map_mul, mul_atV, hu, zero_mul, atV_zero, map_zero]
    refine ⟨?_, ?_⟩ <;> rw [Algebra.smul_def]
    · linear_combination -(hu0 1) + 3 * algebraMap (AF F) (AE F E) (⅟2) * hu0 (x : Fv F v) +
        3 * algebraMap (AF F) (AE F E) (⅟2) * inclR (F := F) (AF F) (a : E) * hu0 (y : Fv F v)
    · linear_combination -(algebraMap (AF F) (AE F E) (⅟2)) * hu0 (x : Fv F v) -
        algebraMap (AF F) (AE F E) (⅟2) * inclR (F := F) (AF F) (a : E) * hu0 (y : Fv F v)
  · intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine key (1 - atV v 1 + 3 * ⅟2 * atV v (x : Fv F v)) (3 * ⅟2 * atV v (y : Fv F v)) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat]; ring
    · refine key (-(⅟2 * atV v (x : Fv F v))) (-(⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat]; ring
    · refine key (1 - atV v 1 + 3 * ⅟2 * (atV v (x : Fv F v) - atV v (y : Fv F v) * algebraMap F (AF F) (b : F)))
        (-(3 * ⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, AlgHom.commutes, hcA]; ring
    · refine key (⅟2 * (atV v (x : Fv F v) - atV v (y : Fv F v) * algebraMap F (AF F) (b : F)))
        (-(⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, AlgHom.commutes, hcA]; ring
  · intro b' hb'
    rw [sub_eq_iff_eq_add.mp R3, add_smul]
    have : (algebraMap (AF F) (AE F E) (atV v 1) - 1) • b' = 0 := by
      rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, algebraMap_smul]
      exact hb' _ (by rw [map_sub, evFin_atV, map_one, sub_self])
    rw [this, zero_add]

end GlobalTheory.InertConjSq
end
