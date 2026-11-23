import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma vecMulVec_mul_transpose' {m k : Type} [Fintype k] {R : Type} [CommRing R] (p : m → R) (q : k → R)
    (M : Matrix k k R) : Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d ⊕ Fin d → AE F E} (hq : q ∈ GlobalTheory.DblVac.latD W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latDbl X W v := by
  refine ⟨?_, ?_⟩
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₁ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inl) := by
      ext i j; simp [Matrix.toCols₁, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.1
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₂ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inr) := by
      ext i j; simp [Matrix.toCols₂, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.2

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F)
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hM : ∀ q ∈ GlobalTheory.DblVac.latD W v, M *ᵥ q ∈ GlobalTheory.DblVac.latD W v) :
    ∀ γ ∈ latDbl X W v, γ * Mᵀ ∈ latDbl X W v := by

  let φ₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols γ 0 : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  let φ₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols 0 γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  have key : ∀ (φ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)),
      (∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ x ∈ X.L, ∀ y ∈ W.L,
        ∃ q ∈ GlobalTheory.DblVac.latD W v,
          φ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) →
      latAtV X W v ≤ (latDbl X W v).comap φ := by
    intro φ hφ
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    obtain ⟨q, hq, he⟩ := hφ a ha hai x hx y hy
    show φ _ ∈ latDbl X W v
    rw [he]; exact vecMulVec_mem_latDbl X W v hx hq
  have gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun a ha hai y hy =>
    AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
  have h₁ : latAtV X W v ≤ (latDbl X W v).comap φ₁ := by
    refine key φ₁ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim (a • fun i => inclR (F := F) (AF F) (y i)) 0, hM _ ?_, ?_⟩
    · exact ⟨by simpa using gen a ha hai y hy, by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₁, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  have h₂ : latAtV X W v ≤ (latDbl X W v).comap φ₂ := by
    refine key φ₂ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (y i)), hM _ ?_, ?_⟩
    · exact ⟨by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem, by simpa using gen a ha hai y hy⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₂, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  intro γ hγ
  have hsplit : γ * Mᵀ = φ₁ γ.toCols₁ + φ₂ γ.toCols₂ := by
    simp only [φ₁, φ₂, AddMonoidHom.mk'_apply]
    rw [← Matrix.add_mul]
    congr 1
    ext i (j | j) <;> simp [Matrix.toCols₁, Matrix.toCols₂]
  rw [hsplit]
  exact (latDbl X W v).add_mem (h₁ hγ.1) (h₂ hγ.2)

end GlobalTheory.DblVacStab

theorem GlobalTheory.DblVac.kD_stab_latDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  intro F E _ _ _ _ _ σ n d X W v g hg γ hγ
  exact ⟨GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).1) γ hγ,
    GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).2) γ hγ⟩
