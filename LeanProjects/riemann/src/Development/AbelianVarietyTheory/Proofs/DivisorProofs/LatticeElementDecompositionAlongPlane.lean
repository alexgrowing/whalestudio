import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LatPlaneSplit

theorem incM_vecMulVec_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {m k : ℕ} (s : E) (x : Fin m → E) (y : Fin k → E) :
    incM F (Matrix.vecMulVec (s • x) y) = Matrix.vecMulVec (incV F x) (incV F (s • y)) := by
  ext i j
  simp only [incM, incV, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem smul_vecMulVec' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {m k : ℕ} (c : AF F) (x : Fin m → AE F E) (w : Fin k → AE F E) :
    c • Matrix.vecMulVec x w = Matrix.vecMulVec x (c • w) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_smul_comm]

theorem vecMulVec_add' {R : Type} [CommRing R] {m k : ℕ} (x : Fin m → R) (w w' : Fin k → R) :
    Matrix.vecMulVec x (w + w') = Matrix.vecMulVec x w + Matrix.vecMulVec x w' := by
  ext i j; simp [Matrix.vecMulVec_apply, mul_add]

theorem vecMulVec_neg' {R : Type} [CommRing R] {m k : ℕ} (x : Fin m → R) (w : Fin k → R) :
    Matrix.vecMulVec x (-w) = -Matrix.vecMulVec x w := by
  ext i j; simp [Matrix.vecMulVec_apply]

theorem vecMulVec_zero' {R : Type} [CommRing R] {m k : ℕ} (x : Fin m → R) :
    Matrix.vecMulVec x (0 : Fin k → R) = 0 := by
  ext i j; simp [Matrix.vecMulVec_apply]

theorem mulVec_vecMulVec' {R : Type} [CommRing R] {m k l : ℕ} (A : Matrix (Fin m) (Fin l) R) (u : Fin l → R)
    (y : Fin k → R) : Matrix.vecMulVec (A *ᵥ u) y = A * Matrix.vecMulVec u y := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, mul_assoc]

theorem latAtV_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ),
    H.IsAdapted σ B X X₁ j₀ j₁ → ∀ (v : Pl F), ∀ γ ∈ latAtV X W v,
      ∃ (a b : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)), z ∈ latAtV X₁ W v ∧
        Matrix.vecMulVec (incV F H.x) a ∈ latAtV X W v ∧ Matrix.vecMulVec (incV F H.y) b ∈ latAtV X W v ∧
        γ = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z + Matrix.vecMulVec (incV F H.y) b := by
  intro F E _ _ _ _ _ σ B n d n₁ X W X₁ H j₀ j₁ hH v γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem γ hγ =>
    obtain ⟨c, hc1, hc2, x, hx, y, hy, rfl⟩ := hγ
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split x hx
    refine ⟨c • incV F (s • y), c • incV F (t • y), c • incM F (Matrix.vecMulVec u y), ?_, ?_, ?_, ?_⟩
    · exact AddSubgroup.subset_closure ⟨c, hc1, hc2, u, hu, y, hy, rfl⟩
    · refine AddSubgroup.subset_closure ⟨c, hc1, hc2, s • H.x, hs, y, hy, ?_⟩
      rw [incM_vecMulVec_smul, smul_vecMulVec']
    · refine AddSubgroup.subset_closure ⟨c, hc1, hc2, t • H.y, ht, y, hy, ?_⟩
      rw [incM_vecMulVec_smul, smul_vecMulVec']
    · rw [Matrix.add_vecMulVec, Matrix.add_vecMulVec, mulVec_vecMulVec']
      have hm : incM F (H.ι * Matrix.vecMulVec u y) = incM F H.ι * incM F (Matrix.vecMulVec u y) := by
        simp only [incM]; exact Matrix.map_mul
      have hadd : ∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) E), incM F (A + B) = incM F A + incM F B := by
        intro p q A B; simp only [incM]; exact Matrix.map_add _ (map_add _) A B
      rw [hadd, hadd, hm, incM_vecMulVec_smul, incM_vecMulVec_smul, smul_add, smul_add, smul_vecMulVec', smul_vecMulVec', Matrix.mul_smul]
  | zero =>
    refine ⟨0, 0, 0, zero_mem _, ?_, ?_, ?_⟩
    · rw [vecMulVec_zero']; exact zero_mem _
    · rw [vecMulVec_zero']; exact zero_mem _
    · rw [vecMulVec_zero', vecMulVec_zero', Matrix.mul_zero]; simp
  | add γ γ' _ _ ih ih' =>
    obtain ⟨a, b, z, hz, ha, hb, rfl⟩ := ih
    obtain ⟨a', b', z', hz', ha', hb', rfl⟩ := ih'
    refine ⟨a + a', b + b', z + z', add_mem hz hz', ?_, ?_, ?_⟩
    · rw [vecMulVec_add']; exact add_mem ha ha'
    · rw [vecMulVec_add']; exact add_mem hb hb'
    · rw [vecMulVec_add', vecMulVec_add', Matrix.mul_add]; abel
  | neg γ _ ih =>
    obtain ⟨a, b, z, hz, ha, hb, rfl⟩ := ih
    refine ⟨-a, -b, -z, neg_mem hz, ?_, ?_, ?_⟩
    · rw [vecMulVec_neg']; exact neg_mem ha
    · rw [vecMulVec_neg']; exact neg_mem hb
    · rw [vecMulVec_neg', vecMulVec_neg', Matrix.mul_neg]; abel

end GlobalTheory.LatPlaneSplit

end
