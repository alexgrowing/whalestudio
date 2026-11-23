import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacRestr

section Extend

variable {α β : Type} {j : α → β}

theorem ext_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (g : M → N) (hg : g 0 = 0) (y : α → M) :
    (fun k => g (Function.extend j y 0 k)) = Function.extend j (fun i => g (y i)) 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, hg]

theorem ext_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (a b : α → M) :
    Function.extend j a 0 + Function.extend j b 0 = Function.extend j (a + b) 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem ext_dot [Fintype α] [Fintype β] {R : Type} [CommRing R] (hj : Function.Injective j) (a b : α → R) :
    Function.extend j a 0 ⬝ᵥ Function.extend j b 0 = a ⬝ᵥ b := by
  classical
  simp only [dotProduct]
  refine (Fintype.sum_of_injective j hj _ _ (fun k hk => ?_) (fun i => ?_)).symm
  · have h : ¬ ∃ x, j x = k := fun ⟨x, hx⟩ => hk ⟨x, hx⟩
    simp [Function.extend_apply' _ _ _ h]
  · simp [hj.extend_apply]

end Extend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incM (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i k
  simp [incM, cA, inclR, Matrix.map_apply]

theorem mul_mem_latAtV {n d n₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (ι : Matrix (Fin n) (Fin n₁) E)
    (hlow : ∀ u, u ∈ X₁.L ↔ ι *ᵥ u ∈ X.L) (v : Pl F) :
    ∀ z ∈ latAtV X₁ W v, incM F ι * z ∈ latAtV X W v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hv, ι *ᵥ x, (hlow x).1 hx, y, hy, ?_⟩
    rw [Matrix.mul_smul, incM, incM, ← Matrix.map_mul, Matrix.mul_vecMulVec]
    rfl
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.VacRestr

theorem GlobalTheory.VacRestr.restr_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W),
    H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
      Function.Injective j →
      (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
      ∀ (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (θ : 𝓞 E),
        (∀ γ ∈ latAtV X W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) φ =
          B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ) →
        ∀ z ∈ latAtV X₁ W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M₁.co v z) (fun y => φ (Function.extend j y 0)) =
          B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W.J) z z) •
            (fun y => φ (Function.extend j y 0)) := by
  intro F E _ _ _ _ _ σ B n d n₁ X W X₁ H j₀ j₁ M₁ hH j co hj hco v φ θ heig z hz
  have hγ := GlobalTheory.VacRestr.mul_mem_latAtV X W X₁ H.ι hH.low v z hz
  have hloc : GlobalTheory.LatVac.locCo co v (incM F H.ι * z) =
      (Function.extend j (GlobalTheory.LatVac.locCo M₁.co v z).1 0, Function.extend j (GlobalTheory.LatVac.locCo M₁.co v z).2 0) := by
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hco]
    exact Prod.ext (GlobalTheory.VacRestr.ext_map hj _ (map_zero _) _) (GlobalTheory.VacRestr.ext_map hj _ (map_zero _) _)
  have htw : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) (incM F H.ι * z) (incM F H.ι * z) =
      symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W.J) z z := by
    rw [GlobalTheory.symp_mul_left, GlobalTheory.VacRestr.cA_incM, ← hH.gram]
    congr 1
    simp only [incM]
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  funext y
  have h := congrFun (heig _ hγ) (Function.extend j y 0)
  rw [hloc, htw] at h
  simp only [schr, Pi.smul_apply, smul_eq_mul] at h ⊢
  rwa [GlobalTheory.VacRestr.ext_dot hj, GlobalTheory.VacRestr.ext_dot hj, GlobalTheory.VacRestr.ext_add hj] at h
