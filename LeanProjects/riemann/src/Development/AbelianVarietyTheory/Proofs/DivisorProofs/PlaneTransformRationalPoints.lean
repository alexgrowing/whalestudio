import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

namespace GlobalTheory.ThK.PlaneCo.Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bA_repr_inclR (e : E) (i : Fin (Module.finrank F E)) :
    (bA F E).repr (inclR (F := F) (AF F) e) i = algebraMap F (AF F) ((bE F E).repr e i) := by
  simp [bA, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem bA'_repr_inclR (e : E) (i : Fin (Module.finrank F E)) :
    (bA' F E).repr (inclR (F := F) (AF F) e) i = algebraMap F (AF F) ((bE' F E).repr e i) := by
  simp [bA', inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem incM_mul' {l m k : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m k E) :
    incM F (A * B) = incM F A * incM F B := by
  simp only [incM]; exact Matrix.map_mul

theorem coefLin_incM {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (x : Matrix (Fin n) (Fin d) E) :
    coefLin H H' (incM F x) = incM F (planeCoef H * x * (planeCoef H')ᵀ) := by
  show incM F (planeCoef H) * incM F x * (incM F (planeCoef H'))ᵀ = _
  rw [incM_mul', incM_mul']; rfl

theorem cA_inclR' (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

theorem planeT_incM (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁) (x : Matrix (Fin n) (Fin d) E) :
    (∃ y z : Kc F E d₁ n₁ → F, (planeT σ X W H H' (incM F x)).1 = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) ∧
    ∃ x₁ : Matrix (Fin n₁) (Fin d₁) E, (planeT σ X W H H' (incM F x)).2 = incM F x₁ := by
  set M := planeCoef H * x * (planeCoef H')ᵀ with hM
  have hc := coefLin_incM (F := F) H H' x
  have hs : ∀ k, sI H H' (incM F x) k = inclR (F := F) (AF F) (M (posS k).1 (posS k).2) := by
    intro k; rw [sI, hc]; rfl
  have ht : ∀ k, tI H H' (incM F x) k = inclR (F := F) (AF F) (M (posT k).1 (posT k).2) := by
    intro k; rw [tI, hc]; rfl
  have hp : ∀ k, pairI σ X W H H' (incM F x) k = inclR (F := F) (AF F)
      (-∑ m, (planeGram σ X.J H (posS k).1 (posT m).1 * planeGram σ W.J H' (posS k).2 (posT m).2) *
        σ (M (posT m).1 (posT m).2)) := by
    intro k; simp only [pairI, ht, cA_inclR', map_neg, map_sum, map_mul]
  refine ⟨⟨fun k => (bE F E).repr (M (posS k.1).1 (posS k.1).2) k.2,
    fun k => (bE' F E).repr (-∑ m, (planeGram σ X.J H (posS k.1).1 (posT m).1 *
      planeGram σ W.J H' (posS k.1).2 (posT m).2) * σ (M (posT m).1 (posT m).2)) k.2, ?_⟩,
    ⟨M.submatrix Sum.inl Sum.inl, ?_⟩⟩
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show (bA F E).repr (sI H H' (incM F x) k.1) k.2 = _
      rw [hs, bA_repr_inclR]
    · show (bA' F E).repr (pairI σ X W H H' (incM F x) k.1) k.2 = _
      rw [hp, bA'_repr_inclR]
  · show (coefLin H H' (incM F x)).submatrix Sum.inl Sum.inl = _
    rw [hc]; rfl

end GlobalTheory.ThK.PlaneCo.Rat
