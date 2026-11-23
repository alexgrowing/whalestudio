import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.CAConjBdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finEmb_compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (τ : E →ₐ[F] FvBar F v) (z : AE F E) :
    finEmb F v τ (compFin F E v (cA σ z)) = finEmb F v (τ.comp σ) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

def embComp (σ : E →ₐ[F] E) {w : InfinitePlace F} (τ : EmbOver E w) : EmbOver E w :=
  ⟨τ.1.comp (σ : E →+* E), by
    rw [RingHom.comp_assoc, show ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E from
      RingHom.ext fun x => σ.commutes x]; exact τ.2⟩

theorem infEmb_compInf_cA (σ : E →ₐ[F] E) (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E) :
    infEmb τ (compInf F E w (cA σ z)) = infEmb (embComp σ τ) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem cA_mem_bddA (σ : E →ₐ[F] E) {S : Finset (Pl F)} {c : ℝ≥0} {z : AE F E} (hz : z ∈ bddA E S c) :
    cA σ z ∈ bddA E S c := by
  refine ⟨fun v => ?_, fun w τ => ?_⟩
  · refine le_trans ((absFin_le_iff F v).2 fun τ => ?_) (hz.1 v)
    rw [finEmb_compFin_cA]
    exact le_absFin F v _ _
  · rw [infEmb_compInf_cA]
    exact hz.2 w (embComp σ τ)

theorem cA_mem_Bdd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ι : Type) (f : ι → AE F E), f ∈ Bdd F E ι → (fun t => cA σ (f t)) ∈ Bdd F E ι := by
  intro F E _ _ _ _ _ σ ι f ⟨S, c, h⟩
  exact ⟨S, c, fun t => cA_mem_bddA σ (h t)⟩

end GlobalTheory.CAConjBdd
