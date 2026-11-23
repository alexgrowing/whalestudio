import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def occCoef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)

def tensWord {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → (Fin n → M) → (Fin n → M)
  | [] => id
  | p :: w => fun f => tensF dual E p.1 p.2 (tensWord dual E w f)

section Ambient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem occA_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  exact tensor_group_mul_kDiag dual hσ hg hk f

theorem occA_coef_Eab (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (occCoef dual σ η (fun c => (f c : H))) g =
      occCoef dual σ η (fun c => (tensF dual E a b f c : H)) g := by
  exact tensor_coef_Eab_action dual hσ hD η f a b hg

theorem occA_coef_Eword (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (w : List (Fin n × Fin n)) (f : Fin n → D) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (occCoef dual σ η (fun c => (f c : H))) g =
      occCoef dual σ η (fun c => ((tensWord dual E w f c : D) : H)) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (occCoef dual σ η fun c => (f c : H))) g = _
    rw [Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => ih hx) hg]
    exact occA_coef_Eab dual hσ hD η (tensWord dual E w f) p.1 p.2 hg

theorem occA_coef_smooth (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (η f : Fin n → H)
    (hf : ∀ d, IsSmoothVecU ε σ (f d)) : Formalism.REAL.SmoothOnG ε (occCoef dual σ η f) := by
  exact tensor_coef_smooth dual η f hf

theorem occA_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      occCoef dual σ (fun c => (η c : H)) (fun c => (f c : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  exact tensor_coef_memLp dual hσ hW η f hη hf

theorem occA_tensWord_mem {V : Submodule ℂ D} (dual : Bool) (w : List (Fin n × Fin n)) :
    ∀ f ∈ tensSub (genSub E V), tensWord dual E w f ∈ tensSub (genSub E V) := by
  intro f hf
  induction w with
  | nil => exact hf
  | cons p w ih => exact tensSub_stable dual p.1 p.2 _ ih

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2
