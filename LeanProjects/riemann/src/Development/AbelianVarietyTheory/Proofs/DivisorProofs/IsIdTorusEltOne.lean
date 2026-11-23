import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z

variable (F E) in

def archUnitF (c : ℝ) : (AF F)ˣ where
  val := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp c, fun _ => (Real.exp c : ℂ)), 1)
  inv := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp (-c), fun _ => (Real.exp (-c) : ℂ)), 1)
  val_inv := by
    refine Prod.ext ?_ (mul_one _)
    change _ * _ = (1 : InfiniteAdeleRing F)
    rw [← map_mul, ← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · simp [← Real.exp_add]
    · simp [← Complex.exp_add]
  inv_val := by
    refine Prod.ext ?_ (mul_one _)
    change _ * _ = (1 : InfiniteAdeleRing F)
    rw [← map_mul, ← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · simp [← Real.exp_add]
    · simp [← Complex.exp_add]

variable (F E) in

def archUnit (c : ℝ) : (AF F ⊗[F] E)ˣ := Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (archUnitF F c)

def torTrans (S : Finset (Fin r)) (φ : GAd σ J → ℂ) : Set (GAd σ J → ℂ) :=
  {f | ∃ l a, (∀ k ∉ S, l k = 1) ∧ IsIdTorusElt σ J X Y l a ∧ f = fun g => φ (a * g)}

theorem isIdTorusElt_one : IsIdTorusElt σ J X Y 1 1 := by
  refine ⟨?_, ?_, fun z _ => ?_⟩ <;> simp

@[simp] theorem archUnit_zero : archUnit F E 0 = 1 := by
  have : archUnitF F 0 = 1 := Units.ext (Prod.ext (by
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = 1
    rw [← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_) <;> simp) rfl)
  rw [archUnit, this, map_one]

end GlobalTheory.IdTorus
