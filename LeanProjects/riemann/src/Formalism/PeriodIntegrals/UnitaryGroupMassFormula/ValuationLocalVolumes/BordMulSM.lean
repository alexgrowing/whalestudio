import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def sM {a : ℕ} (π : Fin a → Fin a) (z : Fin a) (g : Fv F v ⊗[F] E) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun k => Fin.snoc (α := fun _ => Fv F v ⊗[F] E)
      (fun j => if k = z ∨ j = z then 0 else if j = π k then 1 else 0) (if k = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) (-g))

theorem bord_mul_sM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (π : Fin a → Fin a)
    (hπ : Function.Involutive π) (z : Fin a) (hπz : π z = z) (g : Fv F v ⊗[F] E) (d : Fin a → Fv F v ⊗[F] E)
    (hd : ∀ i, i ≠ z → d i = 1) (hdz : d z = g) (hG : ∀ i k, G i k = if k = π i then d i else 0) :
    bordM v G z * sM v π z g = 1 := by
  have hπz' : ∀ i, π i = z ↔ i = z := fun i => ⟨fun h => by rw [← hπ i, h, hπz], fun h => h ▸ hπz⟩
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply] <;>
    simp only [bordM, sM, Fin.snoc_castSucc, Fin.snoc_last, hG]
  all_goals simp [hπz', hπ _, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne', Fin.castSucc_inj]
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs <;> first | rfl | (exfalso; tauto)
  · rcases eq_or_ne i z with rfl | hi
    · simp [hπz, hdz]
    · have : z ≠ π i := fun h => hi ((hπz' i).1 h.symm)
      simp [this, hi]
  · rw [Finset.sum_eq_single (π i) (fun x _ hx => by simp [hx]) (by simp)]
    simp only [hπ i, hπz', if_true]
    rcases eq_or_ne i z with rfl | hi
    · by_cases hj : j = i
      · simp [hj]
      · simp [hj, Ne.symm hj]
    · rcases eq_or_ne j z with rfl | hj
      · simp [hi]
      · simp [hi, hj, hd i hi, eq_comm]

end PI.OmVf
