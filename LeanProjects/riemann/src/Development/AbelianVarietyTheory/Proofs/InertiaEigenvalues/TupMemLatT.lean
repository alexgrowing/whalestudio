import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

def tup {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) : Fin m → Matrix (Fin a) (Fin a) (Om l) :=
  fun k => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))

def latL {m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (⋃ k, (fun x => Pi.single k ((l : Om l) ^ M • x)) '' (t k : Set (Matrix (Fin a) (Fin a) (Om l))))

def latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (Set.range (tup ρs)) ⊔ latL t M

def Carries (r : Γ →* GL (Fin a) (Om l)) {d d' m : ℕ} (b : Fin d → Matrix (Fin a) (Fin a) (Om l))
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ)
    (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (P : Matrix (Fin d) (Fin d') ℤ_[l]) (N : ℕ) : Prop :=
  ∀ (z : Fin d' → ℤ_[l]) (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M →
    ∑ s, zOm l (z s) • bb s = (F.sum fun g c => zOm l c • tup ρs g) + y →
    ∃ w : Fin d → ℤ_[l], ∑ i, zOm l ((P *ᵥ z) i) • b i =
      (F.sum fun g c => zOm l c • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) +
        (l : Om l) ^ N • ∑ i, zOm l (w i) • b i

theorem zOm_smul {α : Type} [AddCommGroup α] [Module (Om l) α] [Module ℤ_[l] α] [IsScalarTower ℤ_[l] (Om l) α]
    (c : ℤ_[l]) (x : α) : zOm l c • x = c • x := by
  rw [← algebraMap_smul (Om l) c x]
  congr 1

theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact (PadicAlgCl.norm_extends l (l : ℚ_[l])).trans Padic.norm_p

theorem norm_zOm_le (c : ℤ_[l]) : ‖zOm l c‖ ≤ 1 := by
  simp only [zOm, RingHom.comp_apply]
  exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one c)

theorem tup_mem_latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (g : Γ) : tup ρs g ∈ latT ρs t M :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨g, rfl⟩)

theorem traceL : ∀ (l : ℕ) [Fact l.Prime] (a d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), ∃ K : ℕ, ∀ w : Fin d → ℤ_[l], ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ (l : ℝ) ^ K := by
  intro l _ a d b
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ i, ‖(b i).trace‖) (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine ⟨K, fun w => ?_⟩
  rw [Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (le_trans ?_ hK.le)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le _)

end GlobalTheory.TraceConjugationCover

end
