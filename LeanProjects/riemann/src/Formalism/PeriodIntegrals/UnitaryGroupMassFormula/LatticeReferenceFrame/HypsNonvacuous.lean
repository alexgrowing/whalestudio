import Mathlib
import Formalism.PeriodIntegrals.ScRefExists

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

theorem zmod_one_of_mem {c : I.E ⊗[I.F] Af I.F} (h : c ∈ IntAf I.F I.E) : ZMod' I 1 c := by
  unfold ZMod'
  exact ⟨c, h, by simp⟩

theorem mL_one : mL I 1 = I.Lf := by
  unfold mL
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, by simp⟩

theorem ite_mem_int {p : Prop} [Decidable p] (x : I.E ⊗[I.F] Af I.F) (hx : x ∈ IntAf I.F I.E) :
    (if p then x else 0) ∈ IntAf I.F I.E := by
  split_ifs
  · exact hx
  · exact zero_mem _

def frameOne (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) : RefData I 1 r k e f where
  e0 := fun _ => 0
  f0 := fun _ => 0
  z0 := 0
  bw := fun _ => 0
  bwd := fun _ => 0
  ew := 0
  vectorsInLattice := ⟨fun _ => ⟨zero_mem _, zero_mem _⟩, zero_mem _, fun _ => ⟨zero_mem _, zero_mem _⟩⟩
  basisApprox := by
    intro a
    constructor
    · obtain ⟨c, hc, hm⟩ := (he a).1
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
    · obtain ⟨c, hc, hm⟩ := (he a).2
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
  gramIntegral := by
    intro a b
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left, zero_sub]; exact neg_mem (ite_mem_int I 1 (one_mem _))
  formsAtZero := by
    refine ⟨zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩
    · rw [hA_zero_left, zero_add]; exact one_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
  weightVectorsIntegral := by
    intro i
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_,
      zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩ <;>
      (rw [hA_zero_left]; exact zero_mem _)
  ew_idem := by simp
  ew_orth := by simp
  ew_int := zero_mem _
  ew_full := by
    intro y hy
    rw [map_zero, sub_zero, sub_zero, one_smul, mL_one]
    exact hy
  bw_w := fun _ => by simp
  bwd_w := fun _ => by simp
  bw_dual := by
    intro i j
    apply zmod_one_of_mem
    rw [hA_zero_left, zero_sub]
    exact neg_mem (ite_mem_int I 0 (zero_mem _))
  latticeSpan := by
    intro y hy
    apply Submodule.mem_sup_right
    rw [mL_one]
    exact hy

theorem refData_one (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) :
    Nonempty (RefData I 1 r k e f) := ⟨frameOne I r k e f he⟩

def TargetTwo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 2 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

theorem target_of_two (h : TargetTwo) : Target := by
  unfold TargetTwo at h
  unfold Target
  intro J g r k e f hg hs hn he hf hef hin
  rcases Nat.lt_or_ge g 2 with hlt | hge
  · obtain rfl : g = 1 := by omega
    exact refData_one J r k e f hin
  · exact h J g r k e f hge hs hn he hf hef hin

end PI.ScRefExists.UnitaryGroupMassFormula

end
