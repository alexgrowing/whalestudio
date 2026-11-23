import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LocFin

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}

def stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : Submodule ℂ V := S ⊔ ⨆ i, S.map (L i)

def fil (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) : Submodule ℂ V := (stp L)^[k] S₀

theorem fil_succ (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) :
    fil L S₀ (k + 1) = stp L (fil L S₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem le_stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : S ≤ stp L S := le_sup_left

theorem letter_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S) (i : ι) :
    L i u ∈ stp L S :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hu))

theorem span_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S)
    {C : Module.End ℂ V} (hC : C ∈ Submodule.span ℂ (Set.range L)) : C u ∈ stp L S := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact letter_mem_stp L hu i
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem fil_mono (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) : Monotone (fil L S₀) :=
  monotone_nat_of_le_succ fun k => by
    rw [fil_succ]
    exact le_stp L _

theorem fil_finite [Finite ι] (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) [h₀ : FiniteDimensional ℂ S₀] (k : ℕ) :
    FiniteDimensional ℂ (fil L S₀ k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    have : ∀ i, FiniteDimensional ℂ ((fil L S₀ k).map (L i)) := fun i => inferInstance
    have : FiniteDimensional ℂ ↥(⨆ i, (fil L S₀ k).map (L i) : Submodule ℂ V) := Submodule.finiteDimensional_iSup _
    exact Submodule.finiteDimensional_sup _ _

theorem stp_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S : Submodule ℂ V}
    (hS : ∀ w ∈ S, K w ∈ S) : ∀ w ∈ stp L S, K w ∈ stp L S := by
  have key : stp L S ≤ (stp L S).comap K := by
    refine sup_le (fun w hw => le_stp L S (hS w hw)) (iSup_le fun i => ?_)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : L i (K u) ∈ stp L S := letter_mem_stp L (hS u hu) i
    have h2 : (K * L i - L i * K) u ∈ stp L S := span_mem_stp L hu (hK i)
    have h3 : K (L i u) = (K * L i - L i * K) u + L i (K u) := by simp
    change K (L i u) ∈ stp L S
    rw [h3]
    exact add_mem h2 h1
  exact fun w hw => key hw

theorem fil_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S₀ : Submodule ℂ V}
    (h₀ : ∀ w ∈ S₀, K w ∈ S₀) (k : ℕ) : ∀ w ∈ fil L S₀ k, K w ∈ fil L S₀ k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    exact stp_stable L K hK ih

theorem mem_fil_of_adjoin (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) {T : Module.End ℂ V}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range L)) {f : V} (hf : f ∈ S₀) : ∃ k, T f ∈ fil L S₀ k := by
  have key : ∀ w, (∃ k, w ∈ fil L S₀ k) → ∃ k, T w ∈ fil L S₀ k := by
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rintro w ⟨k, hk⟩
      exact ⟨k + 1, by rw [fil_succ]; exact letter_mem_stp L hk i⟩
    | algebraMap r =>
      rintro w ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hk
    | add x y _ _ hx hy =>
      intro w hw
      obtain ⟨k, hk⟩ := hx w hw
      obtain ⟨m, hm⟩ := hy w hw
      refine ⟨max k m, ?_⟩
      simpa using add_mem (fil_mono L S₀ (le_max_left k m) hk) (fil_mono L S₀ (le_max_right k m) hm)
    | mul x y _ _ hx hy =>
      intro w hw
      simpa using hx (y w) (hy w hw)
  exact key f ⟨0, hf⟩

end Abstract

section Pair

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Bool × Fin n × Fin n → Module.End ℂ V
  | (true, a, b) => F1 a b
  | (false, a, b) => F2 a b

theorem range_letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) :
    Set.range (letters F1 F2) = {x | ∃ a b, x = F1 a b ∨ x = F2 a b} := by
  ext x
  constructor
  · rintro ⟨⟨_ | _, a, b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl rfl⟩
  · rintro ⟨a, b, rfl | rfl⟩
    · exact ⟨(true, a, b), rfl⟩
    · exact ⟨(false, a, b), rfl⟩

theorem gl_span (F1 F2 : Fin n → Fin n → Module.End ℂ V) (e : Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : ∀ a b, E a b = letters F1 F2 (e, a, b)) (a b c d : Fin n) :
    (if b = c then E a d else 0) - (if d = a then E c b else 0) ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  have hm : ∀ a b, E a b ∈ Submodule.span ℂ (Set.range (letters F1 F2)) := fun a b =>
    Submodule.subset_span ⟨(e, a, b), (hE a b).symm⟩
  refine sub_mem ?_ ?_
  · split_ifs
    · exact hm _ _
    · exact zero_mem _
  · split_ifs
    · exact hm _ _
    · exact zero_mem _

theorem comm_letters {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h1 : Formalism.REAL.GlRel F1) (h2 : Formalism.REAL.GlRel F2)
    (hc : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) (a b : Fin n) (i : Bool × Fin n × Fin n) :
    kF F1 F2 a b * letters F1 F2 i - letters F1 F2 i * kF F1 F2 a b ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  obtain ⟨_ | _, c, d⟩ := i
  · have h : kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b =
        (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) := by
      rw [← h2 a b c d]
      simp only [kF, add_mul, mul_add, hc a b c d]
      abel
    change kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 false F2 (fun _ _ => rfl) a b c d
  · have h : kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b =
        (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) := by
      rw [← h1 a b c d]
      simp only [kF, add_mul, mul_add, hc c d a b]
      abel
    change kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 true F1 (fun _ _ => rfl) a b c d

end Pair

theorem cyclic_locFin : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
    (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) →
    ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
    ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  intro n V _ _ F1 F2 h1 h2 hc f hgen S₀ hfin hf hst x
  obtain ⟨T, hT, rfl⟩ := hgen x
  have hT' : T ∈ Algebra.adjoin ℂ (Set.range (letters F1 F2)) := by
    rw [range_letters]
    exact hT
  obtain ⟨k, hk⟩ := mem_fil_of_adjoin (letters F1 F2) S₀ hT' hf
  exact ⟨fil (letters F1 F2) S₀ k, fil_finite _ _ k, hk, fun a b =>
    fil_stable _ _ (comm_letters h1 h2 hc a b) (hst a b) k⟩

end GlobalTheory.CompanionTheory.ModelS.LocFin
