import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspIff

def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }

theorem mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl

theorem pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp

theorem eq_zero_of_sum_char {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0) (v : V) (hv : ∀ u ∈ U, ρ u v = v) : v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then ρ.character u else 0) =
      ∑ g : U, Representation.character (ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => ρ.character g)
  rw [hs] at h
  rw [h, mul_zero] at h1
  have h2 : Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ)]
    exact h1.symm
  have hm : v ∈ Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) := by
    rw [Representation.mem_invariants]
    exact fun u => hv u.1 u.2
  rw [h2] at hm
  simpa using hm

theorem isCuspidal_of_sum_char : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm K σ * x * (pm K σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm K σ * x⁻¹ * (pm K σ)⁻¹ = (pm K σ * x * (pm K σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm K σ) v) (by
    intro u hu
    have hx : (pm K σ)⁻¹ * u * pm K σ ∈ unip K b := by
      apply hun
      have : pm K σ * ((pm K σ)⁻¹ * u * pm K σ) * (pm K σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm K σ = pm K σ * ((pm K σ)⁻¹ * u * pm K σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm K σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3

end GlobalTheory.CompanionTheory.TyFin.CuspIff
