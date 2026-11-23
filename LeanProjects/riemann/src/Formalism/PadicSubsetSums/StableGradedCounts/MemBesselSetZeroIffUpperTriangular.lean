import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Lemmata.TwistedIdempotents.TwistedIdem

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section GelfandTrick
variable {G : Type} [Group G] [Fintype G]

open Classical in
theorem twistedIdem_mul_of (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : twistedIdem J χ * MonoidAlgebra.of ℂ G (v : G)
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by
  rw [twistedIdem_def, Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight v) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, smul_smul, Subgroup.coe_mul]
  congr 1
  have h1 : ((χ v : ℂˣ) : ℂ) ≠ 0 := (χ v).ne_zero
  have h2 : ((χ u : ℂˣ) : ℂ) ≠ 0 := (χ u).ne_zero
  rw [map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp

theorem idem_sandwich (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G ((u : G) * g * u') * twistedIdem J χ =
      (((χ u * χ u' : ℂˣ)) : ℂ) •
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  rw [map_mul, map_mul]
  calc twistedIdem J χ * (MonoidAlgebra.of ℂ G (u : G) * MonoidAlgebra.of ℂ G g *
        MonoidAlgebra.of ℂ G (u' : G)) * twistedIdem J χ
      = (twistedIdem J χ * MonoidAlgebra.of ℂ G (u : G)) * MonoidAlgebra.of ℂ G g *
        (MonoidAlgebra.of ℂ G (u' : G) * twistedIdem J χ) := by simp only [mul_assoc]
    _ = _ := by
      rw [twistedIdem_mul_of, of_mul_twistedIdem, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul, Units.val_mul]

theorem idem_sandwich_zero (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G)
    (h : (u : G) * g * u' = g) (hne : χ u * χ u' ≠ 1) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ = 0 := by
  have h1 := idem_sandwich J χ u u' g
  rw [h] at h1
  set X := twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ
  have h2 : ((1 : ℂ) - ((χ u * χ u' : ℂˣ) : ℂ)) • X = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.mp h3).symm
  · exact h3

noncomputable def antiLift (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (MonoidAlgebra ℂ G)ᵐᵒᵖ :=
  MonoidAlgebra.lift ℂ _ G
    { toFun := fun g => MulOpposite.op (MonoidAlgebra.of ℂ G (σ g))
      map_one' := by
        have h1 : σ 1 = 1 := by
          have := hσ 1 1
          rw [mul_one] at this
          exact (mul_eq_left.mp this.symm)
        rw [h1, map_one, MulOpposite.op_one]
      map_mul' := by
        intro x y
        rw [hσ, map_mul, MulOpposite.op_mul] }

theorem antiLift_of (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (g : G) :
    antiLift σ hσ (MonoidAlgebra.of ℂ G g) = MulOpposite.op (MonoidAlgebra.of ℂ G (σ g)) := by
  simp [antiLift]

open Classical in
theorem antiLift_idem (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u) :
    antiLift σ hσ (twistedIdem J χ) = MulOpposite.op (twistedIdem J χ) := by
  let s : J ≃ J :=
    { toFun := fun u => ⟨σ u, (hJ u).1⟩
      invFun := fun u => ⟨σ u, (hJ u).1⟩
      left_inv := fun u => Subtype.ext (hσσ u)
      right_inv := fun u => Subtype.ext (hσσ u) }
  rw [twistedIdem_def, map_sum]
  show _ = MulOpposite.opAddEquiv _
  rw [map_sum]
  refine Fintype.sum_equiv s _ _ (fun u => ?_)
  rw [map_smul, antiLift_of, MulOpposite.opAddEquiv_apply, MulOpposite.op_smul]
  have : χ (s u) = χ u := (hJ u).2
  rw [this]
  rfl

theorem hecke_comm (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (H : ∀ g, (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
      (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)) (g g' : G) :
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  have key : ∀ g, twistedIdem J χ * MonoidAlgebra.of ℂ G (σ g) * twistedIdem J χ =
      twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ := by
    intro g
    rcases H g with ⟨u, u', h1, h2⟩ | ⟨u, u', h1, h2⟩
    · rw [h1, idem_sandwich, h2, Units.val_one, one_smul]
    · rw [idem_sandwich_zero J χ u u' g h1 h2]
      obtain ⟨m, hm⟩ := hJ u
      obtain ⟨m', hm'⟩ := hJ u'
      refine idem_sandwich_zero J χ ⟨σ u', m'⟩ ⟨σ u, m⟩ (σ g) ?_ ?_
      · show σ u' * σ g * σ u = σ g
        rw [← hσ, ← hσ, ← mul_assoc, h1]
      · rw [hm, hm', mul_comm]; exact h2
  have fix : ∀ a, antiLift σ hσ (twistedIdem J χ * a * twistedIdem J χ) =
      MulOpposite.op (twistedIdem J χ * a * twistedIdem J χ) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [map_mul, map_mul, antiLift_idem σ hσ hσσ J χ hJ, antiLift_of, ← MulOpposite.op_mul,
        ← MulOpposite.op_mul, ← mul_assoc, key]
    | add x y hx hy => rw [mul_add, add_mul, map_add, hx, hy, MulOpposite.op_add]
    | smul r x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, hx, MulOpposite.op_smul]
  have h := map_mul (antiLift σ hσ) (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ)
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ)
  rw [fix, fix, ← MulOpposite.op_mul] at h
  have h' : (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      twistedIdem J χ * (MonoidAlgebra.of ℂ G g * twistedIdem J χ * twistedIdem J χ *
        MonoidAlgebra.of ℂ G g') * twistedIdem J χ := by simp only [mul_assoc]
  rw [h', fix, ← h'] at h
  exact MulOpposite.op_injective h

theorem gelfand_trick {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ)
    (hcomm : ∀ g g' : G, (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ))
    (hirr : IsIrr ρ) :
    Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))) ≤ 1 := by
  first | exact Bl.CyclicComponents.goal1 .. | (apply Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply @Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> first | assumption | infer_instance)

end GelfandTrick

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section GG
variable {K : Type} [Field K] {N : ℕ}

def IsUT (A : Matrix (Fin N) (Fin N) K) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

theorem mem_besselSet_zero_iff_upper_triangular (u : GL (Fin N) K) : u ∈ besselSet K 0 0 N ↔ IsUT (u : Matrix (Fin N) (Fin N) K) := by
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    intro i j _ h
    omega

theorem IsUT.det {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h.1 i

noncomputable def utMk (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) : GL (Fin N) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h.det]; exact one_ne_zero)

@[simp] theorem utMk_val (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) :
    ((utMk A h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = A := rfl

theorem IsUT.one : IsUT (1 : Matrix (Fin N) (Fin N) K) :=
  ⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_gt h)⟩

theorem IsUT.mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) : IsUT (A * B) := by
  constructor
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.1, hB.1, one_mul]
    · intro m _ hm
      rcases lt_or_gt_of_ne hm with h | h
      · rw [hA.2 i m h, zero_mul]
      · rw [hB.2 m i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA.2 i m h, zero_mul]
    · rw [hB.2 m j (lt_of_lt_of_le hij h), mul_zero]

def edgeSum (A : Matrix (Fin N) (Fin N) K) : K :=
  ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then A i j else 0

theorem besselChar_zero_eq_edge_sum (ψ₀ : AddChar K ℂ) (u : GL (Fin N) K) :
    besselChar ψ₀ 0 0 N u = ψ₀ (edgeSum (u : Matrix (Fin N) (Fin N) K)) := by
  unfold besselChar edgeSum
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : besselEdge 0 0 i j ↔ (j : ℕ) = i + 1 := by
    unfold besselEdge
    omega
  simp only [this]

theorem edgeSum_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) :
    edgeSum (A * B) = edgeSum A + edgeSum B := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hij : i ≠ j := by
      intro h'; rw [h'] at h; omega
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      hA.1, hB.1, one_mul, mul_one, Finset.sum_eq_zero, add_zero, add_comm]
    intro m hm
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
    rcases lt_or_ge m i with h1 | h1
    · rw [hA.2 i m h1, zero_mul]
    · have : j < m := by
        have h2 : (m : ℕ) ≠ i := fun h' => hm.2 (Fin.ext h')
        have h3 : (m : ℕ) ≠ j := fun h' => hm.1 (Fin.ext h')
        have h4 : (i : ℕ) ≤ m := h1
        show (j : ℕ) < m
        omega
      rw [hB.2 m j this, mul_zero]
  · rw [add_zero]

theorem IsUT.inv_val (u : GL (Fin N) K) (h : IsUT (u : Matrix (Fin N) (Fin N) K)) :
    IsUT ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have hlow : ∀ i j, j < i → ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j = 0 := by
    intro i j hij
    rw [Matrix.coe_units_inv]
    have : Invertible (u : Matrix (Fin N) (Fin N) K) := u.invertible
    have hb : Matrix.BlockTriangular (u : Matrix (Fin N) (Fin N) K) id := fun i j hij => h.2 i j hij
    exact Matrix.blockTriangular_inv_of_blockTriangular hb hij
  refine ⟨fun i => ?_, hlow⟩
  have h1 : ((u * u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i i = 1 := by
    rw [mul_inv_cancel]; simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, h.1, one_mul] at h1
  · exact h1
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h' | h'
    · rw [h.2 i m h', zero_mul]
    · rw [hlow m i h', mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def uniSub (K : Type) [Field K] (N : ℕ) : Subgroup (GL (Fin N) K) where
  carrier := {u | IsUT (u : Matrix (Fin N) (Fin N) K)}
  mul_mem' := fun {a b} ha hb => by
    show IsUT ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_mul]; exact IsUT.mul ha hb
  one_mem' := by
    show IsUT ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_one]; exact IsUT.one
  inv_mem' := fun {a} ha => IsUT.inv_val a ha

noncomputable def uniChar (ψ₀ : AddChar K ℂ) (N : ℕ) : uniSub K N →* ℂˣ where
  toFun u := (ψ₀.toMonoidHom.toHomUnits) (Multiplicative.ofAdd (edgeSum ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
  map_one' := by
    have : edgeSum (((1 : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 0 := by
      have h := edgeSum_mul (K := K) (N := N) IsUT.one IsUT.one
      rw [mul_one] at h
      simpa using h
    rw [this]; simp
  map_mul' := fun a b => by
    have : edgeSum (((a * b : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        edgeSum ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) +
          edgeSum ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
      rw [Subgroup.coe_mul, Units.val_mul]
      exact edgeSum_mul a.2 b.2
    rw [this, ofAdd_add, map_mul]

theorem uniChar_val (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ((uniChar ψ₀ N u : ℂˣ) : ℂ) = ψ₀ (edgeSum ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  simp [uniChar]

theorem besselSpace_zero_eq_equivariant {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) :
    besselSpace ρ ψ₀ 0 0 = eqvSpace ρ (fun u : uniSub K N => (u : GL (Fin N) K))
      (fun u => ((uniChar ψ₀ N u : ℂˣ) : ℂ)) := by
  ext x
  constructor
  · intro h u
    have := h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mpr u.2⟩
    show ρ (u : GL (Fin N) K) x = ((uniChar ψ₀ N u : ℂˣ) : ℂ) • x
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum]
    exact this
  · intro h u
    have : ρ (u : GL (Fin N) K) x =
        ((uniChar ψ₀ N ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩ : ℂˣ) : ℂ) • x :=
      h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum] at this
    exact this

end GG
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Comb
variable {N : ℕ}

theorem desc_run (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) :
    ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
  intro d
  induction d with
  | zero =>
    intro i j hj hlt
    have : j = i := Fin.ext (by omega)
    rw [this] at hlt
    exact absurd hlt (lt_irrefl _)
  | succ d ih =>
    intro i j hj hlt m him hmj
    have hi' : (i : ℕ) + 1 < N := by have := j.2; omega
    set i' : Fin N := ⟨i + 1, hi'⟩ with hi'def
    have hi'v : (i' : ℕ) = i + 1 := rfl
    have hne : τ i' ≠ τ i := by
      intro h'
      have := τ.injective h'
      have := congrArg Fin.val this
      omega
    have hlt' : (τ j : ℕ) < τ i := hlt
    have him' : (i : ℕ) ≤ m := him
    have hmj' : (m : ℕ) ≤ j := hmj
    by_cases hmi : m = i
    · rw [hmi]
    have hmi' : (m : ℕ) ≠ i := fun h' => hmi (Fin.ext h')
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 := h i i' hi'v h1
      by_cases hji : j = i'
      · have : m = i' := Fin.ext (by rw [hji] at hmj'; omega)
        rw [this]; omega
      · have h3 : τ j ≠ τ i' := fun h' => hji (τ.injective h')
        have h3' : (τ j : ℕ) ≠ τ i' := fun h' => h3 (Fin.ext h')
        have h4 : τ j < τ i' := by
          show (τ j : ℕ) < τ i'
          omega
        have := ih i' j (by omega) h4 m (by show (i' : ℕ) ≤ m; omega) hmj
        omega
    · exfalso
      have h1' : (τ i : ℕ) < τ i' := h1
      have h4 : τ j < τ i' := lt_trans hlt h1
      have hall := ih i' j (by omega) h4
      have hjj := hall j (by show (i' : ℕ) ≤ j; omega) le_rfl
      have hm0 : (i' : ℕ) + ((τ i' : ℕ) - τ i) < N := by have := j.2; omega
      set m0 : Fin N := ⟨i' + ((τ i' : ℕ) - τ i), hm0⟩ with hm0def
      have hm0v : (m0 : ℕ) = i' + ((τ i' : ℕ) - τ i) := rfl
      have := hall m0 (by show (i' : ℕ) ≤ m0; omega) (by show (m0 : ℕ) ≤ j; omega)
      have h5 : τ m0 = τ i := Fin.ext (by omega)
      have h6 := congrArg Fin.val (τ.injective h5)
      omega

theorem desc_invol (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (i : Fin N) :
    τ (τ i) = i := by
  have run := desc_run τ h
  have run' : ∀ i j : Fin N, i < j → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    exact run (j - i) i j (by omega)
  obtain ⟨j0, hj0⟩ := τ.surjective i
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := run' j0 i h1 (by rw [hj0]; exact hc) i h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]
    · exfalso
      have hp : ∃ p, p < i ∧ i < τ p := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Iio i, τ p ∈ (Finset.Iio i).erase (τ i) := by
          intro p hp
          have hp' : p < i := Finset.mem_Iio.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_lt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Iio.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Iio.mpr hc)] at hcard
        have : 0 < (Finset.Iio i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Iio.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' p j0 (lt_trans hp1 h1) (by rw [hj0]; exact hp2)
      have e1 := hr i hp1.le h1.le
      have e2 := hr j0 (lt_trans hp1 h1).le le_rfl
      rw [hj0] at e2
      have hc' : (τ i : ℕ) < i := hc
      have h1' : (i : ℕ) < j0 := h1
      omega
  · rw [hc, hc]
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exfalso
      have hp : ∃ p, i < p ∧ τ p < i := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Ioi i, τ p ∈ (Finset.Ioi i).erase (τ i) := by
          intro p hp
          have hp' : i < p := Finset.mem_Ioi.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_gt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Ioi.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [← this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Ioi.mpr hc)] at hcard
        have : 0 < (Finset.Ioi i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Ioi.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' j0 p (lt_trans h1 hp1) (by rw [hj0]; exact hp2)
      have e1 := hr i h1.le hp1.le
      rw [hj0] at e1
      have hc' : (i : ℕ) < τ i := hc
      have h1' : (j0 : ℕ) < i := h1
      omega
    · have := run' i j0 h1 (by rw [hj0]; exact hc) j0 h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]

theorem desc_const {α : Type} (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (t : Fin N → α)
    (ht : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j) (i : Fin N) :
    t (τ i) = t i := by
  have inv := desc_invol τ h
  have main : ∀ i : Fin N, i < τ i → t (τ i) = t i := by
    intro i hi
    have hi' : (i : ℕ) < τ i := hi
    have hr := desc_run τ h ((τ i : ℕ) - i) i (τ i) (by omega) (by rw [inv]; exact hi)
    have step : ∀ d : ℕ, ∀ m : Fin N, (m : ℕ) = i + d → m ≤ τ i → t m = t i := by
      intro d
      induction d with
      | zero => intro m hm _; rw [show m = i from Fin.ext (by omega)]
      | succ d ih =>
        intro m hm hle
        have hle' : (m : ℕ) ≤ τ i := hle
        have hm1 : (i : ℕ) + d < N := by have := m.2; omega
        set m1 : Fin N := ⟨i + d, hm1⟩ with hm1def
        have hm1v : (m1 : ℕ) = i + d := rfl
        have e1 := hr m1 (by show (i : ℕ) ≤ m1; omega) (by show (m1 : ℕ) ≤ τ i; omega)
        have e2 := hr m (by show (i : ℕ) ≤ m; omega) hle
        rw [← ih m1 hm1v (by show (m1 : ℕ) ≤ τ i; omega)]
        exact (ht m1 m (by omega) (by show (τ m : ℕ) < τ m1; omega)).symm
    exact step ((τ i : ℕ) - i) (τ i) (by omega) le_rfl
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have := main (τ i) (by rw [inv]; exact hc)
    rw [inv] at this
    exact this.symm
  · rw [hc]
  · exact main i hc

end Comb
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Bruhat
variable {K : Type} [Field K] {N : ℕ}

def rowOp (a : Fin N → K) (r : Fin N) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun i m => if m = r then a i else 0

theorem rowOp_isUT (a : Fin N → K) (r : Fin N) (ha : ∀ i, r ≤ i → a i = 0) :
    IsUT (rowOp a r) := by
  constructor
  · intro i
    simp only [rowOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [ha i (h ▸ le_rfl), add_zero]
    · rw [add_zero]
  · intro i j hij
    simp only [rowOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply,
      zero_add]
    split_ifs with h
    · exact ha i (h ▸ hij.le)
    · rfl

theorem rowOp_mul (a : Fin N → K) (r : Fin N) (h : Matrix (Fin N) (Fin N) K) (i c : Fin N) :
    (rowOp a r * h) i c = h i c + a i * h r c := by
  rw [rowOp, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single r]
  · simp
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def colOp (k : Fin N) (b : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun m c => if m = k then b c else 0

theorem colOp_isUT (k : Fin N) (b : Fin N → K) (hb : ∀ c, c ≤ k → b c = 0) :
    IsUT (colOp k b) := by
  constructor
  · intro i
    simp only [colOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [hb i (h ▸ le_rfl), add_zero]
    · rw [add_zero]
  · intro i j hij
    simp only [colOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply,
      zero_add]
    split_ifs with h
    · exact hb j (h ▸ hij.le)
    · rfl

theorem mul_colOp (k : Fin N) (b : Fin N → K) (h : Matrix (Fin N) (Fin N) K) (i c : Fin N) :
    (h * colOp k b) i c = h i c + h i k * b c := by
  rw [colOp, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single k]
  · simp
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def Cleared (h : Matrix (Fin N) (Fin N) K) (k : ℕ) (p : Fin N → Fin N) : Prop :=
  ∀ j : Fin N, (j : ℕ) < k →
    h (p j) j ≠ 0 ∧ (∀ i, i ≠ p j → h i j = 0) ∧ (∀ c, c ≠ j → h (p j) c = 0)

open Classical in
theorem bruhat_step (g : GL (Fin N) K) : ∀ k : ℕ, k ≤ N → ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ p, Cleared ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) k p := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, ?_, id, ?_⟩
    · rw [Units.val_one]; exact IsUT.one
    · rw [Units.val_one]; exact IsUT.one
    · intro j hj; omega
  | succ k ih =>
    intro hk
    obtain ⟨u, u', hu, hu', p, hp⟩ := ih (by omega)
    set hh : GL (Fin N) K := u * g * u' with hhdef
    set h : Matrix (Fin N) (Fin N) K := (hh : Matrix (Fin N) (Fin N) K) with hdef
    set kk : Fin N := ⟨k, by omega⟩ with hkk
    have hex : ∃ r, h r kk ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : h.det = 0 := Matrix.det_eq_zero_of_column_eq_zero kk hcon
      have h1 : IsUnit h.det := (Matrix.isUnit_iff_isUnit_det _).mp hh.isUnit
      exact h1.ne_zero h0
    set S : Finset (Fin N) := Finset.univ.filter (fun r => h r kk ≠ 0) with hS
    have hSne : S.Nonempty := by
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    set r0 := S.max' hSne with hr0
    have hd : h r0 kk ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    have hmax : ∀ i, r0 < i → h i kk = 0 := by
      intro i hi
      by_contra hne
      have := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact absurd hi (not_lt.mpr this)
    set d := h r0 kk with hddef
    set a : Fin N → K := fun i => if i < r0 then - h i kk / d else 0 with hadef
    set b : Fin N → K := fun c => if kk < c then - h r0 c / d else 0 with hbdef
    have haUT : IsUT (rowOp a r0) := rowOp_isUT a r0 (fun i hi => by
      simp only [hadef]; rw [if_neg (not_lt.mpr hi)])
    have hbUT : IsUT (colOp kk b) := colOp_isUT kk b (fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)])
    refine ⟨utMk _ haUT * u, u' * utMk _ hbUT, ?_, ?_, Function.update p kk r0, ?_⟩
    · rw [Units.val_mul]; exact IsUT.mul haUT hu
    · rw [Units.val_mul]; exact IsUT.mul hu' hbUT
    have hprod : ((utMk _ haUT * u * g * (u' * utMk _ hbUT) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = rowOp a r0 * h * colOp kk b := by
      have : utMk _ haUT * u * g * (u' * utMk _ hbUT) = utMk _ haUT * hh * utMk _ hbUT := by
        rw [hhdef]; group
      rw [this, Units.val_mul, Units.val_mul, utMk_val, utMk_val]
    rw [hprod]
    have hform : ∀ i c, (rowOp a r0 * h * colOp kk b) i c =
        h i c + a i * h r0 c + (h i kk + a i * d) * b c := by
      intro i c
      rw [mul_colOp, rowOp_mul, rowOp_mul]
    have F1 : ∀ j : Fin N, (j : ℕ) < k → p j ≠ r0 := by
      intro j hj h'
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      have := (hp j hj).2.2 kk hne
      rw [h'] at this
      exact hd this
    have F2 : ∀ j : Fin N, (j : ℕ) < k → h r0 j = 0 := fun j hj =>
      (hp j hj).2.1 r0 (F1 j hj).symm
    have F3 : ∀ i, h i kk + a i * d = if i = r0 then d else 0 := by
      intro i
      rcases lt_trichotomy i r0 with h1 | h1 | h1
      · simp only [hadef]
        rw [if_pos h1, if_neg (ne_of_lt h1)]
        field_simp
        ring
      · simp only [hadef]
        rw [if_pos h1, h1, if_neg (lt_irrefl _), zero_mul, add_zero]
      · simp only [hadef]
        rw [if_neg (ne_of_gt h1), if_neg (not_lt.mpr h1.le), hmax i h1, zero_mul, add_zero]
    have F4 : ∀ j : Fin N, (j : ℕ) < k → a (p j) = 0 := by
      intro j hj
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      simp only [hadef]
      rw [(hp j hj).2.2 kk hne]
      simp
    have F5 : ∀ c, c ≤ kk → b c = 0 := fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)]
    have F6 : a r0 = 0 := by simp only [hadef]; rw [if_neg (lt_irrefl _)]
    intro j hj
    by_cases hjk : j = kk
    · rw [hjk, Function.update_self]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F6, F5 kk le_rfl]
        simpa using hd
      · intro i hi
        rw [hform, F5 kk le_rfl, mul_zero, add_zero, F3, if_neg hi]
      · intro c hc
        rw [hform, F6, zero_mul, zero_mul, add_zero, add_zero]
        rcases lt_or_gt_of_ne hc with h1 | h1
        · rw [F5 c h1.le, mul_zero, add_zero]
          exact F2 c h1
        · simp only [hbdef]
          rw [if_pos h1]
          field_simp
          ring
    · have hjlt : (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
        omega
      have hjle : j ≤ kk := by show (j : ℕ) ≤ k; omega
      rw [Function.update_of_ne hjk]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F5 j hjle, F4 j hjlt]
        simpa using (hp j hjlt).1
      · intro i hi
        rw [hform, F5 j hjle, F2 j hjlt, (hp j hjlt).2.1 i hi]
        simp
      · intro c hc
        rw [hform, F3, if_neg (F1 j hjlt), F4 j hjlt, (hp j hjlt).2.2 c hc]
        simp

theorem bruhat_exists (g : GL (Fin N) K) : ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ (π : Equiv.Perm (Fin N)) (t : Fin N → K), (∀ j, t j ≠ 0) ∧
      ∀ i j, ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
        if i = π j then t j else 0 := by
  obtain ⟨u, u', hu, hu', p, hp⟩ := bruhat_step g N le_rfl
  refine ⟨u, u', hu, hu', ?_⟩
  set h : Matrix (Fin N) (Fin N) K := ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hinj : Function.Injective p := by
    intro j j' hjj
    by_contra hne
    have h1 := (hp j j.2).2.2 j' (Ne.symm hne)
    rw [hjj] at h1
    exact (hp j' j'.2).1 h1
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj), fun j => h (p j) j,
    fun j => (hp j j.2).1, ?_⟩
  intro i j
  rw [Equiv.ofBijective_apply]
  split_ifs with hij
  · rw [hij]
  · exact (hp j j.2).2.1 i hij

end Bruhat
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Transfer
variable {G : Type} [Group G]

def GTAlt (σ : G → G) (J : Subgroup G) (χ : J →* ℂˣ) (g : G) : Prop :=
  (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
    (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)

theorem GTAlt.transfer (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (u1 u2 : J) (g : G) (h : GTAlt σ J χ ((u1 : G) * g * u2)) : GTAlt σ J χ g := by
  rcases h with ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2⟩
  · left
    obtain ⟨m1, e1⟩ := hJ u1
    obtain ⟨m2, e2⟩ := hJ u2
    refine ⟨(⟨σ u2, m2⟩ : J)⁻¹ * a * u1, u2 * b * (⟨σ u1, m1⟩ : J)⁻¹, ?_, ?_⟩
    · rw [hσ, hσ] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : σ g = (σ u2)⁻¹ * (σ u2 * (σ g * σ u1)) * (σ u1)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv, e1, e2]
      calc (χ u2)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u1)⁻¹)
          = (χ a * χ b) * ((χ u2)⁻¹ * χ u2) * (χ u1 * (χ u1)⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = 1 := by rw [h2]; simp
  · right
    refine ⟨u1⁻¹ * a * u1, u2 * b * u2⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : (u1 : G)⁻¹ * a * u1 * g * (u2 * b * (u2 : G)⁻¹) =
          (u1 : G)⁻¹ * (a * (u1 * g * u2) * b) * (u2 : G)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv]
      intro h3
      apply h2
      calc χ a * χ b = (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) := by
            have : (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) =
              (χ a * χ b) * ((χ u1)⁻¹ * χ u1) * (χ u2 * (χ u2)⁻¹) := by
                simp only [mul_assoc, mul_comm, mul_left_comm]
            rw [this]; simp
        _ = 1 := h3

end Transfer

section Flip
variable {K : Type} [Field K] {N : ℕ}

def flipM (A : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => A (Fin.rev j) (Fin.rev i)

theorem flipM_apply (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    flipM A i j = A (Fin.rev j) (Fin.rev i) := rfl

theorem flipM_mul (A B : Matrix (Fin N) (Fin N) K) : flipM (A * B) = flipM B * flipM A := by
  ext i j
  simp only [flipM_apply, Matrix.mul_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun m => ?_)
  simp [mul_comm]

theorem flipM_one : flipM (1 : Matrix (Fin N) (Fin N) K) = 1 := by
  ext i j
  rw [flipM_apply, Matrix.one_apply, Matrix.one_apply]
  simp only [Fin.rev_inj]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem flipM_flipM (A : Matrix (Fin N) (Fin N) K) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

def flipG (g : GL (Fin N) K) : GL (Fin N) K :=
  ⟨flipM g.1, flipM (g⁻¹).1, by
    rw [← flipM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, flipM_one], by
    rw [← flipM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, flipM_one]⟩

theorem flipG_val (g : GL (Fin N) K) :
    ((flipG g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = flipM g.1 := rfl

theorem flipG_mul (x y : GL (Fin N) K) : flipG (x * y) = flipG y * flipG x := by
  apply Units.ext
  rw [Units.val_mul, flipG_val, flipG_val, flipG_val, Units.val_mul, flipM_mul]

theorem flipG_flipG (x : GL (Fin N) K) : flipG (flipG x) = x := by
  apply Units.ext
  rw [flipG_val, flipG_val, flipM_flipM]

theorem IsUT.flip {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : IsUT (flipM A) :=
  ⟨fun i => h.1 _, fun i j hij => h.2 _ _ (Fin.rev_lt_rev.mpr hij)⟩

theorem edgeSum_flip (A : Matrix (Fin N) (Fin N) K) : edgeSum (flipM A) = edgeSum A := by
  unfold edgeSum
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, flipM_apply]
  have : ((j : ℕ) = i + 1) ↔ ((Fin.rev i : Fin N) : ℕ) = (Fin.rev j : Fin N) + 1 := by
    rw [Fin.val_rev, Fin.val_rev]
    have := i.2
    have := j.2
    omega
  simp only [this]

theorem flip_char (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ∃ h : flipG (u : GL (Fin N) K) ∈ uniSub K N, uniChar ψ₀ N ⟨flipG u, h⟩ = uniChar ψ₀ N u := by
  refine ⟨IsUT.flip u.2, ?_⟩
  apply Units.ext
  rw [uniChar_val, uniChar_val]
  show ψ₀ (edgeSum (flipM _)) = _
  rw [edgeSum_flip]

end Flip

section Elem
variable {K : Type} [Field K] {N : ℕ}

def elM (p q : Fin N) (v : K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun x c => if x = p ∧ c = q then v else 0

theorem elM_isUT (p q : Fin N) (v : K) (h : p < q) : IsUT (elM p q v) := by
  constructor
  · intro i
    simp only [elM, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    rw [if_neg, add_zero]
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at h
    exact lt_irrefl _ h
  · intro i j hij
    simp only [elM, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply, zero_add]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at h
    exact lt_asymm h hij

theorem elM_mul (p q : Fin N) (v : K) (h : Matrix (Fin N) (Fin N) K) (x c : Fin N) :
    (elM p q v * h) x c = h x c + if x = p then v * h q c else 0 := by
  rw [elM, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single q]
  · by_cases hx : x = p <;> simp [hx]
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem mul_elM (p q : Fin N) (v : K) (h : Matrix (Fin N) (Fin N) K) (x c : Fin N) :
    (h * elM p q v) x c = h x c + if c = q then h x p * v else 0 := by
  rw [elM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single p]
  · by_cases hx : c = q <;> simp [hx]
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem edgeSum_elM (p q : Fin N) (v : K) :
    edgeSum (elM p q v) = if (q : ℕ) = p + 1 then v else 0 := by
  unfold edgeSum
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · by_cases h : (q : ℕ) = p + 1
      · have hpq : p ≠ q := by intro h'; rw [h'] at h; omega
        simp [h, elM, Matrix.one_apply_ne hpq]
      · simp [h]
    · intro c _ hc
      split_ifs with h
      · have hpc : p ≠ c := by intro h'; rw [h'] at h; omega
        simp [elM, Matrix.one_apply_ne hpc, hc]
      · rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x _ hx
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · have hxc : x ≠ c := by intro h'; rw [h'] at h; omega
      simp [elM, Matrix.one_apply_ne hxc, hx]
    · rfl
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Elem

section Mono
variable {K : Type} [Field K] {N : ℕ}

def MonoAdm (π : Equiv.Perm (Fin N)) (t : Fin N → K) : Prop :=
  ∀ i j : Fin N, (j : ℕ) = i + 1 → π i < π j → (π j : ℕ) = π i + 1 ∧ t i = t j

theorem flip_mono (n : GL (Fin N) K) (π : Equiv.Perm (Fin N)) (t : Fin N → K)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : MonoAdm π t) : flipG n = n := by
  set τ : Equiv.Perm (Fin N) := π.trans Fin.revPerm with hτ
  have hτv : ∀ i, τ i = Fin.rev (π i) := fun i => rfl
  have hlt : ∀ i j, τ j < τ i ↔ π i < π j := by
    intro i j
    rw [hτv, hτv, Fin.rev_lt_rev]
  have h1 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1 := by
    intro i j hij hl
    have := (hadm i j hij ((hlt i j).mp hl)).1
    rw [hτv, hτv, Fin.val_rev, Fin.val_rev]
    have := (π j).2
    omega
  have h2 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j := fun i j hij hl =>
    (hadm i j hij ((hlt i j).mp hl)).2
  have inv := desc_invol τ h1
  have cst := desc_const τ h1 t h2
  have hπ : ∀ x, π x = Fin.rev (τ x) := fun x => by rw [hτv, Fin.rev_rev]
  apply Units.ext
  ext i j
  rw [flipG_val, flipM_apply, hn, hn]
  by_cases hij : i = π j
  · have e1 : Fin.rev i = τ j := by rw [hij, hτv]
    rw [if_pos hij, e1, hπ (τ j), inv, if_pos rfl, cst]
  · rw [if_neg hij, if_neg]
    intro h3
    apply hij
    have e2 : j = τ (Fin.rev i) := by rw [hτv, ← h3, Fin.rev_rev]
    have e3 : τ j = Fin.rev i := by rw [e2, inv]
    rw [hπ j, e3, Fin.rev_rev]

theorem mono_not_adm (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (n : GL (Fin N) K)
    (π : Equiv.Perm (Fin N)) (t : Fin N → K) (ht : ∀ j, t j ≠ 0)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : ¬ MonoAdm π t) :
    ∃ u u' : uniSub K N, (u : GL (Fin N) K) * n * u' = n ∧
      uniChar ψ₀ N u * uniChar ψ₀ N u' ≠ 1 := by
  unfold MonoAdm at hadm
  push Not at hadm
  obtain ⟨i, j, hij, hlt, hbad⟩ := hadm
  obtain ⟨a0, ha0⟩ := (AddChar.ne_one_iff).mp hψ
  have hilt : i < j := by show (i : ℕ) < j; omega
  set s : K := if (π j : ℕ) = π i + 1 then t i / t j else 0 with hs
  have hs1 : 1 - s ≠ 0 := by
    rw [hs]
    split_ifs with h
    · have := hbad h
      intro h'
      apply this
      have h'' : t i / t j = 1 := (sub_eq_zero.mp h').symm
      rwa [div_eq_one_iff_eq (ht j)] at h''
    · simp
  set a : K := a0 / (1 - s) with ha
  set c0 : K := a * t i / t j with hc0
  refine ⟨⟨utMk _ (elM_isUT (π i) (π j) (-c0) hlt), elM_isUT (π i) (π j) (-c0) hlt⟩,
    ⟨utMk _ (elM_isUT i j a hilt), elM_isUT i j a hilt⟩, ?_, ?_⟩
  · apply Units.ext
    ext x c
    simp only [Units.val_mul, utMk_val]
    rw [mul_elM, elM_mul, elM_mul, hn, hn, hn, hn]
    have hne : π j ≠ π i := ne_of_gt hlt
    rw [if_neg hne]
    by_cases hx : x = π i
    · by_cases hc : c = j
      · rw [if_pos hx, if_pos hc, hc, if_pos rfl, if_pos hx]
        rw [hx, if_neg hne.symm, hc0]
        have htj := ht j
        simp only [if_true, mul_zero, add_zero, zero_add]
        field_simp
        ring
      · have : π j ≠ π c := fun h' => hc (π.injective h').symm
        rw [if_neg hc, if_neg this]
        simp
    · rw [if_neg hx, if_neg hx]
      simp
  · intro h
    apply ha0
    have h' := congrArg (fun z : ℂˣ => (z : ℂ)) h
    simp only [Units.val_mul, uniChar_val, Units.val_one, utMk_val] at h'
    rw [← AddChar.map_add_eq_mul, edgeSum_elM, edgeSum_elM, if_pos hij] at h'
    have e : (if (π j : ℕ) = π i + 1 then -c0 else 0) + a = a0 := by
      have e1 : (if (π j : ℕ) = π i + 1 then -c0 else 0) = - (a * s) := by
        rw [hs]
        split_ifs with h
        · rw [hc0]; ring
        · simp
      rw [e1, ha]
      field_simp
      ring
    rw [e] at h'
    exact h'

end Mono

theorem gelfand_graev_multiplicity_one : GelfandGraevMultOne := by
  intro K V _ _ _ _ _ N ψ₀ ρ hψ hirr
  classical
  have : Fintype (GL (Fin N) K) := Fintype.ofFinite _
  rw [besselSpace_zero_eq_equivariant]
  refine gelfand_trick ρ (uniSub K N) (uniChar ψ₀ N) ?_ hirr
  refine hecke_comm flipG flipG_mul flipG_flipG (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ?_
  intro g
  obtain ⟨u, u', hu, hu', π, t, ht, hn⟩ := bruhat_exists g
  refine GTAlt.transfer flipG flipG_mul (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ⟨u, hu⟩ ⟨u', hu'⟩
    g ?_
  by_cases hadm : MonoAdm π t
  · left
    refine ⟨1, 1, ?_, by simp⟩
    rw [flip_mono _ π t hn hadm]
    simp
  · right
    exact mono_not_adm ψ₀ hψ _ π t ht hn hadm

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
