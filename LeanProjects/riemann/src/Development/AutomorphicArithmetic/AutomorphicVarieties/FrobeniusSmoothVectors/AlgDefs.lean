import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

section Lau

variable {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K) [SetLike.GradedMonoid P]

theorem coeff_mul_mem {p q : AddMonoidAlgebra K ℤ} (j : ℤ) (M : Submodule C K)
    (h : ∀ a b, a + b = j → p.coeff a * q.coeff b ∈ M) : (p * q).coeff j ∈ M := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  dsimp only
  split_ifs with e
  · exact h a b e
  · exact zero_mem _

def lauSub : Subalgebra C (AddMonoidAlgebra K ℤ) where
  carrier := {p | ∀ j, p.coeff j ∈ P j}
  mul_mem' {p q} hp hq j := coeff_mul_mem j _ fun a b e => e ▸ SetLike.mul_mem_graded (hp a) (hq b)
  add_mem' {p q} hp hq j := add_mem (hp j) (hq j)
  algebraMap_mem' c j := by
    classical
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with e
    · subst e
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.one_mem_graded P)
    · exact zero_mem _

theorem mem_lauSub {p : AddMonoidAlgebra K ℤ} : p ∈ lauSub P ↔ ∀ j, p.coeff j ∈ P j := Iff.rfl

theorem single_mem_lauSub {j : ℤ} {x : K} (hx : x ∈ P j) : AddMonoidAlgebra.single j x ∈ lauSub P := by
  classical
  intro i
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with e
  · subst e
    exact hx
  · exact zero_mem _

variable [IsLocalRing C]

structure HasVertex : Prop where
  zero : ∀ x ∈ P 0, ∃ c : C, algebraMap C K c = x
  cross : ∀ j, j ≠ 0 → ∀ x ∈ P j, ∀ y ∈ P (-j), ∃ c ∈ maximalIdeal C, algebraMap C K c = x * y

variable {P} in

def vertex (h : HasVertex P) : Ideal (lauSub P) where
  carrier := {p | ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0}
  add_mem' := by
    rintro p q ⟨c, h1, h2⟩ ⟨d, h3, h4⟩
    exact ⟨c + d, add_mem h1 h3, by rw [map_add, h2, h4]; rfl⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro q p ⟨c, h1, h2⟩
    refine Submodule.mem_map.1 (coeff_mul_mem (p := q.1) (q := p.1) 0
      (Submodule.map (Algebra.linearMap C K) (maximalIdeal C)) fun a b e => Submodule.mem_map.2 ?_)
    by_cases h0 : a = 0
    · subst h0
      rw [zero_add] at e
      subst e
      obtain ⟨d, hd⟩ := h.zero _ (q.2 0)
      exact ⟨d * c, Ideal.mul_mem_left _ _ h1, by rw [← hd, ← h2, ← map_mul]; rfl⟩
    · obtain rfl : b = -a := by omega
      exact h.cross a h0 _ (q.2 a) _ (p.2 _)

variable {P} in
theorem mem_vertex (h : HasVertex P) {p : lauSub P} :
    p ∈ vertex h ↔ ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0 := Iff.rfl

end Lau

section Part

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type}
  [CommRing K] [Algebra C K] (ρ : NRep F n K)

def NRep.part (j : ℤ) : Submodule C K := Submodule.span C (ρ.mon j)

instance : SetLike.GradedMonoid (ρ.part C) where
  one_mem := Submodule.subset_span ⟨[], by simp, by simp⟩
  mul_mem i j x y hx hy := by
    have := Submodule.mul_mem_mul hx hy
    rw [NRep.part, NRep.part, Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨L, h1, rfl⟩, _, ⟨M, h2, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp only [List.map_append, List.sum_append, h1, h2], by simp⟩

theorem NRep.r_mem_part (g : F.G0) (i j : Fin n) : ρ.r g i j ∈ ρ.part C (w n i - w n j) :=
  Submodule.subset_span ⟨[(g, i, j)], by simp, by simp⟩

end Part

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsVertexRing (C : Type) [CommRing C] [IsLocalRing C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D) :
    Prop where
  noeth : IsNoetherianRing D
  inj : Function.Injective (algebraMap C D)
  sep : ⨅ N : ℕ, 𝔪 ^ N = ⊥
  comap : 𝔪.comap (algebraMap C D) = maximalIdeal C
  surj : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ 𝔪

structure IsModel (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra C D]
    (𝔪 : Ideal D) (ρ : NRep F n D) : Prop where
  cont : ρ.Cont 𝔪
  off : ∀ g i j, i ≠ j → ρ.r g i j ∈ 𝔪
  dg : ∀ g i, ∃ c : C, algebraMap C D c = ρ.r g i i ∧
    res O C c = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  psi : ∀ v i g, ∃ c : C, algebraMap C D c = ρ.ψ v i g ∧
    res O C c = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  mon : ∀ x ∈ ρ.mon 0, ∃ c : C, algebraMap C D c = x

end UpperTheory.V.Fr
