import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb

noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module Polynomial TensorProduct

section Inv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inv_one_mem_all (h1 : (1 : BdR) ∈ PD.Fil 1) : ∀ a : ℤ, (1 : BdR) ∈ PD.Fil a := by
  have hpos : ∀ n : ℕ, (1 : BdR) ∈ PD.Fil ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have := PD.Fil_mul 1 ((n : ℤ) + 1) 1 1 h1 ih
      rw [one_mul] at this
      convert this using 2
      push_cast; ring
  have hle : ∀ (a : ℤ) (n : ℕ), PD.Fil (a + n) ≤ PD.Fil a := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      apply ih
      have hx' : x ∈ PD.Fil (a + n + 1) := by
        have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
        rwa [e] at hx
      exact PD.Fil_anti (a + n) hx'
  intro a
  rcases le_or_gt a 1 with h | h
  · have e : (1 : ℤ) = a + ((1 - a).toNat : ℕ) := by omega
    have := hle a (1 - a).toNat
    rw [← e] at this
    exact this h1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) + 1 := ⟨(a - 1).toNat, by omega⟩
    rw [hn]; exact hpos n

theorem field_inter_filtration_one_eq_zero (c : K) (hc : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hne
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ hc
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one] at this
  have hall := inv_one_mem_all PD h1
  have h0 : (1 : BdR) = 0 := PD.Fil_sep 1 hall
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by
    rw [← one_mul (PD.ι PD.t), h0, zero_mul]
  rw [this]
  exact (PD.Fil 2).zero_mem

def invPsi (φ : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift ((LinearMap.lsmul Qp BdR).compl₁₂ φ LinearMap.id)

end Inv

end Formalism.MainNotions.N.JsetEmb

end
