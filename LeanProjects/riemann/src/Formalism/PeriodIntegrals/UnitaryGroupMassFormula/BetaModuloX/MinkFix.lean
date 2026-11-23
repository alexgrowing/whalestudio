import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MapEqOfIff
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet

noncomputable section

open scoped Classical

open NumberField Module

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q4

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Type} [AddCommGroup Q] [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]

theorem mink_fix (L : Submodule (𝓞 E) Q) (hL : L.FG) (φ : Q →ₗ[E] Q) (hφL : ∀ x ∈ L, φ x ∈ L)
    (n : ℕ) (hn : 0 < n) (hpow : ∀ x, φ^[n] x = x) (g : ℕ) (hg : 3 ≤ g)
    (hcong : ∀ x ∈ L, ∃ y ∈ L, φ x - x = g • y) : ∀ x ∈ L, φ x = x := by
  have hfinO : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have hfinZ : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have := Formalism.HermitianLatticesTheory.isAddTorsionFree_ringOfIntegers_submodule (K := E) L
  have hfree : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ψ : L →ₗ[ℤ] L :=
    (((φ.restrictScalars (𝓞 E)).restrict hφL : L →ₗ[𝓞 E] L) : L →+ L).toIntLinearMap
  have hψ : ∀ x : L, (ψ x : Q) = φ x := fun x => rfl
  have hiter : ∀ (k : ℕ) (x : L), ((ψ^[k] x : L) : Q) = φ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hψ, ih]
  have hψn : ψ ^ n = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [Module.End.pow_apply, hiter, hpow]
    rfl
  have hc : ∀ x : L, ∃ y : L, ψ x - x = (g : ℤ) • y := by
    intro x
    obtain ⟨y, hy, h⟩ := hcong x x.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_sub, hψ, h, Submodule.coe_smul_of_tower, natCast_zsmul]
  choose yf hyf using hc
  let b := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ L))
  let A := LinearMap.toMatrixAlgEquiv b ψ
  let B : Matrix (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L)))
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L))) ℤ :=
    Matrix.of fun i j => b.repr (yf (b j)) i
  have hAn : A ^ n = 1 := by
    show (LinearMap.toMatrixAlgEquiv b ψ) ^ n = 1
    rw [← map_pow, hψn, map_one]
  have hAB : A = 1 + (g : ℤ) • B := by
    ext i j
    show (LinearMap.toMatrixAlgEquiv b ψ) i j = _
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have h := hyf (b j)
    rw [sub_eq_iff_eq_add'] at h
    rw [h, map_add, map_zsmul, Finsupp.add_apply, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    simp [B, Matrix.one_apply, eq_comm]
  have hA1 := Formalism.HermitianLatticeCounting.P.finite_order_congruence _ n (g : ℤ) A B (by exact_mod_cast hg) hn hAn hAB
  have hψ1 : ψ = 1 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact hA1
  intro x hx
  have := congrArg (fun f : L →ₗ[ℤ] L => ((f ⟨x, hx⟩ : L) : Q)) hψ1
  simpa [hψ] using this

end Q4

end PI.UnitaryGroupMassFormula.BetaModX
