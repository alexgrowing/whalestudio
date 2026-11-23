import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.NilLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.unipPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → InPow 1 ((g - 1) ^ R) := by
  intro l _ X _ _ R g hgen hu
  obtain ⟨N, hN⟩ := hu
  let p : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have memp : ∀ v : X, v ∈ p ↔ ∃ y, v = (l : ℤ_[l]) ^ 1 • y := by
    intro v
    simp only [p, LinearMap.mem_range, LinearMap.smul_apply, Module.End.one_apply, pow_one]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  have hp : p ≤ p.comap (g - 1) := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memp v).mp hv
    rw [Submodule.mem_comap, map_smul]
    exact (memp _).mpr ⟨(g - 1) y, rfl⟩
  let F : Module.End ℤ_[l] (X ⧸ p) := p.mapQ p (g - 1) hp
  have hFx : ∀ x : X, F (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((g - 1) x) :=
    fun x => Submodule.mapQ_apply _ _ _ x
  have key : ∀ (k : ℕ) (x : X), (F ^ k) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (((g - 1) ^ k) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hFx, ih, pow_succ, Module.End.mul_apply]
  have hnil : IsNilpotent F := by
    refine ⟨N, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p z
    rw [Submodule.mkQ_apply, key, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, memp]
    exact hN x
  have hlen : Module.length ℤ_[l] (X ⧸ p) ≤ R := cokL l X R hgen
  have hF0 := nilLen ℤ_[l] (X ⧸ p) F R hnil hlen
  intro x
  have hk := key R x
  rw [hF0, LinearMap.zero_apply, eq_comm, Submodule.Quotient.mk_eq_zero, memp] at hk
  exact hk
