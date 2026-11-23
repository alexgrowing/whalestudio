import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem surjective_of_range_sup_smul_top_eq_top (R : Type) [CommRing R] (M : Type 1)
    [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective f := by
  set S := LinearMap.range f

  have key : ∀ I : Ideal R, I.IsMaximal → ¬ Module.annihilator R (N ⧸ S) ≤ I := by
    intro I hI hle
    have hle' : (⊤ : Submodule R (N ⧸ S)) ≤ I • (⊤ : Submodule R (N ⧸ S)) := by
      have h1 := congrArg (Submodule.map S.mkQ) (h I hI)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
      have h2 : Submodule.map S.mkQ S = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        simpa [Submodule.mem_bot] using (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [h2, bot_sup_eq] at h1
      rw [h1]
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.Finite.fg_top) hle'
    have hrA : r ∈ Module.annihilator R (N ⧸ S) :=
      Module.mem_annihilator.mpr fun m => hr m trivial
    have hrI : r ∈ I := hle hrA
    have h1I : (1 : R) ∈ I := by
      have := I.sub_mem hrI hr1
      simpa using this
    exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h1I)
  have htop : Module.annihilator R (N ⧸ S) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    exact key I hI hle
  have hS : S = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ S) := htop ▸ Submodule.mem_top
    have h2 := Module.mem_annihilator.mp h1 (S.mkQ n)
    rw [one_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact LinearMap.range_eq_top.mp hS

example : ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] (f : M →ₗ[R] N), (∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) → Function.Surjective f := @surjective_of_range_sup_smul_top_eq_top

end GlobalTheory
