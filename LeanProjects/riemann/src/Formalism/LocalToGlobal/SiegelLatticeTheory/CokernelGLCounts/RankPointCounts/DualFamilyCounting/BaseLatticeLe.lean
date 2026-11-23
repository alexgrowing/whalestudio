import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FinrankSpanLb
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt

noncomputable section

open NumberField Formalism.BasicNotions
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas.IntG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem base_lattice_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]
  exact le_sup_of_le_left le_sup_right

theorem Lb_le_aaLbS (b : Fin D.R.rS) : X.Lb ≤ aaLbS X b := fun l hl =>
  Submodule.subset_span ⟨1, one_mem_aaD b, l, hl, by rw [one_smul]⟩

theorem aaLbS_le_span (b : Fin D.R.rS) :
    aaLbS X b ≤ (Submodule.span D.host.E (X.Lb : Set (VS D).V)).restrictScalars (𝓞 D.host.E) := by
  unfold aaLbS
  rw [Submodule.span_le]
  rintro _ ⟨c, -, l, hl, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.subset_span hl)

theorem span_aaLbS (b : Fin D.R.rS) :
    Submodule.span D.host.E (aaLbS X b : Set (VS D).V) = Submodule.span D.host.E (X.Lb : Set (VS D).V) :=
  le_antisymm (Submodule.span_le.2 (aaLbS_le_span X b)) (Submodule.span_mono (Lb_le_aaLbS X b))

theorem aaD_ne_zero' (b : Fin D.R.rS) : aaD D b ≠ 0 := by
  unfold aaD
  exact zpow_ne_zero _ ddS_ne_zero

theorem fg_aaLbS (b : Fin D.R.rS) : (aaLbS X b).FG := by
  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ (D.R.rS - (b : ℕ)) with hNdef
  have hN : ((N : ℕ) : D.host.E) ∈ (aaD D b)⁻¹ := mem_aaD_inv b
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  let f : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (N : 𝓞 D.host.E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((N : 𝓞 D.host.E) : D.host.E) • x = ((N : 𝓞 D.host.E) : D.host.E) • y := by
      rw [algebraMap_smul, algebraMap_smul]
      exact hxy
    have h2 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      push_cast
      exact_mod_cast hN0
    exact smul_right_injective _ h2 h1
  have hle : (aaLbS X b).map f ≤ (VS D).L0 := by
    unfold aaLbS
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨c, hc, l, hl, rfl⟩, rfl⟩
    have hmul : ((N : ℕ) : D.host.E) * c ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E) := by
      have := FractionalIdeal.mul_mem_mul hN hc
      rwa [inv_mul_cancel₀ (aaD_ne_zero' b)] at this
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    have e : f (c • l) = o • l := by
      show (N : 𝓞 D.host.E) • (c • l) = o • l
      rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E), smul_smul, ← algebraMap_smul D.host.E o l, ho]
      push_cast
      rfl
    rw [e]
    exact base_lattice_le X (X.Lb.smul_mem o hl)
  haveI : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_fg_of_noetherian _ (VS D).standardTuple_isLattice.fg
  have hfg : ((aaLbS X b).map f).FG := (isNoetherian_submodule.1 inferInstance) _ hle
  exact Submodule.fg_of_fg_map_injective f hf hfg

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
