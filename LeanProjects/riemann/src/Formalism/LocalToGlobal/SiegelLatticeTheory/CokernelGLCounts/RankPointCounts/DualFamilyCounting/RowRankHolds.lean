import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BaseLatticeLe
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

open NumberField Formalism.BasicNotions Module
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem rowRank_holds : RowRank := by
  intro D X b
  set S := Submodule.span D.host.E (aaLbS X b : Set (VS D).V) with hSdef
  have hSfin : finrank D.host.E S = D.R.k + 1 := by
    rw [hSdef, span_aaLbS, finrank_span_Lb]
  have hSle : ∀ x ∈ aaLbS X b, x ∈ S := fun x hx => Submodule.subset_span hx
  let B : Basis (Fin (D.R.k + 1)) D.host.E S := Module.finBasisOfFinrankEq D.host.E S hSfin
  let eS : S ≃ₗ[D.host.E] (Fin (D.R.k + 1) → D.host.E) := B.equivFun
  let Φ : (Fin (D.R.k + 1) → D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
    (S.subtype.comp eS.symm.toLinearMap).restrictScalars (𝓞 D.host.E)
  have hΦ : ∀ y, Φ y = ((eS.symm y : S) : (VS D).V) := fun y => rfl
  have hΦinj : Function.Injective Φ := by
    intro y y' h
    rw [hΦ, hΦ] at h
    exact eS.symm.injective (Subtype.ext h)
  let A : Submodule (𝓞 D.host.E) (Fin (D.R.k + 1) → D.host.E) := (aaLbS X b).comap Φ
  have hmemA : ∀ y, y ∈ A ↔ Φ y ∈ aaLbS X b := fun y => Iff.rfl

  have hmap : A.map Φ = aaLbS X b := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun x hx => ?_
    refine ⟨eS ⟨x, hSle x hx⟩, ?_, ?_⟩
    · show Φ (eS ⟨x, hSle x hx⟩) ∈ aaLbS X b
      rw [hΦ, LinearEquiv.symm_apply_apply]
      exact hx
    · show Φ (eS ⟨x, hSle x hx⟩) = x
      rw [hΦ, LinearEquiv.symm_apply_apply]
  have hAfg : A.FG := Submodule.fg_of_fg_map_injective Φ hΦinj (by rw [hmap]; exact fg_aaLbS X b)

  have hAspan : Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have key : ∀ (v : (VS D).V) (hv : v ∈ S), eS ⟨v, hv⟩ ∈ Submodule.span D.host.E (A : Set _) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        show Φ (eS ⟨x, _⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact hx
      | zero =>
        have : eS ⟨0, S.zero_mem⟩ = 0 := by
          rw [show (⟨0, S.zero_mem⟩ : S) = 0 from rfl, map_zero]
        rw [this]
        exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
        have : eS ⟨x + y, S.add_mem hx hy⟩ = eS ⟨x, hx⟩ + eS ⟨y, hy⟩ := by
          rw [← map_add]; rfl
        rw [this]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ihx =>
        have : eS ⟨c • x, S.smul_mem c hx⟩ = c • eS ⟨x, hx⟩ := by
          rw [← map_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ c ihx
    have := key _ (eS.symm y).2
    rwa [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at this

  let Az : Submodule ℤ (Fin (D.R.k + 1) → D.host.E) := A.restrictScalars ℤ
  have h1 : Module.Finite (𝓞 D.host.E) A := Module.Finite.iff_fg.2 hAfg
  have h2 : Module.Finite ℤ A := Module.Finite.trans (𝓞 D.host.E) _
  have h3 : Module.Finite ℤ Az :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) _ A).restrictScalars ℤ).symm
  have hlat : Submodule.IsLattice ℚ Az := by
    refine ⟨Module.Finite.iff_fg.1 h3, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) := by rw [hAspan]; trivial
    obtain ⟨n, hn, hnx⟩ := Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem A hx
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)
  have hr : finrank ℤ Az = finrank ℚ (Fin (D.R.k + 1) → D.host.E) :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' ℚ Az).trans (Module.finrank_eq_rank ℚ (Fin (D.R.k + 1) → D.host.E)).symm)
  let bZ : Basis (Fin (finrank ℚ (Fin (D.R.k + 1) → D.host.E))) ℤ Az := Module.finBasisOfFinrankEq ℤ Az hr
  have hdim : finrank ℚ (Fin (D.R.k + 1) → D.host.E) = finrank ℚ D.host.E * (D.R.k + 1) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

  let eqv : Az ≃ₗ[ℤ] ((aaLbS X b).restrictScalars ℤ) :=
    { toFun := fun y => ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), (hmemA _).1 y.2⟩
      invFun := fun x => ⟨eS ⟨x, hSle x x.2⟩, by
        show Φ (eS ⟨x, hSle x x.2⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact x.2⟩
      map_add' := fun y y' => Subtype.ext (map_add Φ (y : Fin (D.R.k + 1) → D.host.E) y')
      map_smul' := fun c y => Subtype.ext (by
        show Φ (c • (y : Fin (D.R.k + 1) → D.host.E)) = c • Φ (y : Fin (D.R.k + 1) → D.host.E)
        exact map_zsmul Φ c _)
      left_inv := fun y => Subtype.ext (by
        show eS ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), _⟩ = (y : Fin (D.R.k + 1) → D.host.E)
        have : (⟨Φ (y : Fin (D.R.k + 1) → D.host.E), hSle _ ((hmemA _).1 y.2)⟩ : S) = eS.symm y := Subtype.ext (hΦ _)
        rw [this, LinearEquiv.apply_symm_apply])
      right_inv := fun x => Subtype.ext (by
        show Φ (eS ⟨x, _⟩) = (x : (VS D).V)
        rw [hΦ, LinearEquiv.symm_apply_apply]) }
  exact ⟨(bZ.map eqv).reindex (finCongr hdim)⟩

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
