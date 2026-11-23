import Formalism.LocalToGlobal.GroupLattices.JointServices
import Formalism.LocalToGlobal.Divisibility.Inputs
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LocalizationStructureHolds

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Indef Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.G.ServJoint

variable {D : D7}

def sgFl (L : SizeData₂ D) (u : D.what₂.Word) (z : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℝ :=
  ((⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ : ℤ) : ℝ)

theorem sg_off (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : w ∉ L.supp) : L.sg u w = 0 := by
  unfold SizeData₂.sg
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : L.gain j w = 0 := L.gain_supp j w hw
  have h2 := L.F_supp j w hw
  have h3 := L.E_supp u j w hw
  simp [SizeData₂.gainD, h1, h2, h3]

theorem shiftZ_sgFl (L : SizeData₂ D) (u : D.what₂.Word) (z : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    shiftZ (sgFl L u) z = ⌊ur D (D.plEq.symm z) (L.sg u (D.plEq.symm z))⌋ := by
  first
  | rfl
  | (simp [shiftZ, sgFl])
  | (unfold shiftZ sgFl; simp)

theorem shiftIdeal_sgFl (L : SizeData₂ D) (u : D.what₂.Word) : Formalism.DivisionValues.shiftIdeal (shiftZ (sgFl L u)) = Iu D L u := by
  unfold Formalism.DivisionValues.shiftIdeal Iu
  rw [finprod_eq_prod_of_mulSupport_subset (s := L.supp.map D.plEq.toEmbedding)]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [shiftZ_sgFl]
  · intro z hz
    rw [Function.mem_mulSupport] at hz
    rw [Finset.coe_map, Set.mem_image]
    refine ⟨D.plEq.symm z, ?_, by simp⟩
    by_contra h
    apply hz
    rw [shiftZ_sgFl, sg_off L u _ h]
    simp [ur]

theorem Iu_ne_zero (L : SizeData₂ D) (u : D.what₂.Word) : Iu D L u ≠ 0 := by
  unfold Iu
  rw [Finset.prod_ne_zero_iff]
  intro x _
  apply zpow_ne_zero
  first
  | exact FractionalIdeal.coeIdeal_ne_zero.mpr (D.plEq x).ne_bot
  | exact (FractionalIdeal.coeIdeal_ne_zero).2 (HeightOneSpectrum.ne_bot _)
  | simp [(D.plEq x).ne_bot]

theorem nu_map_eq (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC Nu : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L = NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)))
    (hshift : NuC = shiftLat Nu (sgFl L u)) :
    Nu.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) = L.NuLat u := by
  set f := ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) with hf

  have hmap : ∀ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (N : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL)),
      (Formalism.HermitianLatticesTheory.idealSmul I N).map f = Formalism.HermitianLatticesTheory.idealSmul I (N.map f) := by
    intro I N
    unfold Formalism.HermitianLatticesTheory.idealSmul
    rw [Submodule.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, f x, Submodule.mem_map_of_mem hx, by simp [hf]⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp [hf]⟩
  have hN' : (D.div.Nu u).L = Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (L.NuLat u) := by
    rw [hN u]
    rfl
  have h1 : Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (Nu.map f) =
      Formalism.HermitianLatticesTheory.idealSmul (Iu D L u : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (L.NuLat u) := by
    rw [← hmap, ← hN', hlat, hshift, shiftLat, shiftIdeal_sgFl]
  have hIu : Iu D L u ≠ 0 := Iu_ne_zero L u
  have hone : ∀ X : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V,
      Formalism.HermitianLatticesTheory.idealSmul ((((Iu D L u)⁻¹ * Iu D L u : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL)) :
        Submodule (𝓞 D.what₂.LL) D.what₂.LL) X = X := by
    intro X
    rw [inv_mul_cancel₀ hIu, FractionalIdeal.coe_one, Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_one]
  rw [← hone (Nu.map f), ← hone (L.NuLat u), FractionalIdeal.coe_mul, Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_mul,
    Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_mul, h1]

theorem nu_into (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC Nu : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L = NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)))
    (hshift : NuC = shiftLat Nu (sgFl L u)) : ∀ x ∈ Nu, e x ∈ L.NuLat u := by
  intro x hx
  rw [← nu_map_eq L hN u e NuC Nu hlat hshift]
  exact Submodule.mem_map_of_mem hx

end Formalism.L2.G.ServJoint

end
