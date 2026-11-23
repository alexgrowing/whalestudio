import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem cont_ev {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {Ξ : AlgRep E a}
    {m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)}
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : Continuous (ev m) := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | finRep E a k φ = φ}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : finRep E a x φ = φ := hx
          have hy' : finRep E a y φ = φ := hy
          change finRep E a (x * y) φ = φ
          rw [map_mul, Module.End.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : finRep E a x φ = φ := hx
          change finRep E a x⁻¹ φ = φ
          conv_lhs => rw [← hx']
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (H₁ := U) (fun u hu => hφ.2.1 u hu) hU
    exact (ContAut.continuous_of_isOpen_stab E a φ hS).smul continuous_const
  | zero => rw [map_zero]; exact continuous_const
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

theorem UpperTheory.V.Lit.Geo.bdCompact :
    BdCompact := by
  intro E _ _ _ a U hU Ξ q α hα R
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  obtain ⟨K, hK, hR⟩ := (qhtFacts E a).2.2.2 R
  have hb : ∀ X : Fin q → Herm E a, ∃ c : ℝ, ∀ g ∈ K, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ c := fun X =>
    hK.exists_bound_of_continuousOn
      ((cont_ev hU (hα.val X)).comp (continuous_subtype_val.comp continuous_retractOne)).continuousOn
  choose c hc using hb
  refine ⟨B * ∑ X ∈ T, |c X|, by positivity, fun g hg => hT α g _ (by positivity) fun X hX => ?_⟩
  obtain ⟨γ, t, h⟩ := hR g hg
  have e := hc X _ h
  rw [(retrFacts E a).2.1, ((levelVal E a U Ξ _).1 (hα.val X)).1] at e
  exact (e.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun X => |c X|) (fun _ _ => abs_nonneg _) hX)
