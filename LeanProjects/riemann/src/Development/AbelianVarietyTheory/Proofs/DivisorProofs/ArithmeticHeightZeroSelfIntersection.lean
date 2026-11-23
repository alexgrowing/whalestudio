import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HermLB GlobalTheory.ArInt

namespace GlobalTheory.CurveDegZero

theorem isSelfInter_zero : GlobalTheory.Published.CycleHeights → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (M : HermLB (spMap (algebraMap k k'))), IsArithVar (spMap (algebraMap k k')) 0 →
    ∀ (h : X → ℝ) (x : X), (M.pull ρ hρ).IsArithHeight h → ArInt.IsAlgPt x → h x = 0 → M.IsSelfInter 0 := by
  intro H k _ X p D hX k' _ _ _ ρ hρ M hk' h x hh hx hx0
  have := hX.isIntegral
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hc1 : CharZero (X.residueField (j (genericPoint W))) := hx.1
  have hcW : CharZero (W.residueField (genericPoint W)) :=
    (RingHom.charZero_iff (j.residueFieldMap (genericPoint W)).hom.injective).1 hc1
  have hc : CharZero Γ(W, ⊤) := (W.Γevaluation (genericPoint W)).hom.charZero
  have hr : Set.range j = closure {j (genericPoint W)} := by
    have h₁ := (genericPoint_spec W).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  have hd : topologicalKrullDim W = ((0 : ℕ) + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hr).symm.trans hx.2
  have hW : IsArithVar (j ≫ p) 0 := hX.of_isClosedImmersion j hc hd
  have hgen : ρ (j (genericPoint W)) = genericPoint (Sp k') :=
    SmallSecHeight.eq_genericPoint hk' (ρ.residueFieldMap (j (genericPoint W))).hom.charZero
  have hd' : topologicalKrullDim (closure ({ρ (j (genericPoint W))} : Set (Sp k'))) = ((0 : ℕ) + 1 : ℕ) := by
    rw [hgen, (genericPoint_spec (Sp k')).def]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans hk'.dim_eq
  have hNF : NumberField (W.residueField (genericPoint W)) := SmallSecHeight.numberField hW hcW
  have hm : ρ.residueDegree (j (genericPoint W)) ≠ 0 := by
    have e : (j ≫ ρ).residueDegree (genericPoint W) = ρ.residueDegree (j (genericPoint W)) := by
      rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one]
    rw [← e, PullbackFinitePoint.residueDegree_ne_zero_iff_finite]
    have : CharZero ((Sp k').residueField ((j ≫ ρ) (genericPoint W))) :=
      ((j ≫ ρ).residueFieldMap (genericPoint W)).hom.charZero
    letI := ((j ≫ ρ).residueFieldMap (genericPoint W)).hom.toAlgebra
    change Module.Finite _ _
    exact Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨h₀, hh₀, -⟩ := H.existsUnique hk' M
  have e := H.height_pull hk' hX ρ hρ hh₀ hh j hc hd hd' hm
  rw [hx0, eq_comm, mul_eq_zero] at e
  refine ⟨h₀, hh₀, ?_⟩
  rw [← hgen]
  exact e.resolve_left (by exact_mod_cast hm)

end GlobalTheory.CurveDegZero
