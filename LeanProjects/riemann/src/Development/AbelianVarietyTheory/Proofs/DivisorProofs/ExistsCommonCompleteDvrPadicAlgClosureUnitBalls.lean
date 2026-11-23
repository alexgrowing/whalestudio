import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UnifField

open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

variable {p : ℕ} [Fact p.Prime]

theorem exists_field (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Algebra (FractionRing V) (PadicAlgCl p)] (hc : IsAdicComplete (maximalIdeal V) V)
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      (K : Set (PadicAlgCl p)) = Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) := by
  haveI := hc
  obtain ⟨K, hK, e⟩ := GlobalTheory.ZH.FieldOfTest.exists_finiteDimensional_of_isComplete p
    (algebraMap (FractionRing V) (PadicAlgCl p)).fieldRange
    (by rw [RingHom.coe_fieldRange]; exact GlobalTheory.ZH.FieldOfTest.isComplete_range_fractionRing V (PadicAlgCl p) hn)
  exact ⟨K, hK, by rw [e, RingHom.coe_fieldRange]⟩

def secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K →+* FractionRing (intRing K) :=
  (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm.toRingHom

theorem comp_secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp (secK K) = algebraMap K (PadicAlgCl p) := by
  have h : algebraMap (FractionRing (intRing K)) (PadicAlgCl p) = (algebraMap K (PadicAlgCl p)).comp
      (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (intRing K)) (RingHom.ext fun w => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (intRing_injective K) w).trans ?_
    have := (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).commutes w
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_coe, this]
    rfl
  rw [h, RingHom.comp_assoc]
  ext x
  show algebraMap K (PadicAlgCl p) ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K)
    ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem exists_map (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V)))
    (hK : Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) ⊆ K) :
    ∃ (φ : V →+* intRing K) (φK : FractionRing V →+* FractionRing (intRing K)),
      φK.comp (algebraMap V _) = (algebraMap (intRing K) _).comp φ ∧
      (maximalIdeal V).map φ ≤ maximalIdeal (intRing K) ∧
      (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp φK =
        algebraMap (FractionRing V) (PadicAlgCl p) := by
  let jF := algebraMap (FractionRing V) (PadicAlgCl p)
  let ρK : FractionRing V →+* K := jF.codRestrict K (fun x => hK ⟨x, rfl⟩)
  have hle : ∀ v : V, ‖jF (algebraMap V _ v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  let φ : V →+* intRing K := (ρK.comp (algebraMap V (FractionRing V))).codRestrict (intRing K) (fun v => by
    rw [ValuationSubring.mem_comap, mem_OO_iff]
    exact hle v)
  have h3 : (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp ((secK K).comp ρK) = jF := by
    rw [← RingHom.comp_assoc, comp_secK]
    rfl
  refine ⟨φ, (secK K).comp ρK, ?_, ?_, h3⟩
  · refine RingHom.ext fun v => (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).injective ?_
    have e1 := RingHom.congr_fun h3 (algebraMap V _ v)
    simp only [RingHom.comp_apply] at e1 ⊢
    rw [e1]
    exact ((IsFractionRing.lift_algebraMap (intRing_injective K) (φ v)).trans rfl).symm
  · refine Ideal.map_le_iff_le_comap.2 fun m hm => ?_
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine (IsLocalRing.mem_maximalIdeal _).1 hm ?_
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : jF (algebraMap V _ m) * ((y : K) : PadicAlgCl p) = 1 := by
      have := congrArg (fun w : intRing K => ((w : K) : PadicAlgCl p)) hy
      simpa [φ, ρK] using this
    have h2 : ((y : K) : PadicAlgCl p) = jF (algebraMap V _ m)⁻¹ := by
      rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
    have hy1 : ‖((y : K) : PadicAlgCl p)‖ ≤ 1 := by
      have := y.2
      rw [ValuationSubring.mem_comap, mem_OO_iff] at this
      exact this
    obtain ⟨z, hz⟩ := (hn (algebraMap V _ m)⁻¹).1 (h2 ▸ hy1)
    have h0 : algebraMap V (FractionRing V) m ≠ 0 := fun h => by simp [h] at h1
    refine IsUnit.of_mul_eq_one z (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]

end GlobalTheory.UnifField
end

noncomputable section
namespace GlobalTheory.UnifField
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

theorem exists_common_ring : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  intro p _ V V' _ _ _ _ _ _ _ _ hc hc' hn hn' s
  obtain ⟨K₁, h₁, e₁⟩ := exists_field V hc hn
  obtain ⟨K₂, h₂, e₂⟩ := exists_field V' hc' hn'
  let K₃ := IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))
  have h₃ : FiniteDimensional ℚ_[p] K₃ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let K := K₁ ⊔ K₂ ⊔ K₃
  have hK : FiniteDimensional ℚ_[p] K := inferInstance
  obtain ⟨hdvr, hcW, hnW⟩ := GlobalTheory.T.padicIntermediateFieldIntRing_complete_dvr p K hK
  have l₁ : K₁ ≤ K := le_sup_left.trans le_sup_left
  have l₂ : K₂ ≤ K := le_sup_right.trans le_sup_left
  have l₃ : K₃ ≤ K := le_sup_right
  refine ⟨intRing K, inferInstance, inferInstance, hdvr, fracAlgebra K, hcW, hnW, ?_, ?_,
    exists_map K V (fun x => hn x) (fun x hx => l₁ (show x ∈ (K₁ : Set (PadicAlgCl p)) by rw [e₁]; exact hx)),
    exists_map K V' (fun x => hn' x) (fun x hx => l₂ (show x ∈ (K₂ : Set (PadicAlgCl p)) by rw [e₂]; exact hx))⟩
  · intro x hx
    have hxK : x ∈ K := l₃ (IntermediateField.subset_adjoin ℚ_[p] _ hx)
    exact ⟨secK K ⟨x, hxK⟩, (RingHom.congr_fun (comp_secK K) ⟨x, hxK⟩).trans rfl⟩
  · intro z
    have hz : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
    refine ⟨(minpoly ℚ_[p] z).map ((secK K).comp (algebraMap ℚ_[p] K)),
      Polynomial.map_ne_zero (minpoly.ne_zero hz), ?_⟩
    rw [Polynomial.eval₂_map, ← RingHom.comp_assoc, comp_secK, ← IsScalarTower.algebraMap_eq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[p] z

end GlobalTheory.UnifField
end
