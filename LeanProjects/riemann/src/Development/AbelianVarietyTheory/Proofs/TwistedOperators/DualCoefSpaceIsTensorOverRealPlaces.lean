import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnitaStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefTensorProof

theorem coefTensor : CoefTensor := by
  intro D V θ c hθ hc
  classical
  haveI : Nontrivial c.W := hc.2.2.2.1
  haveI : Nontrivial (Module.Dual ℂ c.W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  let a : ∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.UH (gramAt D V τ) → Module.End ℂ (Module.Dual ℂ c.W) :=
    fun τ g => (c.ρ (atTau θ V τ g.1)⁻¹).dualMap
  have ha : ∀ τ (g : Formalism.QuantumDeterminants.UH (gramAt D V τ)) f, a τ g f = f ∘ₗ c.ρ (atTau θ V τ g.1)⁻¹ := fun _ _ _ => rfl
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g h, a τ g * a τ' h = a τ' h * a τ g := by
    intro τ τ' hne g h
    have hc' := GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne g.1 g.2 h.1 h.2
    ext f w
    simp only [Module.End.mul_apply, ha, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (c.ρ _), ← map_mul, ← Module.End.mul_apply (c.ρ _), ← map_mul, ← mul_inv_rev,
      ← mul_inv_rev, hc']
  have hirrD : ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ g, ∀ x ∈ N, a τ g x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces D V θ c hθ hc N fun τ g hg f hf => hN τ ⟨g, hg⟩ f hf
  obtain ⟨X, i1, i2, i3, b, m, e, hinj, hint, hirr, heq⟩ := GlobalTheory.T.exists_tensorDecomposition_commutingFamilies D.what₂.Tau (Module.Dual ℂ c.W) _ a hcomm hirrD
  have hone : ∀ τ, atTau θ V τ 1 = 1 := fun τ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  let π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (X τ) := fun τ g =>
    if hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then b τ ⟨g, hg⟩ else 1
  have hπ : ∀ τ g (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), π τ g = b τ ⟨g, hg⟩ := fun τ g hg => dif_pos hg
  refine ⟨X, i1, i2, i3, π, e, fun τ => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    rw [hπ τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)]
    ext x
    apply hinj τ
    rw [hint, ha]
    show m τ x ∘ₗ c.ρ (atTau θ V τ 1)⁻¹ = m τ x
    rw [hone, inv_one, map_one]
    rfl
  · intro g hg h hh
    rw [hπ τ _ (GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh), hπ τ g hg, hπ τ h hh]
    ext x
    apply hinj τ
    rw [Module.End.mul_apply, hint, hint, hint]
    ext w
    simp only [ha, LinearMap.comp_apply]
    rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hh, mul_inv_rev, map_mul, Module.End.mul_apply]
  · intro w l
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (m τ) (LinearMap.ker_eq_bot.2 (hinj τ))
    obtain ⟨v, hv⟩ : ∃ v : c.W, ∀ φ : Module.Dual ℂ c.W, (l ∘ₗ r) φ = φ v :=
      ⟨(Module.evalEquiv ℂ c.W).symm (l ∘ₗ r), fun φ => by
        conv_lhs => rw [← (Module.evalEquiv ℂ c.W).apply_symm_apply (l ∘ₗ r)]
        rfl⟩
    refine (GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary D V θ c hθ hc τ (m τ w) v).congr fun g hg => ?_
    show l (π τ g w) = _
    rw [hπ τ g hg]
    have : l (b τ ⟨g, hg⟩ w) = (l ∘ₗ r) (m τ (b τ ⟨g, hg⟩ w)) := by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply r, hr, LinearMap.id_apply]
    rw [this, hv, hint, ha, LinearMap.comp_apply]
  · intro U hU
    exact hirr τ U fun g x hx => by rw [← hπ τ g.1 g.2]; exact hU g.1 g.2 x hx
  · intro τ g hg x y hy hy'
    have : y = Function.update x τ (b τ ⟨g, hg⟩ (x τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h; rw [Function.update_self, hy, hπ _ g hg]
      · rw [Function.update_of_ne h, hy' τ' h]
    rw [this, heq]
    rfl

end GlobalTheory.CoefTensorProof
