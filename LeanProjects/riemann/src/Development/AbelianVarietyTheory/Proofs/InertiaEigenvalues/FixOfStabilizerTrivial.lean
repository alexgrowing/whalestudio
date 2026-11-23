import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypeDegOne

theorem fix_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (c : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ P ↔ ‖c (x : E)‖ < 1)
    (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : E) :
    τ (c x) = c x := by
  letI : Algebra E (PadicAlgCl l) := c.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := ((τ : PadicAlgCl l →+* PadicAlgCl l).comp c).toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, c (σ y) = τ (c y) := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc, hc]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    have hn : ‖τ (c y)‖ = ‖c y‖ := (spectralNorm_eq_of_equiv τ _).symm
    rw [e, hσ, hn]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  rw [← hσ, h2]
  rfl

theorem eq_bot_of_subset_closure {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (S : Set (PadicAlgCl l)) (hK : (K : Set (PadicAlgCl l)) ⊆ closure S)
    (hS : ∀ (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ y ∈ S, τ y = y) : K = ⊥ := by
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := IsAlgClosure.isGalois _ _
  refine eq_bot_iff.2 fun y hy => (InfiniteGalois.mem_bot_iff_fixed y).2 fun τ => ?_
  have hc : Continuous τ :=
    (AddMonoidHomClass.isometry_of_norm τ fun x => (spectralNorm_eq_of_equiv τ x).symm).continuous
  exact closure_minimal (hS τ) (isClosed_eq hc continuous_id) (hK hy)

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem degree_one : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧ ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨?_, fun w hw => ?_⟩
  · have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [hs, h1, h5]; ring
  · have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w hw).2.2
    have hb : (D.nbr i w hw).Kw.1 = ⊥ := by
      refine eq_bot_of_subset_closure _ _ (D.nbr i w hw).j_dense ?_
      rintro τ _ ⟨x, rfl⟩
      exact fix_of_stabilizer_trivial ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) w.asIdeal
        (mem_place_iff D i w hw) hP τ x
    exact IntermediateField.finrank_eq_one_iff.2 hb

end GlobalTheory.TypeDegOne

end
