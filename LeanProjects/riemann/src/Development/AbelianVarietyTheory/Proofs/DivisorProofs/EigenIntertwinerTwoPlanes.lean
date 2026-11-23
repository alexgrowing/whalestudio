import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformCardEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRingEmbeddingRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRingOverPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionDerivativeGlueCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueZeroEqExtZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityOfReciprocityStatement

noncomputable section

namespace GlobalTheory.ThK.PlaneCo

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem exists_ev_isoB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoB H H') e := by
  intro _ F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  obtain ⟨eq⟩ : Nonempty (Fin n × Fin d ≃ Kc F E d₁ n₁ ⊕ Fin n₁ × Fin d₁) :=
    Fintype.card_eq.mp (GlobalTheory.T.plane_transform_card_eq σ B X W X₁ W₁ H H' hB hH hH')
  let T := LinearEquiv.ofBijective (planeT σ X W H H') (GlobalTheory.T.plane_transform_bijective σ B X W X₁ W₁ H H' hB hX hW hH hH')
  have hT : ∀ u, T u = planeT σ X W H H' u := fun u => rfl
  have hf : ∀ w w', symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (T w).2 (T w').2 :=
    GlobalTheory.T.plane_transform_symplectic σ B X W X₁ W₁ H H' hB hX hW hH hH'
  let Ma : Model σ X W := Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) M.μ M.dom
  have hS := GlobalTheory.T.vacuum_schwartz_bruhat σ B X W X₁ W₁ H H' hB hX hW hH hH'
  have h0 : ∀ v, vacS σ X W H H' v 0 = 1 := fun v => by
    have hm : (0 : Kc F E d₁ n₁ → Fv F v) ∈ latS σ X W H H' v :=
      ⟨0, (latAtV X W v).zero_mem, fun k => by simp⟩
    simp only [vacS, Set.indicator_of_mem hm, Pi.one_apply]
  refine ⟨Ma, restr eq, ⟨fun x => ?_, fun v => ?_, ?_, hM.haar, hM.dom⟩,
    GlobalTheory.T.adapted_evaluation_block_transform σ B X W X₁ W₁ H.ι H'.ι (isoB H H') M₁ eq T hf (vacS σ X W H H') M.μ M.dom
      (fun z => by rw [hT]; exact GlobalTheory.T.lagrangian_invariant_functional_unique σ B X W X₁ W₁ H H' hB hX hW hH hH' z)
      (fun u hu => by rw [hT]; exact GlobalTheory.T.comparison_readable_at_place σ B X W X₁ W₁ H H' hB hX hW hH hH' u hu)
      (fun v => ⟨hS v, h0 v⟩) (fun v => (hM₁.vac v).1)⟩
  · obtain ⟨⟨y, z, hyz⟩, x₁, hx₁⟩ := GlobalTheory.T.plane_transform_rational_points σ X W H H' x
    obtain ⟨y₁, z₁, h₁⟩ := hM₁.rat x₁
    refine ⟨glue eq y y₁, glue eq z z₁, ?_⟩
    show (glueDarboux M₁.co eq T hf).e (incM F x) = _
    rw [glueDarboux_e, hT, hx₁, h₁, hyz]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp only [glue] <;> rcases eq k with k' | k' <;> rfl
  · exact GlobalTheory.T.evaluation_adapted_good_model σ B X W X₁ W₁ H H' M₁ hB hX hW hH hH' hM₁ eq T hT hf M.μ M.dom v
  · filter_upwards [GlobalTheory.T.vacuum_unramified_almost_all σ B X W X₁ W₁ H H' hB hX hW hH hH', hM₁.std] with v hv hv₁
    show vacGlue eq (vacS σ X W H H' v) (M₁.vac v) = _
    rw [hv, hv₁]
    exact vacGlue_indicator eq _

end GlobalTheory.ThK.PlaneCo

end
