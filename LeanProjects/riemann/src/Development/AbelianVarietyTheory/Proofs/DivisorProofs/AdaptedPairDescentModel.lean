import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinRealisedUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticMemClosureGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxRationalBasisCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionAdaptedStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

theorem GlobalTheory.MixedModel.dbl_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), M.IsGood ψ →
  ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
  ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
    IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
  ∀ x : Matrix (Fin d) (Fin n ⊕ Fin n) E, ∃ u v : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
    dd.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i)) := by
  intro F E _ _ _ _ _ σ ψ n d X W M hM d' hd' dd hdd x
  have hx : incM F x = Matrix.fromCols (incM F (Matrix.toCols₁ x)) (incM F (Matrix.toCols₂ x)) := by
    ext i (j | j) <;> rfl
  have h1 : ∀ y : Matrix (Fin d) (Fin n) E, d'.e (incM F y) = M.co.e (incM F yᵀ) := fun y => by
    rw [← hd']; rfl
  obtain ⟨u₁, v₁, e₁⟩ := hM.rat (Matrix.toCols₁ x)ᵀ
  obtain ⟨u₂, v₂, e₂⟩ := hM.rat (Matrix.toCols₂ x)ᵀ
  refine ⟨Sum.elim u₁ u₂, Sum.elim v₁ (-v₂), ?_⟩
  rw [hx, hdd, h1, h1, e₁, e₂]
  ext (k | k) <;> simp

theorem GlobalTheory.MixedModel.mixed_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∃ (κa : Type) (_ : Fintype κa) (ε : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ κa ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)))
        (C : Matrix κa (Fin n) E)
        (S : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) ∧
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), S Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∃ l' ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l' Φ = l (S Φ)) ∧
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          (fun v => S (dd.rho B.ψ (incM F H'.ι * z) Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v)) =
            dd₁.rho B.ψ z (fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v))) ∧
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∀ v,
          S (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v) = S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v)) ∧
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), (fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v)) ≠ 0) ∧
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∀ v,
          S (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v) =
            S Φ (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁
  have hψ : IsStd B.ψ := hP.base.std
  have hr := GlobalTheory.MixedModel.dbl_rat F E σ B.ψ n d X W M hP.good d' hd' dd hdd
  have hr₁ := GlobalTheory.MixedModel.dbl_rat F E σ B.ψ n d₁ X W₁ M₁ hP₁.good d₁' hd₁' dd₁ hdd₁
  obtain ⟨κa, _, ε, C, dN, hNr, hC, hι, hx, hy⟩ := GlobalTheory.T.seesaw_pair_restriction_adapted F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H'
    i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd₁ hr₁
  have hcard : Fintype.card ((Fin n × Fin d) ⊕ (Fin n × Fin d)) * 2 =
      Fintype.card (Fin d) * Fintype.card (Fin n ⊕ Fin n) * Module.finrank F E := by
    rw [hP.base.cm.2.2.1]; simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; ring
  obtain ⟨g, hgs, hg⟩ := GlobalTheory.T.darboux_rational_basis_compatible F E (Fin d) (Fin n ⊕ Fin n) _ _ dd dN hcard hr hNr
  obtain ⟨S, hS, hSo, hSa, hSi⟩ := GlobalTheory.MixedModel.lin_realised F B.ψ hψ _ g (GlobalTheory.T.symplectic_mem_closure_generators F _ g hgs)
  have key : ∀ w, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), S (dd.rho B.ψ w Φ) = schr B.ψ (dN.e w) (S Φ) :=
    fun w Φ hΦ => by rw [Darboux.rho, hSi _ Φ hΦ, hg]
  refine ⟨κa, inferInstance, ε, C, S, hC, hS, hSa, ?_, ?_, ?_, ?_⟩
  · intro z Φ hΦ
    funext v
    rw [key _ Φ hΦ, hι z]
    simp only [Darboux.rho, schr, GlobalTheory.ThK.Adapt.glue_dot, GlobalTheory.ThK.Adapt.glue_add, zero_dotProduct, zero_add, add_zero]
  · intro y Φ hΦ v
    obtain ⟨q, hq⟩ := hx y
    rw [key _ Φ hΦ, hq]
    simp only [schr, GlobalTheory.ThK.Adapt.glue_dot, dotProduct_zero, zero_dotProduct, add_zero, zero_add, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨Ψ, hΨ, hΨ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F ((Fin n × Fin d) ⊕ (Fin n × Fin d))
    obtain ⟨Φ, hΦ, hSΦ⟩ := hSo Ψ hΨ
    refine ⟨Φ, hΦ, fun h => hΨ0 ?_⟩
    have h0 := congrFun h 0
    simp only [Pi.zero_apply] at h0
    rw [hSΦ, GlobalTheory.ThK.Adapt.glue_zero] at h0
    exact h0
  · intro y Φ hΦ v
    rw [GlobalTheory.SiegelAvg.starFam_apply, key _ Φ hΦ, hy y]
    simp only [schr, GlobalTheory.ThK.Adapt.glue_dot, GlobalTheory.ThK.Adapt.glue_add, dotProduct_zero, zero_dotProduct, add_zero, zero_add,
      mul_zero, AddChar.map_zero_eq_one, one_mul]

end
