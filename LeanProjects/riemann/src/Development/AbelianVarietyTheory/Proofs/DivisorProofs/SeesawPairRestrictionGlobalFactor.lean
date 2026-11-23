import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDoublingSchrodingerFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictsToAdaptedWStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F : Type} [Field F] [NumberField F] {V V₁ : Type} [AddCommGroup V] [Module (AF F) V] [AddCommGroup V₁]
  [Module (AF F) V₁] {b : V → V → AF F} {b₁ : V₁ → V₁ → AF F} {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem rho_zero_first (D₁ : Darboux b₁ κ₁) (ψ : AddChar (AF F) ℂ) (z : V₁) (hz : (D₁.e z).1 = 0)
    (Ψ : (κ₁ → AF F) → ℂ) : D₁.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (D₁ : Darboux b₁ κ₁) (ψ : AddChar (AF F) ℂ) (y : κ₁ → AF F) (Ψ : (κ₁ → AF F) → ℂ) :
    D₁.rho ψ (D₁.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

theorem apply_eq_evaluation_zero (D : Darboux b κ) (D₁ : Darboux b₁ κ₁) (ψ : AddChar (AF F) ℂ) (j : V₁ → V)
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (hS : ∀ z, ∀ Φ ∈ schA F κ, S (D.rho ψ (j z) Φ) = D₁.rho ψ z (S Φ)) (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ)
    (y : κ₁ → AF F) : S Φ y = ev0 κ₁ (S (D.rho ψ (j (D₁.e.symm (y, 0))) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (D : Darboux b κ) (D₁ : Darboux b₁ κ₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (j : V₁ → V)
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (hS : ∀ z, ∀ Φ ∈ schA F κ, S (D.rho ψ (j z) Φ) = D₁.rho ψ z (S Φ)) {Y : Type} (k : Y → V)
    (hI : ∀ y, ∀ Φ ∈ schA F κ, S (D.rho ψ (k y) Φ) = S Φ) (w : (κ → AF F) × (κ → AF F))
    (hw : ∃ y, ∃ z, (D₁.e z).1 = 0 ∧ ∀ φ : (κ → AF F) → ℂ, schr ψ w φ = D.rho ψ (k y) (D.rho ψ (j z) φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) :
    (ev0 κ₁ ∘ₗ S) (schr ψ w Φ) = (ev0 κ₁ ∘ₗ S) Φ := by
  obtain ⟨y, z, hz, he⟩ := hw
  have h1 : D.rho ψ (j z) Φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI y _ h1, hS z Φ hΦ, rho_zero_first D₁ ψ z hz]

theorem lag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∃ L : Submodule F (((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ y : Fin n ⊕ Fin n → AE F E, ∃ z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E),
          (dd₁.e z).1 = 0 ∧ ∀ φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) (dd.rho B.ψ (incM F H'.ι * z) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.pair_restricts_to_adapted_w F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
    d' hd' d₁' hd₁' dd hdd dd₁ hdd₁
  refine ⟨L, hiso, hrk, fun t w hw => ?_⟩
  obtain ⟨y, z, hz, he⟩ := hL t w hw
  refine ⟨y, z, hz, fun φ => ?_⟩
  rw [GlobalTheory.T.darboux_doubling_schrodinger_formula F E σ B n d X W d₁ W₁ H' i₀ i₁ hH dd B.ψ y z φ]
  simp only [Darboux.rho, he]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ T : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (T Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          T (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = T Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        ∃ c : ℂ, ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ = c • ed Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ ed hEm hEh hEi hEa hEnz T hTm hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := lag F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
    d' hd' d₁' hd₁' dd hdd dd₁ hdd₁
  have hadmT := hTa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  have hadmE := hEa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  let j : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E) → Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) := fun z => incM F H'.ι * z
  let k : (Fin n ⊕ Fin n → AE F E) → Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) := fun y => Matrix.vecMulVec (incV F H'.x) y
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hEnz
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ _ L hiso hrk _ hadmT _ hadmE
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul dd dd₁ B.ψ hψ j T hTh k hTi _ (hL t w hw) Φ hΦ)
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul dd dd₁ B.ψ hψ j ed hEh k hEi _ (hL t w hw) Φ hΦ)
    ⟨dd.rho B.ψ (j (dd₁.e.symm (y₀, 0))) Φ₀, GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ₀ hΦ₀, by
      rw [LinearMap.comp_apply, ← apply_eq_evaluation_zero dd dd₁ B.ψ j ed hEh Φ₀ hΦ₀ y₀]; exact hy₀⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [apply_eq_evaluation_zero dd dd₁ B.ψ j T hTh Φ hΦ y, Pi.smul_apply, apply_eq_evaluation_zero dd dd₁ B.ψ j ed hEh Φ hΦ y, smul_eq_mul]
  exact hc _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ)

end GlobalTheory.DblUniq
