import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairTransferAlongPlaneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXDblUniq

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

section Generic

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

end Generic

theorem transpose_mulVec_eq_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E)
    (h : ∀ u, form σ J (ι *ᵥ u) x = 0) : ιᵀ *ᵥ (J *ᵥ fun k => σ (x k)) = 0 := by
  funext m
  have := h (Pi.single m 1)
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem hTens_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (y : Fin d ⊕ Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)),
      hTens (cA σ) (incM F X.J) (dbl (incM F W.J)) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) y) = 0 := by
  intro F E _ _ _ _ _ σ B n d X W n₁ X₁ H j₀ j₁ hA y z
  set v : Fin n → AE F E := incM F X.J *ᵥ fun k => cA σ (incV F H.x k) with hv
  have h0 : (incM F H.ι)ᵀ *ᵥ v = 0 := by
    have e := transpose_mulVec_eq_zero σ X.J H.ι H.x (fun u => (hA.orth u).1)
    funext m
    have := congrArg (inclR (F := F) (AF F)) (congrFun e m)
    have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
    simpa [hv, incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, hc] using this
  have h1 : (incM F H.ι * z)ᵀ *ᵥ v = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  set b := incM F H.ι * z with hb
  have step : ∀ i j, (∑ k, ∑ l, b i j * incM F X.J i k * dbl (incM F W.J) j l *
      cA σ (Matrix.vecMulVec (incV F H.x) y k l)) = b i j * v i * ∑ l, dbl (incM F W.J) j l * cA σ (y l) := by
    intro i j
    simp only [hv, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.vecMulVec_apply, map_mul]
    ring
  simp only [hTens]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step i j, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun h1 j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
  rw [← Finset.sum_mul, this, zero_mul]

theorem rho_vecMulVec_add_orth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
      (ψ : AddChar (AF F) ℂ) (y : Fin d ⊕ Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E))
      (φ : ((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ),
      dd.rho ψ (Matrix.vecMulVec (incV F H.x) y) (dd.rho ψ (incM F H.ι * z) φ) =
        dd.rho ψ (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * z) φ := by
  intro F E _ _ _ _ _ σ B n d X W n₁ X₁ H j₀ j₁ hA dd ψ y z φ
  have hz := hTens_eq_zero F E σ B n d X W n₁ X₁ H j₀ j₁ hA y z
  have hba : symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) y) = 0 := by
    simp [symp, hz]
  have hab : symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (Matrix.vecMulVec (incV F H.x) y) (incM F H.ι * z) = 0 := by
    have e1 := dd.form (Matrix.vecMulVec (incV F H.x) y) (incM F H.ι * z)
    have e2 := dd.form (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) y)
    rw [hba] at e2
    linear_combination e1 + e2
  rw [GlobalTheory.InertRhoLaw.darboux_rho_rho, hab, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem lag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∃ L : Submodule F ((Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d ⊕ Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ y : Fin d ⊕ Fin d → AE F E, ∃ z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E),
          (dd₁.e z).1 = 0 ∧ ∀ φ : ((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) y) (dd.rho B.ψ (incM F H.ι * z) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.seesaw_pair_transfer_along_plane F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
    dd dd₁ hdd hdd₁
  refine ⟨L, hiso, hrk, fun t w hw => ?_⟩
  obtain ⟨y, z, hz, he⟩ := hL t w hw
  refine ⟨y, z, hz, fun φ => ?_⟩
  rw [rho_vecMulVec_add_orth F E σ B n d X W n₁ X₁ H j₀ j₁ hH dd B.ψ y z φ]
  simp only [Darboux.rho, he]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ≠ 0) →
      ∀ T : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), T Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), T (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (T Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), T (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = T Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), T Φ = c • ed Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e _ _ dd dd₁ hdd hdd₁
    ed hEm hEh hEi hEa hEnz T hTm hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := lag F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
    dd dd₁ hdd hdd₁
  have hadmT := hTa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  have hadmE := hEa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  let j : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) := fun z => incM F H.ι * z
  let k : (Fin d ⊕ Fin d → AE F E) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) := fun y => Matrix.vecMulVec (incV F H.x) y
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

end GlobalTheory.MixXDblUniq
