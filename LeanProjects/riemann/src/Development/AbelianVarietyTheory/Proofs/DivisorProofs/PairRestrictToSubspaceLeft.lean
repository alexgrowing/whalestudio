import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSumCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDirectSumExistsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.EvZeroUniqDbl
open scoped Classical

theorem dblLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
      ∃ L : Submodule F ((Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d ⊕ Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ y y' : Fin n → AE F E, ∃ z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E),
          (dd₁.e z).1 = 0 ∧ ∀ φ : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0)
                (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y' (incV F H'.x)))
                  (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) φ)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ dd dd₁ hdd hdd₁
  obtain ⟨L₀, hiso₀, hrank₀, hL₀⟩ :=
    GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁
  obtain ⟨L, hiso, hrank, hLw⟩ := GlobalTheory.T.lagrangian_direct_sum_exists L₀ hiso₀ hrank₀
  refine ⟨L, hiso, hrank, fun t w hw => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hLw w hw
  obtain ⟨ua, hua, za, hza, hea⟩ := hL₀ t a ha
  obtain ⟨ub, hub, zb, hzb, heb⟩ := hL₀ t b hb
  obtain ⟨ya, rfl⟩ := hua
  obtain ⟨yb, rfl⟩ := hub
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨ya, yb, Matrix.fromCols za zb, ?_, fun φ => ?_⟩
  · rw [hdd₁]
    funext i
    cases i <;> simp [hza, hzb]
  · have hz : Matrix.fromCols za zb * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ =
        Matrix.fromCols (incM F (1 : Matrix (Fin n) (Fin n) E) * za * (incM F H'.ι)ᵀ)
          (incM F (1 : Matrix (Fin n) (Fin n) E) * zb * (incM F H'.ι)ᵀ) := by
      rw [h1, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp
    have hw : t • ((fun i => algebraMap F (AF F) ((Sum.elim a.1 b.1 : Fin n × Fin d ⊕ Fin n × Fin d → F) i)),
        (fun i => algebraMap F (AF F) ((Sum.elim a.2 (-b.2) : Fin n × Fin d ⊕ Fin n × Fin d → F) i))) =
        (Sum.elim (t • ((fun i => algebraMap F (AF F) (a.1 i)), (fun i => algebraMap F (AF F) (a.2 i)))).1
            (t • ((fun i => algebraMap F (AF F) (b.1 i)), (fun i => algebraMap F (AF F) (b.2 i)))).1,
         Sum.elim (t • ((fun i => algebraMap F (AF F) (a.1 i)), (fun i => algebraMap F (AF F) (a.2 i)))).2
            (-(t • ((fun i => algebraMap F (AF F) (b.1 i)), (fun i => algebraMap F (AF F) (b.2 i)))).2)) := by
      ext i <;> cases i <;> simp
    rw [hw, hz]
    simp only [Darboux.rho]
    rw [hdd, hdd, hdd]
    have e := GlobalTheory.T.schrodinger_sum_composition B.ψ _ _ _ _ _ _ hea heb φ
    simpa using e

theorem proj_zero_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) = 0 := by
    funext i
    exact map_zero _
  have h2 : (fun i => ((0 : κ → AF F) i).2) = 0 := rfl
  show pureA F f g 0 = _
  rw [pureA, h1, h2]
  simp [mul_comm]

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
      ∀ (Ed S : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), S Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          S (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (S Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          S (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = S Φ ∧
          S (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = S Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ S ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), S Φ = c • Ed Φ := by
  intro _hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ dd dd₁ hdd hdd₁
    Ed S hEd hEdH hEdI hEdA hEdne _hS hSH hSI hSA
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrank, hL⟩ := dblLagr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁
    dd dd₁ hdd hdd₁
  let δ : ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁) := proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ u Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ Φ hΦ
  have hδe : ∀ (f : (Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) x, f x = δ (dd₁.rho B.ψ (dd₁.e.symm (x, 0)) f) :=
    fun f x => by simp [δ, Darboux.rho, schr]
  have hfix : ∀ z, (dd₁.e z).1 = 0 → ∀ f : (Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ,
      δ (dd₁.rho B.ψ z f) = δ f :=
    fun z hz f => by simp [δ, Darboux.rho, schr, hz]
  have key : ∀ T : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ),
      (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          T (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (T Φ)) →
      (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          T (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = T Φ ∧
          T (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = T Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
        (δ ∘ₗ T) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) =
          (δ ∘ₗ T) φ := by
    intro T hH hI t w hw φ hφ
    obtain ⟨y, y', z, hz, heq⟩ := hL t w hw
    simp only [LinearMap.comp_apply]
    rw [heq, (hI y _ (hρ _ _ (hρ _ _ hφ))).1, (hI y' _ (hρ _ _ hφ)).2, hH z φ hφ, hfix z hz]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hEdne
  obtain ⟨x₀, hx₀⟩ : ∃ x, Ed Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d ⊕ Fin n × Fin d) L hiso hrank (δ ∘ₗ S) (hSA δ hδ)
    (δ ∘ₗ Ed) (hEdA δ hδ) (key S hSH hSI) (key Ed hEdH hEdI)
    ⟨_, hρ ((dd₁.e.symm (x₀, 0)) * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [hEdH _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ ((dd₁.e.symm (x, 0)) * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hSH _ Φ hΦ, hEdH _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

end GlobalTheory.EvZeroUniqDbl
