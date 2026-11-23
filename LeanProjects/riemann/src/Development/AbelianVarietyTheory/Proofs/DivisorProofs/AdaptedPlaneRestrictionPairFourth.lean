import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousExtensionDoubledUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictToSubspaceRightStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblCompare

theorem uniqL : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), S Φ = c • Ed Φ := GlobalTheory.T.pair_restrict_to_subspace_left

theorem extL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ ext : UG (cA σ) (dbl (incM F W₁.J)) → UG (cA σ) (dbl (incM F W.J)), Continuous ext ∧
      ∀ (g₁ : UG (cA σ) (dbl (incM F W₁.J))) (g : UG (cA σ) (dbl (incM F W.J))),
        ((g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (g₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y)) ↔ g = ext g₁ := GlobalTheory.T.continuous_extension_doubled_unitary

theorem siegL : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      ∀ (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
        (omd₁ : UG (cA σ) (dbl (incM F W₁.J)) →* Module.End ℂ ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W₁.J)) dd₁ χX (diagCols (Fin d₁)) omd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
      ∀ (p₁ : UG (cA σ) (dbl (incM F W₁.J))) (t₁ : GL (Fin d₁) (AE F E)),
        (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) * diagCols (Fin d₁) = diagCols (Fin d₁) * t₁.1 →
      ∀ g : UG (cA σ) (dbl (incM F W.J)), ((g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y)) →
      ∀ a : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed (omd g Φ) = a • omd₁ p₁ (Ed Φ)) → a = 1 := GlobalTheory.T.pair_restrict_to_subspace_right

open scoped Classical in

theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  show pureA F f g x = _
  simp [pureA, mul_comm]

theorem vecMulVec_mul_transpose {m k : Type} [Fintype k] {R : Type} [CommRing R] (y : m → R) (w : k → R)
    (G : Matrix k k R) : Matrix.vecMulVec y w * Gᵀ = Matrix.vecMulVec y (G *ᵥ w) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fromCols_vecMulVec_zero {m k : Type} {R : Type} [CommRing R] (y : m → R) (w : k → R) :
    Matrix.fromCols (Matrix.vecMulVec y w) (0 : Matrix m k R) = Matrix.vecMulVec y (Sum.elim w 0) := by
  ext i (j | j) <;> simp [Matrix.vecMulVec_apply]

theorem fromCols_zero_vecMulVec {m k : Type} {R : Type} [CommRing R] (y : m → R) (w : k → R) :
    Matrix.fromCols (0 : Matrix m k R) (Matrix.vecMulVec y w) = Matrix.vecMulVec y (Sum.elim 0 w) := by
  ext i (j | j) <;> simp [Matrix.vecMulVec_apply]

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      ∀ (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
        (omd₁ : UG (cA σ) (dbl (incM F W₁.J)) →* Module.End ℂ ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W₁.J)) dd₁ χX (diagCols (Fin d₁)) omd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
      ∀ (g₁ : UG (cA σ) (dbl (incM F W₁.J))) (g : UG (cA σ) (dbl (incM F W.J))),
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (g₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) →
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y) →
        ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed (omd g Φ) = omd₁ g₁ (Ed Φ) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
    dd omd hdd homd dd₁ omd₁ hdd₁ homd₁ Ed hEpres hEheis hEinv hEadm hEnz g₁ g hg1 hg2 hg3 hg4 hg5
  obtain ⟨ext, hextc, hext⟩ := extL F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hH
  have hc := fun h₁ => (hext h₁ (ext h₁)).2 rfl
  have hsplit := homd.2.1
  have hsplit₁ := homd₁.2.1

  have hinv : ∀ h₁ : UG (cA σ) (dbl (incM F W₁.J)),
      ((h₁⁻¹).1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) * h₁.1.1 = 1 := fun h₁ =>
    Units.inv_mul h₁.1
  have hS : ∀ h₁, ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      (omd₁ h₁⁻¹ ∘ₗ Ed ∘ₗ omd (ext h₁)) Φ = c • Ed Φ := by
    intro h₁
    obtain ⟨e1, e2, e3, e4, e5⟩ := hc h₁
    refine uniqL hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁
      Ed _ hEpres hEheis hEinv hEadm hEnz ?_ ?_ ?_ ?_
    · intro Φ hΦ
      exact hsplit₁.pres _ _ (hEpres _ (hsplit.pres _ _ hΦ))
    · intro z Φ hΦ
      simp only [LinearMap.comp_apply]
      rw [hsplit.impl _ _ _ hΦ]
      have ha : actB (cA σ) (ext h₁) (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) =
          (z * (h₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E))ᵀ) *
            (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ := by
        simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
        congr 2
      rw [ha, hEheis _ _ (hsplit.pres _ _ hΦ), hsplit₁.impl _ _ _ (hEpres _ (hsplit.pres _ _ hΦ))]
      congr 1
      simp only [actB, Matrix.mul_assoc, ← Matrix.transpose_mul]
      show z * ((h₁⁻¹).1.1 * h₁.1.1)ᵀ = z
      rw [hinv, Matrix.transpose_one, Matrix.mul_one]
    · intro y Φ hΦ
      simp only [LinearMap.comp_apply]
      rw [hsplit.impl _ _ _ hΦ, hsplit.impl _ _ _ hΦ]
      have ha : ∀ v : Fin d ⊕ Fin d → AE F E, ((ext h₁).1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ v = v →
          actB (cA σ) (ext h₁) (Matrix.vecMulVec y v) = Matrix.vecMulVec y v := fun v hv => by
        simp only [actB]
        rw [vecMulVec_mul_transpose, hv]
      rw [fromCols_vecMulVec_zero, fromCols_zero_vecMulVec, ha _ e2, ha _ e3, ← fromCols_vecMulVec_zero,
        ← fromCols_zero_vecMulVec, (hEinv y _ (hsplit.pres _ _ hΦ)).1, (hEinv y _ (hsplit.pres _ _ hΦ)).2]
      exact ⟨rfl, rfl⟩
    · intro l hl
      exact hsplit.adm _ _ (hEadm _ (hsplit₁.adm _ _ hl))

  choose c hcS using hS
  have hkey : ∀ h₁ (Φ : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ), Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) →
      Ed (omd (ext h₁) Φ) = c h₁ • omd₁ h₁ (Ed Φ) := by
    intro h₁ Φ hΦ
    have h1 := congrArg (omd₁ h₁) (hcS h₁ Φ hΦ)
    simp only [LinearMap.comp_apply, map_smul] at h1
    rw [← h1, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := hEnz
  have huniq : ∀ (h₁ : UG (cA σ) (dbl (incM F W₁.J))) (a b : ℂ),
      a • omd₁ h₁ (Ed Φ₀) = b • omd₁ h₁ (Ed Φ₀) → a = b := by
    intro h₁ a b hab
    have h1 := congrArg (omd₁ h₁⁻¹) hab
    simp only [map_smul] at h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    have h2 : (a - b) • Ed Φ₀ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hne)
  have hext_mul : ∀ a b, ext (a * b) = ext a * ext b := by
    intro a b
    obtain ⟨a1, a2, a3, a4, a5⟩ := hc a
    obtain ⟨b1, b2, b3, b4, b5⟩ := hc b
    refine ((hext (a * b) (ext a * ext b)).1 ⟨?_, ?_, ?_, ?_, ?_⟩).symm
    · show ((ext a).1.1 * (ext b).1.1) * _ = _ * ((a.1.1) * (b.1.1))
      rw [Matrix.mul_assoc, b1, ← Matrix.mul_assoc, a1, Matrix.mul_assoc]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b2, a2]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b3, a3]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b4, a4]
    · show ((ext a).1.1 * (ext b).1.1) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b5, a5]
  have hext_one : ext 1 = 1 := by
    refine ((hext 1 1).1 ⟨?_, ?_, ?_, ?_, ?_⟩).symm
    · show (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * _ = _ * 1
      rw [Matrix.one_mul, Matrix.mul_one]
    all_goals exact Matrix.one_mulVec _
  have hc_one : c 1 = 1 := by
    refine huniq 1 _ _ ?_
    rw [← hkey 1 Φ₀ hΦ₀, hext_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply, one_smul]
  have hc_mul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine huniq (a * b) _ _ ?_
    rw [← hkey _ Φ₀ hΦ₀, hext_mul, map_mul, Module.End.mul_apply, hkey a _ (hsplit.pres _ _ hΦ₀), hkey b _ hΦ₀,
      map_smul, smul_smul, map_mul, Module.End.mul_apply]
  have hc_ne : ∀ a, c a ≠ 0 := fun a h0 => by
    have := hc_mul a a⁻¹
    rw [mul_inv_cancel, hc_one, h0, zero_mul] at this
    exact one_ne_zero this
  let cM : UG (cA σ) (dbl (incM F W₁.J)) →* ℂ := ⟨⟨c, hc_one⟩, hc_mul⟩
  let cU := cM.toHomUnits
  have hcU : ∀ a, (cU a : ℂ) = c a := fun a => rfl

  obtain ⟨x₀, hx₀⟩ : ∃ x, Ed Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set l : ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj x₀ with hl_def
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁) := proj_mem_adm F _ x₀
  have hcont : Continuous fun a : UG (cA σ) (dbl (incM F W₁.J)) => c a := by
    rw [continuous_iff_continuousAt]
    intro a₀
    have hΦ' : omd (ext a₀⁻¹) Φ₀ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := hsplit.pres _ _ hΦ₀
    have hfc : Continuous fun a => l (omd₁ a (Ed (omd (ext a₀⁻¹) Φ₀))) :=
      hsplit₁.cont l hl _ (hEpres _ hΦ')
    have hhc : Continuous fun a => (l ∘ₗ Ed) (omd (ext a) (omd (ext a₀⁻¹) Φ₀)) :=
      (hsplit.cont (l ∘ₗ Ed) (hEadm l hl) _ hΦ').comp hextc
    have heq : ∀ a, c a * l (omd₁ a (Ed (omd (ext a₀⁻¹) Φ₀))) = (l ∘ₗ Ed) (omd (ext a) (omd (ext a₀⁻¹) Φ₀)) := by
      intro a
      rw [LinearMap.comp_apply, hkey a _ hΦ', map_smul, smul_eq_mul]
    have hf0 : l (omd₁ a₀ (Ed (omd (ext a₀⁻¹) Φ₀))) ≠ 0 := by
      rw [hkey _ _ hΦ₀, map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        map_smul, smul_eq_mul]
      exact mul_ne_zero (hc_ne _) hx₀
    refine ((hhc.continuousAt).div (hfc.continuousAt) hf0).congr ?_
    filter_upwards [hfc.continuousAt.eventually_ne hf0] with a ha
    rw [Pi.div_apply, ← heq a]
    field_simp
  have hcUc : Continuous cU := by
    have h2 : Continuous fun a => (((cU a)⁻¹ : ℂˣ) : ℂ) := by
      have : (fun a => (((cU a)⁻¹ : ℂˣ) : ℂ)) = fun a => (c a)⁻¹ :=
        funext fun a => by rw [Units.val_inv_eq_inv_val, hcU]
      rw [this]
      exact hcont.inv₀ hc_ne
    exact Units.continuous_iff.2 ⟨hcont, h2⟩
  have hskew : ∀ i j, σ (W₁.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W₁.J i j := by
    intro i j
    rw [hP₁.skew.skew]
    simp
  have htriv := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hP.base.cm d₁ W₁.J (-1) hskew
    (GlobalTheory.ThK.TorusCentre.det_ne_zero_of_isSkew hP₁.skew) cU hcUc (by
      intro p t hpt
      refine Units.ext ?_
      rw [hcU]
      exact siegL hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
        dd omd hdd homd dd₁ omd₁ hdd₁ homd₁ Ed hEpres hEheis hEinv hEadm ⟨Φ₀, hΦ₀, hne⟩ p t hpt (ext p) (hc p) (c p)
        (fun Φ hΦ => hkey p Φ hΦ))
  have hg : g = ext g₁ := (hext g₁ g).1 ⟨hg1, hg2, hg3, hg4, hg5⟩
  have hc1 : c g₁ = 1 := by
    rw [← hcU, htriv]
    rfl
  intro Φ hΦ
  rw [hg, hkey g₁ Φ hΦ, hc1, one_smul]

end GlobalTheory.DblCompare
