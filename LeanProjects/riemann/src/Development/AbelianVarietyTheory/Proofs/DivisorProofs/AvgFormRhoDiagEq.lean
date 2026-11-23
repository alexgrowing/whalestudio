import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRestrictsAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelAvgInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_schr_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  have e1 : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := sub_eq_zero.mp h
  simp only [add_dotProduct, dotProduct_add]
  linear_combination ⅟(2 : R) * e1 - (w.1 ⬝ᵥ w'.2) * h2

theorem mul_diagCols_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE F E)) :
    A * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ = Matrix.fromCols A A := by
  simp [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]

theorem symp_diag (σ : E →ₐ[F] E) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) (AE F E)) (JB : Matrix (Fin n) (Fin n) (AE F E))
    (A A' : Matrix (Fin m) (Fin n) (AE F E)) :
    symp (cA σ) (-1) JA (dbl JB) (Matrix.fromCols A A) (Matrix.fromCols A' A') = 0 := by
  simp only [symp, hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, add_neg_cancel, Finset.sum_add_distrib]
  simp

theorem vecMulVec_elim {m n : ℕ} (u : Fin m → AE F E) (v : Fin n → AE F E) :
    Matrix.vecMulVec u (Sum.elim v v) =
      Matrix.vecMulVec u v * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ := by
  rw [mul_diagCols_transpose]
  ext i (j | j) <;> rfl

theorem rho_diag_add (σ : E →ₐ[F] E) {m n : ℕ} {JA : Matrix (Fin m) (Fin m) (AE F E)}
    {JB : Matrix (Fin n) (Fin n) (AE F E)} {κ : Type} [Fintype κ]
    (dd : Darboux (symp (cA σ) (-1) JA (dbl JB)) κ) (ψ : AddChar (AF F) ℂ)
    (A A' : Matrix (Fin m) (Fin n) (AE F E)) (φ : (κ → AF F) → ℂ) :
    dd.rho ψ (A * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ)
        (dd.rho ψ (A' * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) φ) =
      dd.rho ψ ((A + A') * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) φ := by
  simp only [Darboux.rho]
  rw [schr_schr_of_orth ψ _ _ ?_ φ, ← map_add, ← Matrix.add_mul]
  rw [← dd.form, mul_diagCols_transpose, mul_diagCols_transpose, symp_diag]

theorem avgForm_rho_diag_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∀ l₁ : (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ) →ₗ[ℂ] ℂ, l₁ ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
          l₁ (dd₁.rho B.ψ (z * (diagCols (Fin n))ᵀ) φ) = l₁ φ) →
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
        ∀ (z : Matrix (Fin d) (Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          GlobalTheory.SiegelAvg.avgForm μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = GlobalTheory.SiegelAvg.avgForm μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ ed hedS hedH hedI hedA hedNe l₁ hl₁ hl₁I μ hμ z Φ hΦ
  have hstd : IsStd B.ψ := hP.base.std
  have hρ : ∀ u, ∀ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      dd.rho B.ψ u Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    fun u Ψ hΨ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ Ψ hΨ
  have hconv := fun Ψ (hΨ : Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d))) =>
    GlobalTheory.T.pair_restricts_adapted_plane hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ d' hd' d₁' hd₁' dd hdd
      dd₁ hdd₁ ed hedS hedH hedI hedA hedNe l₁ hl₁ hl₁I μ hμ Ψ hΨ
  obtain ⟨Sc, Uc, Tc, hdec⟩ := GlobalTheory.ArchUniq.Coord.decomp (n := n) hP.skew hA
  let a : Fin n → AE F E := fun j => ((incM F Sc)ᵀ * z) () j
  let z₁ : Matrix (Fin d₁) (Fin n) (AE F E) := (incM F Uc)ᵀ * z
  let b : Fin n → AE F E := fun j => ((incM F Tc)ᵀ * z) () j
  have hz : z = Matrix.vecMulVec (incV F H'.x) a + incM F H'.ι * z₁ + Matrix.vecMulVec (incV F H'.y) b := by
    have h := congrArg Matrix.transpose (hdec zᵀ)
    rw [Matrix.transpose_transpose] at h
    conv_lhs => rw [h]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
    congr 1
    congr 1
    all_goals first
      | rfl
      | simp only [z₁, Matrix.mul_assoc]
      | (ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply, a, b, incM, incV, Matrix.replicateCol])
  let Δt : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.transpose (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))
  have hadd : ∀ (A A' : Matrix (Fin d) (Fin n) (AE F E)) (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
      dd.rho B.ψ (A * Δt) (dd.rho B.ψ (A' * Δt) φ) = dd.rho B.ψ ((A + A') * Δt) φ :=
    fun A A' φ => GlobalTheory.SiegelAvgInv.rho_diag_add σ dd B.ψ A A' φ
  have helim : ∀ (u : Fin d → AE F E) (v : Fin n → AE F E),
      Matrix.vecMulVec u (Sum.elim v v) = Matrix.vecMulVec u v * Δt :=
    fun u v => GlobalTheory.SiegelAvgInv.vecMulVec_elim u v
  have key : ∀ y : Fin n → AE F E,
      (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ)) =
        (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) (b + y) Φ) := by
    intro y
    have s2 : Matrix.vecMulVec (incV F H'.y) y + z =
        incM F H'.ι * z₁ + (Matrix.vecMulVec (incV F H'.x) a + Matrix.vecMulVec (incV F H'.y) (b + y)) := by
      conv_lhs => rw [hz]
      ext i j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply]
      ring
    have s1 : dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y)) (dd.rho B.ψ (z * Δt) Φ) =
        dd.rho B.ψ (incM F H'.ι * (z₁ * Δt)) (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) a * Δt)
          (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ)) := by
      rw [helim, hadd, s2, ← Matrix.mul_assoc (incM F H'.ι) z₁ Δt, hadd, hadd]
      simp only [add_assoc]
    have h3 := hρ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ hΦ
    have h2 := hρ (Matrix.vecMulVec (incV F H'.x) a * Δt) _ h3
    have s4 : ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) a * Δt)
        (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ)) =
        ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ) := by
      rw [← helim]
      exact hedI _ _ h3
    calc (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ))
        = l₁ (ed (dd.rho B.ψ (incM F H'.ι * (z₁ * Δt)) (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) a * Δt)
          (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ)))) := congrArg (fun t => l₁ (ed t)) s1
      _ = l₁ (dd₁.rho B.ψ (z₁ * Δt) (ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) a * Δt)
          (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ)))) := congrArg l₁ (hedH _ _ h2)
      _ = l₁ (ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) a * Δt)
          (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ))) := hl₁I _ _ (hedS _ h2)
      _ = l₁ (ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.y) (b + y) * Δt) Φ)) := congrArg l₁ s4
      _ = (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) (b + y) Φ) :=
          congrArg (fun u => l₁ (ed (dd.rho B.ψ u Φ))) (helim _ _).symm
  rw [GlobalTheory.SiegelAvg.avgForm_apply _ _ _ (hconv _ (hρ _ Φ hΦ)), GlobalTheory.SiegelAvg.avgForm_apply _ _ _ (hconv Φ hΦ)]
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  simp only [key]
  exact integral_add_left_eq_self (fun y => (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ)) b

end GlobalTheory.SiegelAvgInv
