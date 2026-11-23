import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.IsoPhase

theorem hTens_pure {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β]
    (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (b y : β → A) :
    hTens c JA JB (Matrix.vecMulVec a b) (Matrix.vecMulVec a' y) =
      (a ⬝ᵥ JA *ᵥ (fun k => c (a' k))) * (b ⬝ᵥ JB *ᵥ (fun l => c (y l))) := by
  unfold hTens
  simp only [Matrix.vecMulVec_apply]
  simp only [_root_.dotProduct, Matrix.mulVec]
  simp only [map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem incM_mulVec_incV {m k : ℕ} (M : Matrix (Fin m) (Fin k) E) (v : Fin k → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  funext i
  exact ((inclR (F := F) (AF F)).map_mulVec M v i).symm

theorem cA_mulVec (σ : E →ₐ[F] E) {m k : ℕ} (M : Matrix (Fin m) (Fin k) E) (y : Fin k → AE F E) :
    (fun i => cA σ ((incM F M *ᵥ y) i)) = incM F (M.map σ) *ᵥ fun l => cA σ (y l) := by
  funext i
  rw [show cA σ ((incM F M *ᵥ y) i) = (cA σ).toRingHom ((incM F M *ᵥ y) i) from rfl, RingHom.map_mulVec]
  congr 1

theorem inclR_form (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (a b : Fin m → E) :
    inclR (F := F) (AF F) (form σ J a b) = incV F a ⬝ᵥ incM F J *ᵥ fun i => cA σ (incV F b i) := by
  have h : (fun i => cA σ (incV F b i)) = incV F (fun i => σ (b i)) := by
    funext i; simp [incV, cA_inclR]
  rw [h, incM_mulVec_incV, form, RingHom.map_dotProduct]
  rfl

theorem gram_step (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (J₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E) (hg : ιᵀ * J * ι.map σ = J₁) (w : Fin d₁ → E) (y : Fin d₁ → AE F E) :
    incV F w ⬝ᵥ incM F J₁ *ᵥ (fun l => cA σ (y l)) =
      incV F (ι *ᵥ w) ⬝ᵥ incM F J *ᵥ (fun l => cA σ ((incM F ι *ᵥ y) l)) := by
  have hg' : incM F J₁ = (incM F ι)ᵀ * incM F J * incM F (ι.map σ) := by
    rw [← hg]; simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [cA_mulVec, hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, incM_mulVec_incV]

theorem phase_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (x x' : Fin n → E) (w : Fin d₁ → E), ∃ L : Matrix (Fin d) (Fin d) (AE F E) → AF F, Continuous L ∧
      ∀ (y : Fin d₁ → AE F E) (b : AE F E) (g : Matrix (Fin d) (Fin d) (AE F E)), incM F H'.ι *ᵥ y = g *ᵥ incV F H'.y - incV F H'.y - b • incV F H'.x →
        symp (cA σ) (-1 : AE F E) (incM F X.J) (incM F W₁.J) (Matrix.vecMulVec (incV F x') (incV F w)) (Matrix.vecMulVec (incV F x) y) = L g := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ hH x x' w
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  set K : AE F E := incV F x' ⬝ᵥ incM F X.J *ᵥ fun k => cA σ (incV F x k) with hK
  set u : Fin d → AE F E := incV F (H'.ι *ᵥ w) ᵥ* incM F W.J with hu
  refine ⟨fun g => Algebra.trace (AF F) (AE F E) ((-1) * (K * ∑ l, u l * cA σ ((g *ᵥ incV F H'.y) l))), ?_, ?_⟩
  · have hLin : ∀ f : AE F E →ₗ[AF F] AE F E, Continuous f := fun f => IsModuleTopology.continuous_of_linearMap f
    have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
    have hmv : ∀ l, Continuous fun g : Matrix (Fin d) (Fin d) (AE F E) => (g *ᵥ incV F H'.y) l := by
      intro l
      simp only [Matrix.mulVec, _root_.dotProduct]
      refine continuous_finset_sum _ fun j _ => ?_
      exact (hLin (LinearMap.mulRight (AF F) (incV F H'.y j))).comp (continuous_id.matrix_elem l j)
    have hin : Continuous fun g : Matrix (Fin d) (Fin d) (AE F E) => ∑ l, u l * cA σ ((g *ᵥ incV F H'.y) l) :=
      continuous_finset_sum _ fun l _ =>
        (hLin (LinearMap.mulLeft (AF F) (u l))).comp ((hLin (cA σ).toLinearMap).comp (hmv l))
    have h3 := (hLin (LinearMap.mulLeft (AF F) ((-1) * K))).comp hin
    exact htr.comp (h3.congr fun g => by simp [mul_assoc, Finset.mul_sum])
  · intro y b g hy
    have h1 := (hH.orth w).1
    have h2 := (hH.orth w).2
    have e1 := inclR_form (F := F) σ W.J (H'.ι *ᵥ w) H'.x
    have e2 := inclR_form (F := F) σ W.J (H'.ι *ᵥ w) H'.y
    rw [h1, map_zero] at e1
    rw [h2, map_zero] at e2
    unfold symp
    rw [hTens_pure, gram_step σ W.J W₁.J H'.ι hH.gram w y, hy]
    congr 1
    have hc : (fun l => cA σ ((g *ᵥ incV F H'.y - incV F H'.y - b • incV F H'.x) l)) =
        (fun l => cA σ ((g *ᵥ incV F H'.y) l)) - (fun l => cA σ (incV F H'.y l)) - cA σ b • fun l => cA σ (incV F H'.x l) := by
      funext l; simp [map_sub, map_mul]
    rw [hc, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, _root_.dotProduct_sub, _root_.dotProduct_sub,
      _root_.dotProduct_smul, ← e1, ← e2, smul_zero, sub_zero, sub_zero]
    congr 2
    rw [Matrix.dotProduct_mulVec]
    rfl

end GlobalTheory.ThK.IsoPhase
