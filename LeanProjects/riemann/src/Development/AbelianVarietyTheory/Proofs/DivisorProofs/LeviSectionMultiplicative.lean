import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviHom

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levi_mul_cols {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b}
    (H : Plane E (b + 2) b) (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h : UA σ W.J) (hL : IsLevi H l g₀ h) :
    mat h * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) =
      fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * blk (mat g₀) l.1 (cA σ (l⁻¹).1) := by
  obtain ⟨hx, hy, hι⟩ := hL
  rw [mul_fromCols, blk, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  refine congrArg₂ fromCols hι ?_
  ext i k
  rw [mul_diagonal]
  fin_cases k
  · have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.x i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · have := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.y i), ← this]; done) | (rw [mul_comm (incV F H.y i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)

theorem isLevi_mul {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b} (H : Plane E (b + 2) b)
    {l l' : (AE F E)ˣ} {g₀ g₀' : UA σ W₁.J} {h h' : UA σ W.J} (hL : IsLevi H l g₀ h) (hL' : IsLevi H l' g₀' h') :
    IsLevi H (l * l') (g₀ * g₀') (h * h') := by
  obtain ⟨hx, hy, hι⟩ := hL
  obtain ⟨hx', hy', hι'⟩ := hL'
  have hm : ∀ (A B : UA σ W.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  have hm₁ : ∀ (A B : UA σ W₁.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← mulVec_mulVec, hx', mulVec_smul, hx, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← mulVec_mulVec, hy', mulVec_smul, hy, smul_smul, _root_.mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, hm₁, Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀') ∧ Continuous (fun x : (AE F E)ˣ × UA σ G₁.V.J => m x.1 x.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  set QA := Q.map f

  have hform : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → mat h = PA * blk (mat g₀) l.1 (cA σ (l⁻¹).1) * QA := by
    intro l g₀ h hL
    rw [← levi_mul_cols H l g₀ h hL, Matrix.mul_assoc, hPQ', Matrix.mul_one]
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h h' : UA σ G.V.J), IsLevi H l g₀ h → IsLevi H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by rw [hform l g₀ h hL, hform l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  have hmul : ∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀' := fun l l' g₀ g₀' =>
    huniq _ _ _ _ (hm _ _) (isLevi_mul H (hm l g₀) (hm l' g₀'))
  refine ⟨hmul, ?_⟩
  have m11 : m 1 1 = 1 := by
    have := hmul 1 1 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ l g₀, (m l g₀)⁻¹ = m l⁻¹ g₀⁻¹ := fun l g₀ =>
    inv_eq_of_mul_eq_one_right (by rw [← hmul, mul_inv_cancel, mul_inv_cancel, m11])
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hmat : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, Continuous fun g : UA σ J => mat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hvec : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ![x.1.1, cA σ (x.1⁻¹).1] := by
    refine continuous_pi fun k => ?_
    fin_cases k
    · exact Units.continuous_val.comp continuous_fst
    · exact hcA.comp (Units.continuous_coe_inv.comp continuous_fst)
  have hval : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2) := by
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) =
        fun x => PA * blk (mat x.2) x.1.1 (cA σ (x.1⁻¹).1) * QA := funext fun x => hform _ _ _ (hm _ _)
    rw [this]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact Continuous.matrix_fromBlocks (hmat.comp continuous_snd) continuous_const continuous_const
      (Continuous.matrix_diagonal hvec)
  have hGL : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => ((((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E))⁻¹ :
        GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))) =
        (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) ∘ fun x => (x.1⁻¹, x.2⁻¹) := by
      funext x
      simp only [Function.comp_apply, ← hinv]
      rfl
    rw [this]
    exact hval.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_inv.comp continuous_snd))
  exact continuous_induced_rng.2 hGL

end GlobalTheory.LeviHom
