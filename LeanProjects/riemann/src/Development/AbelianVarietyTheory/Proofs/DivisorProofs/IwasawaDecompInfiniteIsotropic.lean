import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianIsotropicVectorCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitaryApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponentsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ArchIwasawaLine

theorem mat_mul' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem at_mat_mul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (hg : At (evI F) (mat g - 1)) (hh : At (evI F) (mat h - 1)) :
    At (evI F) (mat (g * h) - 1) := by
  intro u hu
  have e : mat (g * h) - 1 = mat g * (mat h - 1) + (mat g - 1) := by
    rw [mat_mul', Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem at_mat_inv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : At (evI F) (mat g - 1)) : At (evI F) (mat g⁻¹ - 1) := by
  intro u hu
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← mat_mul', inv_mul_cancel]
    show _ = -((((1 : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) - mat g⁻¹)
    simp
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem arch_iwasawa_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n : ℕ} (W : Spc F E n) (r s : ℕ) (x : Fin n → E), IsCMExt F E σ → W.IsSkew σ B r s → x ≠ 0 →
    form σ W.J x x = 0 → ∀ g ∈ UAt σ W (evI F), ∃ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      ∃ k ∈ KInf σ W B.emb, g = p * k := by
  intro F E _ _ _ _ _ σ B n W r s x hCM hW hx hiso g hg
  have hτσ : ∀ w (e : E), (B.emb w).1 (σ e) = star ((B.emb w).1 e) := fun w e => hCM.2.2.2 (B.emb w).1 e
  have hmapJ : ∀ w, (incM F W.J).map (piInf (B.emb w)) = W.J.map (B.emb w).1 := by
    intro w; ext i j; simp [incM, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
  have hmapc : ∀ w (A : Matrix (Fin n) (Fin n) (AE F E)),
      (A.map (cA σ)).map (piInf (B.emb w)) = (A.map (piInf (B.emb w))).map star := by
    intro w A; ext i j; simp [GlobalTheory.RealPlaceConj.piInf_cA_eq_star F E σ hCM]
  have hunit : ∀ (h : UA σ W.J) w, ((mat h).map (piInf (B.emb w)))ᵀ * W.J.map (B.emb w).1 *
      ((mat h).map (piInf (B.emb w))).map star = W.J.map (B.emb w).1 := by
    intro h w
    have h2 : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
    have := congrArg (fun A => A.map (piInf (B.emb w))) h2
    simp only [Matrix.map_mul, ← Matrix.transpose_map, hmapJ, hmapc] at this
    exact this
  have hinv : ∀ (h : UA σ W.J) w, (mat h).map (piInf (B.emb w)) * (mat h⁻¹).map (piInf (B.emb w)) = 1 := by
    intro h w
    rw [← Matrix.map_mul, ← mat_mul', mul_inv_cancel]
    show ((((1 : UA σ W.J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))).map _ = 1
    simp
  have hloc : ∀ w : InfinitePlace F, ∃ k k' : Matrix (Fin n) (Fin n) ℂ, k * k' = 1 ∧
      kᵀ * W.J.map (B.emb w).1 * k.map star = W.J.map (B.emb w).1 ∧ Commute k (W.θ w) ∧
      ∃ β : ℂ, β ≠ 0 ∧ ((mat g).map (piInf (B.emb w)) * k') *ᵥ (fun i => (B.emb w).1 (x i)) =
        β • (fun i => (B.emb w).1 (x i)) := by
    intro w
    set Jw := W.J.map (B.emb w).1
    have hM : (Complex.I • Jw)ᴴ = Complex.I • Jw := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, Jw, smul_eq_mul, star_mul',
        Complex.star_def, Complex.conj_I]
      rw [← Complex.star_def, ← hτσ, hW.skew, map_neg]; ring
    have hu : ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᵀ * Jw * A.map star = Jw → Aᵀ * (Complex.I • Jw) * A.map star = Complex.I • Jw := by
      intro A hA; rw [Matrix.mul_smul, Matrix.smul_mul, hA]
    have hxw : (fun i => (B.emb w).1 (x i)) ≠ 0 := by
      intro h0; apply hx; funext i
      have := congrFun h0 i
      simpa using this
    have hisow : (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Jw) *ᵥ star (fun i => (B.emb w).1 (x i)) = 0 := by
      have e : (fun i => (B.emb w).1 (x i)) ⬝ᵥ Jw *ᵥ star (fun i => (B.emb w).1 (x i)) = (B.emb w).1 (form σ W.J x x) := by
        rw [form, RingHom.map_dotProduct]; congr 1; funext i
        rw [Function.comp_apply, RingHom.map_mulVec]; congr 1; funext j; simp [hτσ]
      rw [Matrix.smul_mulVec, dotProduct_smul, e, hiso, map_zero, smul_zero]
    obtain ⟨k, k', hkk, hk, hkc, β, hβ, hβx⟩ := GlobalTheory.T.hermitian_isotropic_vector_cartan (Complex.I • Jw) (W.θ w) _ _ _ hM (hW.cartan w)
      (hinv g w) (hu _ (hunit g w)) hxw hisow
    refine ⟨k, k', hkk, ?_, hkc, β, hβ, hβx⟩
    have := congrArg (fun A => (-Complex.I) • A) hk
    simpa [Matrix.mul_smul, Matrix.smul_mul, smul_smul] using this
  choose k k' hkk hk hkc β hβ hβx using hloc
  obtain ⟨K, hKat, hKmap⟩ := GlobalTheory.T.archimedean_unitary_approximation σ B.emb W.J k k' hCM hkk hk
  obtain ⟨t, htat, htmap⟩ := GlobalTheory.T.exists_idele_with_archimedean_components σ B.emb β hCM hβ
  have hKi : ∀ w, (mat K⁻¹).map (piInf (B.emb w)) = k' w := by
    intro w
    have h1 := hinv K⁻¹ w
    rw [inv_inv, hKmap] at h1
    calc (mat K⁻¹).map (piInf (B.emb w)) = (mat K⁻¹).map (piInf (B.emb w)) * (k w * k' w) := by rw [hkk, Matrix.mul_one]
      _ = k' w := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨g * K⁻¹, t, ?_, K, ⟨hKat, fun w => by rw [hKmap w]; exact hkc w⟩, by group⟩
  have hpat : At (evI F) (mat (g * K⁻¹) - 1) := at_mat_mul hg (at_mat_inv hKat)
  funext i
  apply sub_eq_zero.1
  apply GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM B.emb
  · intro u hu
    have e : (mat (g * K⁻¹) *ᵥ incV F x) i - (t.1 • incV F x) i =
        ((mat (g * K⁻¹) - 1) *ᵥ incV F x) i - (t.1 - 1) * incV F x i := by
      simp [Matrix.sub_mulVec, sub_mul]
    rw [e, smul_sub, ← Pi.smul_apply, ← Matrix.smul_mulVec, hpat u hu, Matrix.zero_mulVec, Pi.zero_apply,
      ← smul_mul_assoc, htat u hu, zero_mul, sub_zero]
  · intro w
    have e1 := congrFun (hβx w) i
    have hm : (mat (g * K⁻¹)).map (piInf (B.emb w)) = (mat g).map (piInf (B.emb w)) * k' w := by
      rw [mat_mul', Matrix.map_mul, hKi]
    rw [map_sub, RingHom.map_mulVec, hm, Pi.smul_apply, smul_eq_mul, map_mul, htmap]
    have hv : (piInf (B.emb w)) ∘ incV F x = fun j => (B.emb w).1 (x j) := by
      funext j; simp [incV, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
    rw [hv, e1]
    simp [incV, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]

end GlobalTheory.ArchIwasawaLine
