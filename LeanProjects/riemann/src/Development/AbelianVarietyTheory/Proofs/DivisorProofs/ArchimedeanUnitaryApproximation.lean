import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ArchGlueMat

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_add {a b : Type} {X Y : Matrix a b (AE F E)} (hX : At (evI F) X) (hY : At (evI F) Y) :
    At (evI F) (X + Y) := fun c hc => by rw [smul_add, hX c hc, hY c hc, add_zero]

theorem at_mul_left {a b c : Type} [Fintype b] {X : Matrix a b (AE F E)} (hX : At (evI F) X)
    (Y : Matrix b c (AE F E)) : At (evI F) (X * Y) := fun t ht => by
  rw [← Matrix.smul_mul, hX t ht, Matrix.zero_mul]

theorem at_mul_right {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) {Y : Matrix b c (AE F E)}
    (hY : At (evI F) Y) : At (evI F) (X * Y) := fun t ht => by
  rw [← Matrix.mul_smul, hY t ht, Matrix.mul_zero]

theorem at_transpose {a b : Type} {X : Matrix a b (AE F E)} (hX : At (evI F) X) : At (evI F) Xᵀ := fun t ht => by
  rw [← Matrix.transpose_smul, hX t ht, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {a b : Type} {X : Matrix a b (AE F E)} (hX : At (evI F) X) :
    At (evI F) (X.map (cA σ)) := fun t ht => by
  have h := hX t ht
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem eq_zero_of_at {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : Type}
    {D : Matrix a b (AE F E)} (hA : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
  · intro t ht
    have := congrFun (congrFun (hA t ht) i) j
    simpa [Matrix.smul_apply] using this
  · intro w
    have := congrFun (congrFun (h0 w) i) j
    simpa [Matrix.map_apply] using this

end

theorem exists_unitary_glue : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k k' : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ), IsCMExt F E σ → (∀ w, k w * k' w = 1) → (∀ w, (k w)ᵀ * J.map (τ w).1 * (k w).map star = J.map (τ w).1) → ∃ K : UA σ J, At (evI F) (mat K - 1) ∧ ∀ w, (mat K).map (piInf (τ w)) = k w := by
  intro F E _ _ _ _ _ σ τ n J k k' hCM hkk' hk
  obtain ⟨u, hu, -⟩ := GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf σ τ hCM (fun w => k w - 1)
  obtain ⟨u', hu', -⟩ := GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf σ τ hCM (fun w => k' w - 1)
  set K : Matrix (Fin n) (Fin n) (AE F E) := 1 + u with hKdef
  set K' : Matrix (Fin n) (Fin n) (AE F E) := 1 + u' with hK'def
  have hKw : ∀ w, K.map (piInf (τ w)) = k w := fun w => by
    rw [hKdef, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hu.2 w]; abel
  have hK'w : ∀ w, K'.map (piInf (τ w)) = k' w := fun w => by
    rw [hK'def, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hu'.2 w]; abel
  have hmul : K * K' = 1 := by
    have e : K * K' - 1 = u + u' + u * u' := by rw [hKdef, hK'def]; noncomm_ring
    have hz : K * K' - 1 = 0 := by
      refine eq_zero_of_at hCM τ ?_ ?_
      · rw [e]; exact at_add (at_add hu.1 hu'.1) (at_mul_left hu.1 _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hKw, hK'w, hkk', Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact sub_eq_zero.1 hz
  have hmul' : K' * K = 1 := mul_eq_one_comm.1 hmul
  have hunit : Kᵀ * incM F J * K.map (cA σ) = incM F J := by
    have e : Kᵀ * incM F J * K.map (cA σ) - incM F J =
        uᵀ * incM F J + incM F J * u.map (cA σ) + uᵀ * incM F J * u.map (cA σ) := by
      rw [hKdef, Matrix.transpose_add, Matrix.transpose_one, Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      noncomm_ring
    have hz : Kᵀ * incM F J * K.map (cA σ) - incM F J = 0 := by
      refine eq_zero_of_at hCM τ ?_ ?_
      · rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hu.1) _) (at_mul_right _ (at_map_cA σ hu.1)))
          (at_mul_right _ (at_map_cA σ hu.1))
      · intro w
        have hc : (K.map (cA σ)).map (piInf (τ w)) = (k w).map star := by
          rw [← hKw w, Matrix.map_map, Matrix.map_map]
          congr 1
          funext z
          exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star F E σ hCM w (τ w) z
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hKw,
          GlobalTheory.ThK.PlaneEv.incM_map_piInf_emb, hk w, sub_self]
    exact sub_eq_zero.1 hz
  let g : GL (Fin n) (AE F E) := ⟨K, K', hmul, hmul'⟩
  have hg : g ∈ UG (cA σ) (incM F J) := hunit
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · show At (evI F) (K - 1)
    rw [hKdef, add_sub_cancel_left]; exact hu.1
  · intro w
    exact hKw w

end GlobalTheory.ArchGlueMat
