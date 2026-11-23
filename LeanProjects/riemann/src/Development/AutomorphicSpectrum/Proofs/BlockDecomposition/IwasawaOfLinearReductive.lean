import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangularStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebraStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiagStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRegularElementAbelianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneDiagonalConjugateStatement
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exp_mem_unitaryGroup {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1
  rw [← Matrix.exp_conjTranspose, hX]
  exact (Matrix.exp_neg X ▸ Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)))

theorem frame {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧
      U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ ∈ 𝔤 ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) * Y = Y * (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) →
        (Uᴴ * Y * U).IsDiag := by
  obtain ⟨𝔞, hle, hH, hC, hM⟩ := GlobalTheory.T.exists_maximal_abelian_hermitian 𝔤
  obtain ⟨U₀, hU₀, hD⟩ := GlobalTheory.T.commuting_hermitian_simultaneous_diag (𝔞 : Set (Matrix (Fin n) (Fin n) ℂ)) hH hC
  obtain ⟨H, hHa, hreg⟩ := GlobalTheory.T.exists_regular_element_abelian 𝔞 U₀
  have hU₀' : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
  have hU₀'' : U₀ᴴ * U₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU₀
  let d : Fin n → ℝ := fun i => ((U₀ᴴ * H * U₀) i i).re
  have hdd : Matrix.diagonal (fun i => (d i : ℂ)) = U₀ᴴ * H * U₀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have : star ((U₀ᴴ * H * U₀) i i) = (U₀ᴴ * H * U₀) i i := by
        have h2 : (U₀ᴴ * H * U₀)ᴴ = U₀ᴴ * H * U₀ := by
          simp [Matrix.conjTranspose_mul, hH H hHa, Matrix.mul_assoc]
        exact congrFun (congrFun h2 i) i
      have h3 := Complex.conj_eq_iff_real.1 this
      obtain ⟨r, hr⟩ := h3
      simp [d, hr]
    · simp [Matrix.diagonal_apply_ne _ hij, hD H hHa hij]
  have hHd : U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ = H := by
    rw [hdd]
    calc U₀ * (U₀ᴴ * H * U₀) * U₀ᴴ = (U₀ * U₀ᴴ) * H * (U₀ * U₀ᴴ) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hU₀']; simp
  obtain ⟨U, hU, h, hanti, heq, hdiag⟩ := GlobalTheory.T.antitone_diagonal_conjugate U₀ d hU₀
  refine ⟨U, hU, h, hanti, ?_, ?_⟩
  · rw [heq, hHd]; exact hle hHa
  · intro Y hY hYs hcomm
    rw [heq, hHd] at hcomm
    apply hdiag
    refine hD Y (hM Y hY hYs fun A hA => ?_)
    exact GlobalTheory.T.centralizer_regular_commutes U₀ H A Y hU₀ (hD H hHa) (hD A hA) (fun i j hij => hreg i j hij A hA) hcomm

theorem alg {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hs : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hb : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧
      (Uᴴ * B * U).BlockTriangular id := by
  obtain ⟨U, hU, h, hanti, hd, hreg⟩ := frame 𝔤
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have cj : ∀ Z : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * Z * U) * Uᴴ = Z := fun Z => by
    calc U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1]; simp
  have cj' : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * Z * Uᴴ) * U = Z := fun Z => by
    calc Uᴴ * (U * Z * Uᴴ) * U = (Uᴴ * U) * Z * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h2]; simp
  let φ : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun Z => U * Z * Uᴴ
      map_add' := fun a b => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r a => by simp }
  let 𝔥 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤.comap φ
  have mem : ∀ Z, Z ∈ 𝔥 ↔ U * Z * Uᴴ ∈ 𝔤 := fun Z => Iff.rfl
  have mem' : ∀ Z ∈ 𝔤, Uᴴ * Z * U ∈ 𝔥 := fun Z hZ => by rw [mem, cj]; exact hZ
  have mulc : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, (U * P * Uᴴ) * (U * Q * Uᴴ) = U * (P * Q) * Uᴴ := fun P Q => by
    calc (U * P * Uᴴ) * (U * Q * Uᴴ) = U * P * (Uᴴ * U) * Q * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp [Matrix.mul_assoc]
  have hs' : ∀ Z ∈ 𝔥, Zᴴ ∈ 𝔥 := fun Z hZ => by
    have := hs _ ((mem Z).1 hZ)
    rw [mem]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have hb' : ∀ P ∈ 𝔥, ∀ Q ∈ 𝔥, P * Q - Q * P ∈ 𝔥 := fun P hP Q hQ => by
    have := hb _ ((mem P).1 hP) _ ((mem Q).1 hQ)
    rw [mulc, mulc] at this
    rw [mem, Matrix.mul_sub, Matrix.sub_mul]
    exact this
  have hreg' : ∀ Y ∈ 𝔥, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag := by
    intro Y hY hYs hc
    have := hreg _ ((mem Y).1 hY) (by simp [Matrix.conjTranspose_mul, hYs, Matrix.mul_assoc]) (by rw [mulc, mulc, hc])
    rwa [cj'] at this
  refine ⟨U, hU, fun X hX => ?_⟩
  obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := GlobalTheory.T.exists_skewHermitian_add_blockTriangular 𝔥 h hanti (GlobalTheory.T.lie_algebra_function_calculus 𝔥 h ((mem _).2 hd) hb') hs' hreg' _ (mem' X hX)
  refine ⟨U * A * Uᴴ, (mem _).1 hA, U * B * Uᴴ, (mem _).1 hB, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mul, ← Matrix.mul_add, ← hAB, cj]
  · simp [Matrix.conjTranspose_mul, hAs, Matrix.mul_assoc]
  · rwa [cj']

theorem iwaOn_of_isLinRed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → PositivityTheory.Tls2.Iua.IwaOn G := by
  intro n G hG
  obtain ⟨𝔤, hiff, hV⟩ := GlobalTheory.T.lie_algebra_of_exp_local hG
  obtain ⟨hs, hb⟩ := GlobalTheory.T.lie_algebra_star_closed_bracket hG 𝔤 hiff
  obtain ⟨U, hU, hdec⟩ := alg 𝔤 hs hb
  have hexp : ∀ X ∈ 𝔤, NormedSpace.exp X ∈ G := fun X hX => by
    simpa using (hiff X).1 hX 1
  let 𝔨 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | Xᴴ = -X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.conjTranspose_add, ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        ext i j
        have := congrFun (congrFun ha i) j
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
        simp [Matrix.conjTranspose_apply, this] }
  let 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | (Uᴴ * X * U).BlockTriangular id}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul]
        exact ha.add hb
      zero_mem' := by simp [Matrix.BlockTriangular]
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        intro i j hij
        have := ha hij
        have e : Uᴴ * (r • a) * U = r • (Uᴴ * a * U) := by simp
        rw [e, Matrix.smul_apply, this, smul_zero] }
  have hloc := GlobalTheory.T.local_exp_product_decomposition hG 𝔤 𝔨 𝔟 hiff hV inf_le_left inf_le_left (fun X hX => by
    obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := hdec X hX
    rw [hAB]
    exact Submodule.add_mem_sup ⟨hA, hAs⟩ ⟨hB, hBt⟩)
  obtain h := GlobalTheory.T.cartan_local_to_global hG U hU (by
    filter_upwards [hloc] with g hg hgG
    obtain ⟨X, hX, Y, hY, rfl⟩ := hg hgG
    exact ⟨_, ⟨hexp X hX.1, exp_mem_unitaryGroup X hX.2⟩, _, hexp Y hY.1, rfl, GlobalTheory.T.exp_block_triangular U Y hU hY.2⟩)
  exact ⟨U, hU, h⟩

end GlobalTheory.CompanionTheory.IwaGen
