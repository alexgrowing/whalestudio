import Mathlib
import GroundTheory.AutomorphicForms.HermitianOrthogonal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCoordProper
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace UnipotentCoordProper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipVec (H : Matrix ι ι ℂ) (X W₀ u e : ι → ℂ) : ι → ℂ :=
  e + (star X ⬝ᵥ (H *ᵥ e)) • u - (star u ⬝ᵥ (H *ᵥ (e - (star X ⬝ᵥ (H *ᵥ e)) • W₀))) • X

def unipMat (H : Matrix ι ι ℂ) (X W₀ u : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => unipVec H X W₀ u (Pi.single j 1) i

theorem continuous_unipMat (H : Matrix ι ι ℂ) (X W₀ : ι → ℂ) :
    Continuous (unipMat H X W₀) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hc : Continuous fun u => unipVec H X W₀ u (Pi.single j 1) := by
    unfold unipVec
    apply Continuous.sub
    · exact continuous_const.add (continuous_const_smul _)
    · exact (continuous_star.dotProduct continuous_const).smul continuous_const
  exact (continuous_apply i).comp hc

theorem eq_unipMat {H G : Matrix ι ι ℂ} {X W₀ : ι → ℂ} (hU : Gᴴ * H * G = H)
    (hX : G *ᵥ X = X) (hz : ∀ z, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, G *ᵥ z = z + c • X)
    (hXW : star X ⬝ᵥ (H *ᵥ W₀) = 1) (hWX : star W₀ ⬝ᵥ (H *ᵥ X) = 1) :
    G = unipMat H X W₀ (G *ᵥ W₀ - W₀) := by
  have ip : ∀ a b, star (G *ᵥ a) ⬝ᵥ (H *ᵥ (G *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hU]
  set u := G *ᵥ W₀ - W₀ with hu
  have huX : star u ⬝ᵥ (H *ᵥ X) = 0 := by
    have := ip W₀ X
    rw [hX] at this
    simp only [hu, star_sub, sub_dotProduct, this, sub_self]
  have key : ∀ e, G *ᵥ e = unipVec H X W₀ u e := by
    intro e
    set b := star X ⬝ᵥ (H *ᵥ e) with hb
    set z := e - b • W₀ with hzdef
    have hXz : star X ⬝ᵥ (H *ᵥ z) = 0 := by
      simp only [hzdef, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hXW, smul_eq_mul,
        mul_one, b, sub_self]
    obtain ⟨c, hc⟩ := hz z hXz
    have hGW : G *ᵥ W₀ = W₀ + u := by rw [hu]; abel
    have hc' : c = -(star u ⬝ᵥ (H *ᵥ z)) := by
      have := ip W₀ z
      rw [hc, hGW] at this
      simp only [star_add, add_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
        hWX, huX, smul_eq_mul] at this
      linear_combination this
    have he : e = z + b • W₀ := by rw [hzdef]; abel
    have : G *ᵥ e = z + c • X + b • (W₀ + u) := by
      rw [he, mulVec_add, mulVec_smul, hc, hGW]
    rw [this, hc']
    simp only [unipVec, ← hb, ← hzdef]
    rw [he]
    simp only [smul_add, neg_smul]
    abel
  ext i j
  rw [unipMat, of_apply, ← key, mulVec_single_one, col_apply]

end UnipotentCoordProper

open UnipotentCoordProper

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipotentCoordProper.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCoordProper.Statement h v := by
  intro x₀ w₀ hp K hK
  have hherm := HermAtPlace.proof h v
  set H := gramAt h v
  set X := vecAt v x₀
  set W0 := vecAt v w₀
  have hXW : ∀ w, star (X w) ⬝ᵥ (H w *ᵥ W0 w) = 1 := fun w => by
    rw [← hherm, hp.2.2, map_one]
  have hWX : ∀ w, star (W0 w) ⬝ᵥ (H w *ᵥ X w) = 1 := fun w => by
    rw [← hherm, ← h.conj_toSesq, hp.2.2, map_one, map_one]
  have hHdet : ∀ w, IsUnit (H w).det := fun w => by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  set Φ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w => unipMat (H w) (X w) (W0 w)
  set Ψ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w u => (H w)⁻¹ * (Φ w u)ᴴ * H w
  have hΦc : ∀ w, Continuous (Φ w) := fun w => continuous_unipMat _ _ _
  have hΨc : ∀ w, Continuous (Ψ w) := fun w =>
    (continuous_const.matrix_mul (hΦc w).matrix_conjTranspose).matrix_mul continuous_const
  have key : ∀ (n : unipRadical h v x₀) (w : InfinitePlace E),
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
        Φ w (unipCoord h v x₀ w₀ n w) ∧
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) =
        Ψ w (unipCoord h v x₀ w₀ n w) := by
    intro n w
    set G : Matrix ι ι ℂ := (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    have hU : Gᴴ * H w * G = H w := (mem_archUnitary.mp (n : archUnitary h v).2) w
    have hG : G = Φ w (unipCoord h v x₀ w₀ n w) :=
      eq_unipMat hU ((n.2 w).1) ((n.2 w).2) (hXW w) (hWX w)
    refine ⟨hG, ?_⟩
    set Gi : Matrix ι ι ℂ :=
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)
    have hGGi : G * Gi = 1 := Units.mul_inv _
    show Gi = (H w)⁻¹ * (Φ w (unipCoord h v x₀ w₀ n w))ᴴ * H w
    rw [← hG]
    calc Gi = (H w)⁻¹ * (Gᴴ * H w * G) * Gi := by
          rw [hU, Matrix.nonsing_inv_mul _ (hHdet w), Matrix.one_mul]
      _ = (H w)⁻¹ * Gᴴ * H w * (G * Gi) := by simp only [Matrix.mul_assoc]
      _ = (H w)⁻¹ * Gᴴ * H w := by rw [hGGi, Matrix.mul_one]
  set Kw : InfinitePlace E → Set (ι → ℂ) := fun w => (fun y => y w) '' K
  have hKw : ∀ w, IsCompact (Kw w) := fun w => hK.image (continuous_apply w)
  set C : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ((Φ w '' Kw w) ×ˢ (MulOpposite.unop ⁻¹' (Ψ w '' Kw w)))
  have hC : ∀ w, IsCompact (C w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (((hKw w).image (hΦc w)).prod
        (MulOpposite.opHomeomorph.isCompact_preimage.mp ((hKw w).image (hΨc w))))
  have hS : IsClosed {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K} :=
    hK.isClosed.preimage (continuous_unipCoord h v x₀ w₀)
  rw [Subtype.isCompact_iff, Subtype.isCompact_iff, Set.image_image]
  refine (isCompact_univ_pi hC).of_isClosed_subset ?_ ?_
  · rw [← Set.image_image]
    exact (isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _
      ((isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.isClosedMap _ hS)
  · rintro _ ⟨n, hn, rfl⟩ w -
    exact ⟨⟨_, ⟨_, hn, rfl⟩, (key n w).1.symm⟩, ⟨_, ⟨_, hn, rfl⟩, (key n w).2.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
