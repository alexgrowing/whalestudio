import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAtInfinityAdeleWithComplexComponeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConjStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ConjCartan

open scoped ComplexOrder in

theorem exists_conj_cartan_matrix : ∀ (n : ℕ) (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ), Mᴴ = M → IsCartan M θ₁ → IsCartan M θ₂ →
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  intro n M θ₁ θ₂ hM h1 h2
  have key : ∀ θ, IsCartan M θ → θ.map star * θ.map star = 1 ∧ (θ.map star)ᴴ * M * θ.map star = M ∧
      (M * θ.map star).PosDef := by
    rintro θ ⟨hθ, hu, hp⟩
    have hS : θ.map star = θᵀᴴ := rfl
    have hT : (θ.map star)ᴴ = θᵀ := by rw [hS, Matrix.conjTranspose_conjTranspose]
    have hSS : θ.map star * θ.map star = 1 := by
      rw [hS, ← Matrix.conjTranspose_mul, ← Matrix.transpose_mul, hθ, Matrix.transpose_one, Matrix.conjTranspose_one]
    have hMS : M * θ.map star = θᵀ * M := by
      calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [hu]
        _ = θᵀ * M := by rw [Matrix.mul_assoc _ (θ.map star), hSS, Matrix.mul_one]
    have hH : (M * θ.map star)ᴴ = M * θ.map star := by
      rw [Matrix.conjTranspose_mul, hT, hM, hMS]
    refine ⟨hSS, by rw [hT]; exact hu, ?_⟩
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x hx => ?_⟩
    have hx' : star x ≠ 0 := by simpa using hx
    have hre := hp (star x) hx'
    have e1 : star x ⬝ᵥ (M * θ.map star) *ᵥ x = (θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x) := by
      rw [star_star, hMS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : star (star x ⬝ᵥ (M * θ.map star) *ᵥ x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
      conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [Complex.lt_def]
    refine ⟨by rw [e1]; simpa using hre, ?_⟩
    have h3 := congrArg Complex.im e2
    have h4 : (star (star x ⬝ᵥ (M * θ.map star) *ᵥ x)).im = -(star x ⬝ᵥ (M * θ.map star) *ᵥ x).im :=
      Complex.conj_im _
    rw [Complex.zero_im]; linarith
  obtain ⟨hs1, hs2, hs3⟩ := key θ₁ h1
  obtain ⟨ht1, ht2, ht3⟩ := key θ₂ h2
  set S₁ := θ₁.map star
  set S₂ := θ₂.map star
  obtain ⟨p, q, B, B', hBB, hB'B, hBG, hBs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n M S₁ hs1 hs2 hs3
  set D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hDh : Dᴴ = D := by simp [D, Matrix.fromBlocks_conjTranspose]
  have hDD : D * D = 1 := by simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set T := B' * S₂ * B
  have hTT : T * T = 1 := by
    calc T * T = B' * S₂ * (B * B') * S₂ * B := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, Matrix.mul_assoc B', ht1, Matrix.mul_one, hB'B]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    have := congrArg (B'.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hB'B] using this
  have hDT : (D * T).PosDef := by
    have h := ht3.conjTranspose_mul_mul_same hinj
    have e : Bᴴ * (M * S₂) * B = D * T := by
      calc Bᴴ * (M * S₂) * B = Bᴴ * M * (B * B') * S₂ * B := by rw [hBB]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = D * T := by rw [← hBG]; simp only [T, Matrix.mul_assoc]
    rwa [e] at h
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.cartanInvolution_conj_of_posDef _ D T hDh hDD hTT hDT

  have haL : (D * aᴴ * D) * a = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc aᴴ, ha1, hDD]
  set U := B * a * B'
  set V := B * (D * aᴴ * D) * B'
  have hVU : V * U = 1 := by
    calc V * U = B * (D * aᴴ * D) * (B' * B) * a * B' := by simp only [V, U, Matrix.mul_assoc]
      _ = 1 := by rw [hB'B, Matrix.mul_one, Matrix.mul_assoc B, haL, Matrix.mul_one, hBB]
  have hUU : Uᴴ * M * U = M := by
    have hBh : B'ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc Uᴴ * M * U = B'ᴴ * (aᴴ * (Bᴴ * M * B) * a) * B' := by
          simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * (Bᴴ * M * B) * B' := by rw [hBG, ha1]
      _ = (B'ᴴ * Bᴴ) * M * (B * B') := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBh, hBB, Matrix.one_mul, Matrix.mul_one]
  have hB'S : B' * S₁ = D * B' := by
    calc B' * S₁ = B' * S₁ * (B * B') := by rw [hBB, Matrix.mul_one]
      _ = B' * (S₁ * B) * B' := by simp only [Matrix.mul_assoc]
      _ = B' * (B * D) * B' := congrArg (fun Z => B' * Z * B') hBs
      _ = (B' * B) * D * B' := by simp only [Matrix.mul_assoc]
      _ = D * B' := by rw [hB'B, Matrix.one_mul]
  have hUS : U * S₁ = S₂ * U := by
    calc U * S₁ = B * (a * D) * B' := by simp only [U, Matrix.mul_assoc, hB'S]
      _ = B * (T * a) * B' := by rw [ha2]
      _ = (B * B') * S₂ * (B * a * B') := by simp only [T, Matrix.mul_assoc]
      _ = S₂ * U := by rw [hBB, Matrix.one_mul]
  refine ⟨U.map star, V.map star, ?_, ?_, ?_⟩
  · have hUV : U * V = 1 := mul_eq_one_comm.1 hVU
    have : (U * V).map star = (1 : Matrix (Fin n) (Fin n) ℂ).map star := by rw [hUV]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).map star by simp, ← this]; ext i j; simp [Matrix.mul_apply, star_sum]
  · have e : (U.map star)ᵀ = Uᴴ := rfl
    rw [e, show (U.map star).map star = U by ext i j; simp, hUU]
  · have : (U * S₁).map star = (S₂ * U).map star := by rw [hUS]
    have e1 : (U * S₁).map star = U.map star * θ₁ := by ext i j; simp [S₁, Matrix.mul_apply, star_sum]
    have e2 : (S₂ * U).map star = θ₂ * U.map star := by ext i j; simp [S₂, Matrix.mul_apply, star_sum]
    rw [← e1, ← e2, this]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

variable (F E) in

def archIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c z hz u hu => by
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem cA_mem_archIdeal (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ archIdeal F E) : cA σ z ∈ archIdeal F E :=
  fun u hu => by rw [← map_smul, hz u hu, map_zero]

end GlobalTheory.ConjCartan

namespace GlobalTheory.ConjCartan

theorem mapMatrix_transpose {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : f.mapMatrix Aᵀ = (f.mapMatrix A)ᵀ := rfl

theorem conj_cartan_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have cm := hB.cm
  have hM : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← cm.2.2.2 (B.emb w).1, hX.herm]
  have hU := fun w => exists_conj_cartan_matrix n _ (X.θ w) (Y.θ w) (hM w) (hX.cartan w) (hY.cartan w)
  choose u v huv hun hint using hU
  choose lift hlat hlev using GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents F E σ cm B.emb
  let π := Ideal.Quotient.mk (archIdeal F E)
  let Dm : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (u w - 1) i j
  let Dv : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (v w - 1) i j
  have hDm : π.mapMatrix Dm = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDv : π.mapMatrix Dv = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDc : π.mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (cA_mem_archIdeal σ (hlat _))
  have hDmw : ∀ w, (piInf (B.emb w)).mapMatrix Dm = u w - 1 := fun w => by
    ext i j; exact hlev _ w
  have hDvw : ∀ w, (piInf (B.emb w)).mapMatrix Dv = v w - 1 := fun w => by
    ext i j; exact hlev _ w
  have zero : ∀ Z : Matrix (Fin n) (Fin n) (AE F E), π.mapMatrix Z = 0 → (∀ w, (piInf (B.emb w)).mapMatrix Z = 0) → Z = 0 := by
    intro Z h1 h2; ext i j
    exact GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents F E σ cm B.emb _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j))
      (fun w => congrFun (congrFun (h2 w) i) j)
  have hGH : (1 + Dm) * (1 + Dv) = 1 := by
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDm, hDv]; simp
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDmw, hDvw, add_sub_cancel, add_sub_cancel, huv w, sub_self]
  let g0 : GL (Fin n) (AE F E) := ⟨1 + Dm, 1 + Dv, hGH, mul_eq_one_comm.1 hGH⟩
  have hcw : ∀ w, (piInf (B.emb w)).mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = (u w).map star - 1 := fun w => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (cA σ).toRingHom (Dm i j) = cA σ (Dm i j) from rfl, GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj F E σ cm w (B.emb w)]
    simp only [Dm, Matrix.of_apply]
    rw [hlev]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, star_sub]
    split_ifs <;> simp
  have hJw : ∀ w, (piInf (B.emb w)).mapMatrix (incM F X.J) = X.J.map (B.emb w).1 := fun w => by
    ext i j; simp [incM, piInf_inclR]
  have hUG : g0 ∈ UG (cA σ) (incM F X.J) := by
    change (1 + Dm)ᵀ * incM F X.J * (cA σ).toRingHom.mapMatrix (1 + Dm) = incM F X.J
    rw [map_add, map_one]
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDm, hDc]; simp
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDmw, hcw, hJw,
        add_sub_cancel, add_sub_cancel, hun w, sub_self]
  refine ⟨⟨g0, hUG⟩, ?_, fun w => ?_⟩
  · intro a ha
    show a • ((1 + Dm) - 1) = 0
    ext i j
    simp only [add_sub_cancel_left, Matrix.smul_apply, Matrix.zero_apply]
    exact hlat _ a ha
  · have : (mat (⟨g0, hUG⟩ : UA σ X.J)).map (piInf (B.emb w)) = u w := by
      show (piInf (B.emb w)).mapMatrix (1 + Dm) = u w
      rw [map_add, map_one, hDmw]; abel
    rw [this]; exact hint w

end GlobalTheory.ConjCartan
