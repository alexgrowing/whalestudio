import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := by
  simp [vOf]

theorem qi_gram {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  rw [← h3]
  calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
      = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem pinv_gram (v : InfinitePlace X.B.I.F) :
    ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
  have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have h1 : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← X.B.I.P_spec v]
  calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
      = (X.B.I.P v * (X.B.I.P v)⁻¹)ᴴ * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem besselModelTransportMatrix_gram_eq {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * A0 X C w = (Jc X).map (embS D (tauOf D w)) := by
  set τ := tauOf D w
  set B := C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ with hBdef
  have hB : Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B = X.B.I.J.map (X.B.I.φ (vOf X τ)) := by
    rw [← pinv_gram X (vOf X τ), ← qi_gram X C τ, hBdef, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hA : A0 X C w = B.submatrix id (ci X) := rfl
  have hAt : (A0 X C w)ᴴ = Bᴴ.submatrix (ci X) id := by rw [hA, conjTranspose_submatrix]
  have hprod : Bᴴ.submatrix (ci X) id * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B.submatrix id (ci X) =
      (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B).submatrix (ci X) (ci X) := by
    symm
    rw [submatrix_mul (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) B (ci X) id (ci X) Function.bijective_id,
      submatrix_mul Bᴴ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (ci X) id id Function.bijective_id, submatrix_id_id]
  rw [hAt, hA, hprod, hB]
  ext i j
  simp only [submatrix_apply, map_apply, Jc, X.φ_eq, X.J_eq, pl_vOf]

theorem embedding_of_not_direct (w : InfinitePlace D.host.E) (h : ¬ Direct D w) :
    w.embedding = ComplexEmbedding.conjugate (embS D (tauOf D w)) := by
  have hw : InfinitePlace.mk (embS D (tauOf D w)) = w := (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec
  rcases InfinitePlace.embedding_mk_eq (embS D (tauOf D w)) with h1 | h1
  · rw [hw] at h1; exact (h h1).elim
  · rwa [hw] at h1

theorem isModel {θ : ℝ} (C : Choice X θ) : GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) := by
  intro w
  unfold Ac
  split_ifs with h
  · rw [besselModelTransportMatrix_gram_eq, show w.embedding = embS D (tauOf D w) from h]
  · rw [embedding_of_not_direct w h]
    have hH : (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS).map (starRingEnd ℂ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      ext i j; simp only [map_apply, Formalism.QuantumDeterminants.Hpk]; split_ifs <;> simp
    have hc : ((A0 X C w).map (starRingEnd ℂ))ᴴ = ((A0 X C w)ᴴ).map (starRingEnd ℂ) := by
      ext i j; simp [conjTranspose_apply]
    show ((A0 X C w).map (starRingEnd ℂ))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (A0 X C w).map (starRingEnd ℂ) = _
    rw [hc, ← hH, ← Matrix.map_mul, ← Matrix.map_mul, besselModelTransportMatrix_gram_eq]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem v_pos : 0 < D.host.v := by
  have := GlobalTheory.RealPlaces.one_le_rdE D
  unfold Host.v; linarith

theorem frS_ne_zero : frS D ≠ 0 := by
  have hv := v_pos (D := D)
  unfold frS Host.ka
  have : Real.pi / D.host.v / (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast this

theorem frS_pow_inv (m : ℕ) : ((frS D) ^ m)⁻¹ = (((2 * D.host.v) ^ m : ℝ) : ℂ) := by
  have hv := v_pos (D := D)
  have h : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
    unfold Host.ka; field_simp
  rw [frS, h]; push_cast; rw [inv_pow, inv_inv]

theorem star_frS : star (frS D) = frS D := by
  unfold frS; exact Complex.conj_ofReal _

theorem besselModelTransportMatrix_mulVec_coordinates {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) :
    (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) =
      C.Qi (tauOf D w) *ᵥ rv X.B.I (vOf X (tauOf D w)) (X.crd y) := by
  have hx : (fun i => embS D (tauOf D w) (crdH X y i)) =
      (fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X) := rfl
  have hx2 : ((fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X)) ∘ (ci X).symm =
      fun j => embS D (tauOf D w) (X.bas.repr y j) := by
    funext j; simp
  rw [hx, A0, submatrix_mulVec_equiv, hx2, Function.comp_id, ← mulVec_mulVec]
  congr 1
  unfold rv
  congr 1
  funext i
  rw [X.φ_eq, pl_vOf]
  simp [HidaSetting.crd, crdOf]

theorem qi_e {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.eR a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).1
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  rw [← frS_pow_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem qi_f {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.fR a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).2
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  have hs : star (frS D ^ (D.R.rS - (a : ℕ))) = frS D ^ (D.R.rS - (a : ℕ)) := by
    rw [star_pow, star_frS]
  rw [hs] at he
  rw [← frS_pow_inv, inv_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem Ac_mulVec {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) (c : ℝ)
    (j' : Fin (2 * D.R.rS + D.R.k + 1))
    (h : (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j') :
    (Ac X C w *ᵥ fun i => w.embedding (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j' := by
  unfold Ac
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd]; exact h
  · rw [embedding_of_not_direct w hd]
    have e1 : (fun i => (ComplexEmbedding.conjugate (embS D (tauOf D w))) (crdH X y i)) =
        ⇑(starRingEnd ℂ) ∘ (fun i => embS D (tauOf D w) (crdH X y i)) := by
      funext i; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e1]
    funext i
    rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← RingHom.map_mulVec, h]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Formalism.QuantumDeterminants.bvec]
    congr 1
    rcases eq_or_ne i j' with rfl | hij
    · simp
    · simp [hij]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

theorem model_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  intro D X θ C u
  refine ⟨isModel X C, fun w a => ⟨?_, ?_⟩⟩
  · have hP : (fun i => w.embedding (Pc X u i a.castSucc)) = fun i => w.embedding (crdH X (X.eX a) i) := by
      funext i; simp [Pc]
    rw [hP]
    exact Ac_mulVec X C w _ _ _ (by rw [besselModelTransportMatrix_mulVec_coordinates]; exact qi_e X C _ a)
  · have hf : (fun i => w.embedding (fc X i a)) = fun i => w.embedding (crdH X (X.fY a) i) := rfl
    rw [hf]
    have := Ac_mulVec X C w (X.fY a) ((2 * D.host.v) ^ (D.R.rS - (a : ℕ)))⁻¹ (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a)
      (by rw [besselModelTransportMatrix_mulVec_coordinates]; have := qi_f X C (tauOf D w) a; push_cast at this ⊢; exact this)
    unfold sc; push_cast at this ⊢; exact this

end GlobalTheory.CovDom.ModelIso
