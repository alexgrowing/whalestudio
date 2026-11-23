import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameComplement

private theorem cT_sig_eq_conjTranspose {m k : Type} (M : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

private theorem conjTranspose_submatrix_mul_mul_submatrix {R k l m : Type} [CommRing R] [StarRing R] [Fintype k]
    (B : Matrix k l R) (M : Matrix k k R) (f : m → l) :
    (B.submatrix id f)ᴴ * M * B.submatrix id f = (Bᴴ * M * B).submatrix f f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem Jpq_det_ne_zero (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  unfold Formalism.UG.Jpq
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_neg]

private theorem conjTranspose_submatrix_mul_reindex_mul_submatrix {n k : Type} [Fintype n] [Fintype k] (e : n ≃ k)
    (Q : Matrix n k ℂ) (J : Matrix n n ℂ) :
    (Q.submatrix e.symm id)ᴴ * J.reindex e e * Q.submatrix e.symm id = Qᴴ * J * Q := by
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

theorem hasSignature_of_frame {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (hn : Fintype.card n = p + q) (Q : Matrix n (Fin p ⊕ Fin q) ℂ) (hQ : Qᴴ * J * Q = Formalism.UG.Jpq p q) :
    Formalism.UG.HasSignature J p q := by
  classical
  have hc : Fintype.card n = Fintype.card (Fin p ⊕ Fin q) := by simp [hn]
  obtain ⟨e⟩ : Nonempty (n ≃ Fin p ⊕ Fin q) := ⟨Fintype.equivOfCardEq hc⟩
  have hP := conjTranspose_submatrix_mul_reindex_mul_submatrix e Q J
  rw [hQ] at hP
  have hdet : (Q.submatrix e.symm id).det ≠ 0 := by
    intro h0
    apply Jpq_det_ne_zero p q
    rw [← hP, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hu : IsUnit (Q.submatrix e.symm id) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨e, hu.unit, ?_⟩
  rw [IsUnit.unit_spec, cT_sig_eq_conjTranspose]
  exact hP

private theorem card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Formalism.UG.Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using Fintype.card_congr e, (P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  rw [cT_sig_eq_conjTranspose] at hP
  rw [← hP, ← conjTranspose_submatrix_mul_reindex_mul_submatrix e ((P : Matrix _ _ ℂ).submatrix e id) J]
  simp

private theorem Jpq_eq_diagonal_elim_one_neg_one (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i|i) (j|j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h]
  · simp [Formalism.UG.Jpq]
  · simp [Formalism.UG.Jpq]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h]

theorem hasSignature_fromBlocks {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G : Matrix n n ℂ} {H : Matrix m m ℂ} {p q p' q' : ℕ}
    (hG : Formalism.UG.HasSignature G p q) (hH : Formalism.UG.HasSignature H p' q') :
    Formalism.UG.HasSignature (fromBlocks G 0 0 H) (p + p') (q + q') := by
  classical
  obtain ⟨hn, Q1, hQ1⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hG
  obtain ⟨hm, Q2, hQ2⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hH
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin p ⊕ Fin q) ⊕ (Fin p' ⊕ Fin q') ≃ Fin (p + p') ⊕ Fin (q + q'),
      σ = (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    ⟨_, rfl⟩
  apply hasSignature_of_frame (by rw [Fintype.card_sum, hn, hm]; omega)
    ((Matrix.fromBlocks Q1 0 0 Q2).submatrix id σ.symm)
  rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hQ1, hQ2]
  rw [Jpq_eq_diagonal_elim_one_neg_one, Jpq_eq_diagonal_elim_one_neg_one, Jpq_eq_diagonal_elim_one_neg_one, Matrix.fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rcases y with (a|a)|(a|a) <;> simp [hσ]

section

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_det_ne (S : Formalism.BasicNotions.HSpace E) : S.gram.det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : ∀ i, S.hT (S.frame i) (∑ j, c j • S.frame j) = 0 := by
    intro i
    have h2 := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Formalism.BasicNotions.HSpace.gram] at h2
    rw [← h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hy : ∀ x, S.hT x (∑ j, c j • S.frame j) = 0 := by
    intro x
    rw [← S.frame.sum_repr x, map_sum S.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  have hy0 := S.nondeg.2 _ hy
  exact hc0 (funext (Fintype.linearIndependent_iff.mp S.frame.linearIndependent c hy0))

theorem exists_basis (X Y : Formalism.BasicNotions.HSpace E) (ι : X.V →ₗ[E] Y.V) (hι : X.IsIsomEmb Y ι) {c : ℕ}
    (hc : Y.rank = X.rank + c) :
    ∃ b : Fin c → Y.V, (∀ i x, Y.hT (ι x) (b i) = 0) ∧
      LinearIndependent E (Sum.elim (fun a => ι (X.frame a)) b) := by
  classical
  let φ : Y.V →ₗ[E] (Fin X.rank → E) := LinearMap.pi fun i => Y.hT (ι (X.frame i))
  have hker : ∀ y ∈ LinearMap.ker φ, ∀ x, Y.hT (ι x) y = 0 := by
    intro y hy x
    have h1 : ∀ i, Y.hT (ι (X.frame i)) y = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hy) i
      simpa [φ] using this
    rw [← X.frame.sum_repr x, map_sum ι, map_sum Y.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  have hinj : ∀ x, (∀ x', Y.hT (ι x') (ι x) = 0) → x = 0 := fun x h =>
    X.nondeg.2 x fun x' => by rw [← hι x' x]; exact h x'
  have hk : c ≤ Module.finrank E (LinearMap.ker φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ X.rank := by
      simpa using Submodule.finrank_le (LinearMap.range φ)
    rw [Y.rank_eq] at h1
    omega
  let bk := Module.finBasis E (LinearMap.ker φ)
  obtain ⟨b, hbk, hbli⟩ : ∃ b : Fin c → Y.V, (∀ i, b i ∈ LinearMap.ker φ) ∧ LinearIndependent E b :=
    ⟨fun i => (bk (Fin.castLE hk i) : Y.V), fun i => (bk _).2,
      (bk.linearIndependent.comp _ (Fin.castLE_injective hk)).map' _ (Submodule.ker_subtype _)⟩
  have hιker : LinearMap.ker ι = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun x hx => hinj x fun x' => by rw [hx, map_zero]
  have hv1 : LinearIndependent E (fun a => ι (X.frame a)) := X.frame.linearIndependent.map' ι hιker
  refine ⟨b, fun i x => hker _ (hbk i) x, LinearIndependent.sum_type hv1 hbli ?_⟩
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hr : v ∈ LinearMap.range ι :=
    (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact LinearMap.mem_range_self ι _)) hv
  have hk' : v ∈ LinearMap.ker φ := (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbk i)) hv'
  obtain ⟨x0, rfl⟩ := hr
  rw [hinj x0 fun x' => hker _ hk' x', map_zero]

private theorem exists_det_ne_zero_gram_basis_eq_conj_gram (S : Formalism.BasicNotions.HSpace E) {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : Module.Basis κ E S.V) (e : Fin S.rank ≃ κ) :
    ∃ P : Matrix (Fin S.rank) (Fin S.rank) E, P.det ≠ 0 ∧
      (Matrix.of fun i j => S.hT (w i) (w j)).submatrix e e = Pᴴ * S.gram * P := by
  classical
  refine ⟨(S.frame.toMatrix w).submatrix id e, ?_, ?_⟩
  · have h1 : (S.frame.toMatrix w).submatrix id e * (w.toMatrix S.frame).submatrix e id = 1 := by
      rw [Matrix.submatrix_mul_equiv, S.frame.toMatrix_mul_toMatrix_flip w, Matrix.submatrix_id_id]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have hN : (Matrix.of fun a i => S.frame.repr (w i) a) = S.frame.toMatrix w := by
      ext a i
      simp [Module.Basis.toMatrix_apply]
    rw [Formalism.BasicNotions.gram_family S w, hN, conjTranspose_submatrix_mul_mul_submatrix]

theorem det_gram_basis (Y : Formalism.BasicNotions.HSpace E) {κ : Type} [Fintype κ] [DecidableEq κ] (w : Module.Basis κ E Y.V) :
    ∃ a : E, a ≠ 0 ∧ Y.gram.det = star a * a * (Matrix.of fun i l => Y.hT (w i) (w l)).det := by
  classical
  have hcard : Fintype.card κ = Y.rank := by rw [← Module.finrank_eq_card_basis w, Y.rank_eq]
  obtain ⟨P, hP0, hP⟩ := exists_det_ne_zero_gram_basis_eq_conj_gram Y w (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨(P.det)⁻¹, inv_ne_zero hP0, ?_⟩
  have hd : (Matrix.of fun i l => Y.hT (w i) (w l)).det = star P.det * Y.gram.det * P.det := by
    rw [← Matrix.det_submatrix_equiv_self (Fintype.equivFinOfCardEq hcard).symm, hP, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_conjTranspose]
  rw [hd, star_inv₀]
  have hs : star P.det ≠ 0 := star_ne_zero.mpr hP0
  calc Y.gram.det = ((star P.det)⁻¹ * star P.det) * ((P.det)⁻¹ * P.det) * Y.gram.det := by
        rw [inv_mul_cancel₀ hs, inv_mul_cancel₀ hP0]; ring
    _ = (star P.det)⁻¹ * (P.det)⁻¹ * (star P.det * Y.gram.det * P.det) := by ring

private theorem posIndex_Jpq_and_negIndex_Jpq (p q : ℕ) :
    GlobalTheory.Inertia.posIndex (Formalism.UG.Jpq p q) = p ∧ GlobalTheory.Inertia.negIndex (Formalism.UG.Jpq p q) = q := by
  have h1 : (1 : Matrix (Fin p) (Fin p) ℂ).IsHermitian := Matrix.isHermitian_one
  have h2 : (-1 : Matrix (Fin q) (Fin q) ℂ).IsHermitian := Matrix.isHermitian_one.neg
  have hp1 : GlobalTheory.Inertia.posIndex (1 : Matrix (Fin p) (Fin p) ℂ) = p := by
    rw [← Matrix.diagonal_one, GlobalTheory.Inertia.posIndex_diagonal]; simp
  have hn1 : GlobalTheory.Inertia.negIndex (1 : Matrix (Fin q) (Fin q) ℂ) = 0 := by
    rw [← Matrix.diagonal_one, GlobalTheory.Inertia.negIndex_diagonal]; simp
  have hp1' : GlobalTheory.Inertia.posIndex (1 : Matrix (Fin q) (Fin q) ℂ) = q := by
    rw [← Matrix.diagonal_one, GlobalTheory.Inertia.posIndex_diagonal]; simp
  have hn1' : GlobalTheory.Inertia.negIndex (1 : Matrix (Fin p) (Fin p) ℂ) = 0 := by
    rw [← Matrix.diagonal_one, GlobalTheory.Inertia.negIndex_diagonal]; simp
  unfold Formalism.UG.Jpq
  rw [GlobalTheory.Inertia.posIndex_fromBlocks h1 h2, GlobalTheory.Inertia.negIndex_fromBlocks h1 h2,
    GlobalTheory.Inertia.posIndex_neg, GlobalTheory.Inertia.negIndex_neg, hp1, hn1', hn1, hp1']
  simp

private theorem posIndex_negIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) :
    GlobalTheory.Inertia.posIndex J = p ∧ GlobalTheory.Inertia.negIndex J = q := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_sig_eq_conjTranspose] at hP
  have hR : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det ≠ 0 := by
    have h1 : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det =
        starRingEnd ℂ (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det := by
      rw [RingHom.map_det]; rfl
    rw [h1, map_ne_zero]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ =
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hC : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    ext i j; simp
  have hK := GlobalTheory.Inertia.posIndex_congr (J.reindex e e) hR
  have hK' := GlobalTheory.Inertia.negIndex_congr (J.reindex e e) hR
  rw [hA, hC, hP] at hK hK'
  have hJ : J.reindex e e = J.submatrix e.symm e.symm := rfl
  rw [hJ, GlobalTheory.Inertia.posIndex_submatrix_equiv] at hK
  rw [hJ, GlobalTheory.Inertia.negIndex_submatrix_equiv] at hK'
  exact ⟨hK.symm.trans (posIndex_Jpq_and_negIndex_Jpq p q).1, hK'.symm.trans (posIndex_Jpq_and_negIndex_Jpq p q).2⟩

private theorem hasSignature_of_posIndex_of_negIndex {c p q : ℕ} {G : Matrix (Fin c) (Fin c) ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) (hp : GlobalTheory.Inertia.posIndex G = p) (hq : GlobalTheory.Inertia.negIndex G = q) :
    Formalism.UG.HasSignature G p q := by
  have hpq : p + q = c := by
    have := GlobalTheory.Inertia.posIndex_add_negIndex hG hG0
    simpa [hp, hq] using this
  obtain ⟨e⟩ : Nonempty (Fin c ≃ Fin p ⊕ Fin q) := ⟨(finCongr hpq.symm).trans finSumFinEquiv.symm⟩
  have hJh : (Formalism.UG.Jpq p q).IsHermitian := by
    unfold Formalism.UG.Jpq
    exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp) Matrix.isHermitian_one.neg
  have hH : ((Formalism.UG.Jpq p q).submatrix e e).IsHermitian := hJh.submatrix e
  have hH0 : ((Formalism.UG.Jpq p q).submatrix e e).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self]; exact Jpq_det_ne_zero p q
  have hHp : GlobalTheory.Inertia.posIndex G = GlobalTheory.Inertia.posIndex ((Formalism.UG.Jpq p q).submatrix e e) := by
    rw [GlobalTheory.Inertia.posIndex_submatrix_equiv, (posIndex_Jpq_and_negIndex_Jpq p q).1, hp]
  obtain ⟨P, hP0, hP⟩ := (GlobalTheory.Inertia.exists_congr_iff_posIndex_eq hG hG0 hH hH0).mpr hHp
  apply hasSignature_of_frame (by simp [hpq]) ((P.map (starRingEnd ℂ)).submatrix id e.symm)
  rw [conjTranspose_submatrix_mul_mul_submatrix]
  have hA : (P.map (starRingEnd ℂ))ᴴ = Pᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  rw [hA, hP]
  simp

private theorem isHermitian_map_gram_of_star_compatible (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (v : ι → S.V) :
    ((Matrix.of fun i j => S.hT (v i) (v j)).map τ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← starRingEnd_apply, ← hτ]
  congr 1
  have h := S.herm.eq (v j) (v i)
  rwa [starRingEnd_apply] at h

theorem exists_complement (hτ : ∀ (τ : E →+* ℂ) a, τ (star a) = starRingEnd ℂ (τ a))
    (X Y : Formalism.BasicNotions.HSpace E) (ι : X.V →ₗ[E] Y.V) (hι : X.IsIsomEmb Y ι) {c p q : ℕ}
    (hc : Y.rank = X.rank + c) (hX : ∀ τ : E →+* ℂ, Formalism.UG.HasSignature (X.gram.map τ) X.rank 0)
    (hY : ∀ τ : E →+* ℂ, Formalism.UG.HasSignature (Y.gram.map τ) (X.rank + p) q) :
    ∃ b : Fin c → Y.V, (∀ i x, Y.hT (ι x) (b i) = 0) ∧ (Matrix.of fun i l => Y.hT (b i) (b l)).det ≠ 0 ∧
      (∀ τ : E →+* ℂ, Formalism.UG.HasSignature ((Matrix.of fun i l => Y.hT (b i) (b l)).map τ) p q) ∧
      ∃ a : E, a ≠ 0 ∧ Y.gram.det = star a * a * X.gram.det * (Matrix.of fun i l => Y.hT (b i) (b l)).det := by
  classical
  obtain ⟨b, hbo, hbli⟩ := exists_basis X Y ι hι hc
  have hbo' : ∀ i x, Y.hT (b i) (ι x) = 0 := by
    intro i x
    rw [← Y.herm.eq (ι x) (b i), hbo i x, map_zero]
  have hι' : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := hι
  have hcard : Fintype.card (Fin X.rank ⊕ Fin c) = Module.finrank E Y.V := by
    rw [Y.rank_eq, hc]; simp
  obtain ⟨w, hw⟩ : ∃ w : Module.Basis (Fin X.rank ⊕ Fin c) E Y.V,
      ⇑w = Sum.elim (fun a => ι (X.frame a)) b :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank' _ hbli hcard⟩
  have hGw : (Matrix.of fun i l => Y.hT (w i) (w l)) =
      Matrix.fromBlocks X.gram 0 0 (Matrix.of fun i l => Y.hT (b i) (b l)) := by
    ext (i|i) (l|l) <;> simp [hw, hι', hbo, hbo', Formalism.BasicNotions.HSpace.gram]
  have hdetY : Y.gram.det ≠ 0 := gram_det_ne Y
  obtain ⟨a, ha, hYa⟩ := det_gram_basis Y w
  rw [hGw, Matrix.det_fromBlocks_zero₂₁] at hYa
  have hGb : (Matrix.of fun i l => Y.hT (b i) (b l)).det ≠ 0 := by
    intro h0; apply hdetY; rw [hYa, h0, mul_zero, mul_zero]
  refine ⟨b, hbo, hGb, ?_, a, ha, by rw [hYa]; ring⟩
  intro τ
  have hXs := posIndex_negIndex_of_hasSignature (hX τ)
  have hYs := posIndex_negIndex_of_hasSignature (hY τ)
  have hcard' : Fintype.card (Fin Y.rank) = Fintype.card (Fin X.rank ⊕ Fin c) := by simp [hc]
  obtain ⟨eY⟩ : Nonempty (Fin Y.rank ≃ Fin X.rank ⊕ Fin c) := ⟨Fintype.equivOfCardEq hcard'⟩
  obtain ⟨P, hP0, hP⟩ := exists_det_ne_zero_gram_basis_eq_conj_gram Y w eY
  have hA : (Pᴴ).map τ = ((P.map τ).map (starRingEnd ℂ))ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply, hτ]
  have hC : P.map τ = ((P.map τ).map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    ext i j; simp
  have hR : ((P.map τ).map (starRingEnd ℂ)).det ≠ 0 := by
    have h1 : ((P.map τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (τ P.det) := by
      rw [RingHom.map_det, RingHom.map_det]; rfl
    rw [h1, map_ne_zero, map_ne_zero]
    exact hP0
  have hK : ((Matrix.of fun i l => Y.hT (w i) (w l)).map τ).submatrix eY eY =
      ((P.map τ).map (starRingEnd ℂ))ᵀ * Y.gram.map τ *
        ((P.map τ).map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    rw [Matrix.submatrix_map, hP, Matrix.map_mul, Matrix.map_mul, hA, ← hC]
  have hpos := GlobalTheory.Inertia.posIndex_submatrix_equiv ((Matrix.of fun i l => Y.hT (w i) (w l)).map τ) eY
  have hneg := GlobalTheory.Inertia.negIndex_submatrix_equiv ((Matrix.of fun i l => Y.hT (w i) (w l)).map τ) eY
  rw [hK, GlobalTheory.Inertia.posIndex_congr _ hR] at hpos
  rw [hK, GlobalTheory.Inertia.negIndex_congr _ hR] at hneg
  have hXh : (X.gram.map τ).IsHermitian := isHermitian_map_gram_of_star_compatible X τ (hτ τ) X.frame
  have hbh := isHermitian_map_gram_of_star_compatible Y τ (hτ τ) b
  rw [hGw, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ),
    GlobalTheory.Inertia.posIndex_fromBlocks hXh hbh] at hpos
  rw [hGw, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ),
    GlobalTheory.Inertia.negIndex_fromBlocks hXh hbh] at hneg
  have hb0 : ((Matrix.of fun i l => Y.hT (b i) (b l)).map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
    exact hGb
  refine hasSignature_of_posIndex_of_negIndex hbh hb0 ?_ ?_
  · omega
  · omega

end

theorem exists_complement_XY : ∀ (D : D7) (j : ℕ), j < D.R.m → ∃ b : Fin (D.R.m - 1 - j) → (D.sp.Y j).V, (∀ i x, (D.sp.Y j).hT (D.sp.iXY j x) (b i) = 0) ∧ (Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l)).det ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature ((Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l)).map τ) ((D.R.m - 1 - j) / 2) ((D.R.m - 1 - j) - (D.R.m - 1 - j) / 2)) ∧ ∃ a : D.host.E, a ≠ 0 ∧ (D.sp.Y j).gram.det = star a * a * (D.sp.X j).gram.det * (Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l)).det := by
  intro D j hj
  have hτ : ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), τ (star a) = starRingEnd ℂ (τ a) := by
    have := D.host.isCMField_hostE
    intro τ a
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E τ a
  have hc : (D.sp.Y j).rank = (D.sp.X j).rank + (D.R.m - 1 - j) := by
    rw [D.sp.Y_rank j hj.le, D.sp.X_rank j hj.le]
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : j * (D.R.t + 1) = j * D.R.t + j := by ring
    have h2 := D.R.two_le_m
    omega
  have hX : ∀ τ : D.host.E →+* ℂ,
      Formalism.UG.HasSignature ((D.sp.X j).gram.map τ) (D.sp.X j).rank 0 := by
    intro τ
    have h := D.sp.X_sig j τ
    rw [GlobalTheory.Mem.Th.X_posDef D j hj.le τ] at h
    exact h
  have hY : ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature ((D.sp.Y j).gram.map τ)
      ((D.sp.X j).rank + (D.R.m - 1 - j) / 2) ((D.R.m - 1 - j) - (D.R.m - 1 - j) / 2) := by
    intro τ
    have h := D.sp.Y_sig j τ
    rw [D.Y_sigval j hj.le τ] at h
    have hcY : D.R.rankY j = (D.sp.X j).rank + (D.R.m - 1 - j) := by
      rw [← D.sp.Y_rank j hj.le]; exact hc
    have e1 : (Formalism.BasicNotions.sigYD D.R j).1 = (D.sp.X j).rank + (D.R.m - 1 - j) / 2 := by
      show D.R.rankY j - (D.R.m - j) / 2 = _
      rw [hcY]; omega
    have e2 : (Formalism.BasicNotions.sigYD D.R j).2 = (D.R.m - 1 - j) - (D.R.m - 1 - j) / 2 := by
      show (D.R.m - j) / 2 = _
      omega
    rw [e1, e2] at h
    exact h
  exact exists_complement hτ (D.sp.X j) (D.sp.Y j) (D.sp.iXY j) (D.sp.iXY_isom j hj) hc hX hY

end GlobalTheory.FrameComplement
