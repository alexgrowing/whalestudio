import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.WittSign

open GlobalTheory.FrameComplement

theorem hasSignature_hyperbolic (i : ℕ) :
    Formalism.UG.HasSignature (fromBlocks 0 1 1 0 : Matrix (Fin i ⊕ Fin i) (Fin i ⊕ Fin i) ℂ) i i := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (p := i) (q := i) (by simp)
    (Matrix.fromBlocks (1 : Matrix (Fin i) (Fin i) ℂ) 1 ((1 / 2 : ℂ) • 1) (-((1 / 2 : ℂ) • 1))) ?_
  rw [Formalism.UG.P.Jpq_eq_diagonal, ← Matrix.fromBlocks_diagonal]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext a b <;> simp [Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> norm_num

theorem hasSignature_of_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    {e : Fin p ⊕ Fin q ≃ Fin n} (he : SignCompat ε e) : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q := by
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simpa using (Fintype.card_congr e).symm)
    (P⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e) ?_
  calc (P⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) *
        (P⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)
      = ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) *
          (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * Formalism.REAL.Jm ε *
          (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e := by
        rw [h1, hPi, Matrix.mul_one, Matrix.mul_one]
    _ = Formalism.UG.Jpq p q := by
        rw [Formalism.UG.P.Jpq_eq_diagonal]
        ext a b
        have ha := he a
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat] at he
        simp [Matrix.mul_apply, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, e.injective.eq_iff]
        rcases a with a | a <;> split_ifs <;> subst_vars <;> simp_all

private theorem hT_eq_sum_frame_repr {D : D7} (T : HSp D) (x y : T.V) :
    T.hT x y = ∑ j, ∑ j', star (T.frame.repr x j) * T.gram j j' * T.frame.repr y j' := by
  conv_lhs => rw [← T.frame.sum_repr x, ← T.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, RingHom.id_apply]
  ring

private theorem gram_tauE_frame_repr_eq_hT {D : D7} (T : HSp D) (τ : D.what₂.Tau) {κ κ' : Type} (w : κ → T.V) (w' : κ' → T.V) :
    (Matrix.of fun j k => tauE D τ (T.frame.repr (w k) j))ᴴ * gramAt D T τ *
      (Matrix.of fun j k => tauE D τ (T.frame.repr (w' k) j)) =
      Matrix.of fun k l => tauE D τ (T.hT (w k) (w' l)) := by
  ext k l
  rw [Matrix.of_apply, hT_eq_sum_frame_repr]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, map_sum, map_mul,
    GlobalTheory.FockCompare.tauE_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp [gramAt, Matrix.map_apply]

private theorem exists_numbering_signCompat {n : ℕ} (ε : Fin n → Bool) :
    ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  refine ⟨Fintype.card {a // ε a = true}, Fintype.card {a // ¬ε a = true},
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl fun a => ε a = true), ?_⟩
  intro a
  rcases a with a | a
  · simpa using ((Fintype.equivFin {a // ε a = true}).symm a).2
  · simpa using ((Fintype.equivFin {a // ¬ε a = true}).symm a).2

private theorem star_mulVec_dotProduct_gram {n a b : Type} [Fintype n] [Fintype a] [Fintype b] (G : Matrix n n ℂ)
    (X : Matrix n a ℂ) (Y : Matrix n b ℂ) (x : a → ℂ) (y : b → ℂ) :
    star (X *ᵥ x) ⬝ᵥ (G *ᵥ (Y *ᵥ y)) = star x ⬝ᵥ ((Xᴴ * G * Y) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem re_star_dotProduct_self' {a : Type} [Fintype a] (x : a → ℂ) :
    (star x ⬝ᵥ x).re = ∑ j, Complex.normSq (x j) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem card_add_card_add_card_le_of_gram_frames {n : ℕ} {m₁ m₂ k : Type} [Fintype m₁] [Fintype m₂] [Fintype k]
    [DecidableEq m₁] [DecidableEq k]
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G) (A : Matrix (Fin n) m₁ ℂ) (C : Matrix (Fin n) m₂ ℂ)
    (N : Matrix (Fin n) k ℂ) (hA : Aᴴ * G * A = 1) (hAC : Aᴴ * G * C = 0) (hC : Cᴴ * G * C = 0)
    (hCi : ∀ x, C *ᵥ x = 0 → x = 0) (hN : Nᴴ * G * N = -1) :
    Fintype.card m₁ + Fintype.card m₂ + Fintype.card k ≤ n := by
  have hCA : Cᴴ * G * A = 0 := by
    have h := congrArg Matrix.conjTranspose hAC
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : ((m₁ → ℂ) × (m₂ → ℂ)) × (k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    (A.mulVecLin.coprod C.mulVecLin).coprod N.mulVecLin
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨x, z⟩, y⟩ h0
    simp only [f, LinearMap.coprod_apply, Matrix.mulVecLin_apply] at h0
    have hu : A *ᵥ x + C *ᵥ z = -(N *ᵥ y) := eq_neg_of_add_eq_zero_left h0
    have e1 : star (A *ᵥ x + C *ᵥ z) ⬝ᵥ (G *ᵥ (A *ᵥ x + C *ᵥ z)) = star x ⬝ᵥ x := by
      simp only [star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct, star_mulVec_dotProduct_gram, hA, hAC, hCA, hC,
        Matrix.one_mulVec, Matrix.zero_mulVec, dotProduct_zero, add_zero]
    have e2 : star (-(N *ᵥ y)) ⬝ᵥ (G *ᵥ (-(N *ᵥ y))) = -(star y ⬝ᵥ y) := by
      simp only [star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, star_mulVec_dotProduct_gram, hN,
        Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [hu, e2] at e1
    have r := congrArg Complex.re e1
    rw [Complex.neg_re, re_star_dotProduct_self', re_star_dotProduct_self'] at r
    have sx : 0 ≤ ∑ j, Complex.normSq (x j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    have sy : 0 ≤ ∑ j, Complex.normSq (y j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    have hx0 : x = 0 := by
      have hs : ∑ j, Complex.normSq (x j) = 0 := by linarith
      funext j
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp hs j (Finset.mem_univ _))
    have hy0 : y = 0 := by
      have hs : ∑ j, Complex.normSq (y j) = 0 := by linarith
      funext j
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp hs j (Finset.mem_univ _))
    subst hx0 hy0
    have hz : C *ᵥ z = 0 := by simpa using h0
    rw [hCi z hz]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

private theorem submatrix_inl_gram_eq_one_and_inr_eq_neg_one {n : Type} [Fintype n] {p q : ℕ} (G : Matrix n n ℂ)
    (Q : Matrix n (Fin p ⊕ Fin q) ℂ) (hQ : Qᴴ * G * Q = Formalism.UG.Jpq p q) :
    (Q.submatrix id Sum.inl)ᴴ * G * Q.submatrix id Sum.inl = 1 ∧
      (Q.submatrix id Sum.inr)ᴴ * G * Q.submatrix id Sum.inr = -1 := by
  rw [Formalism.UG.P.Jpq_eq_diagonal] at hQ
  constructor
  · ext a b
    have h := congrFun (congrFun hQ (Sum.inl a)) (Sum.inl b)
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id] at h ⊢
    rw [h]
    by_cases hab : a = b <;> simp [hab, Matrix.diagonal_apply, Matrix.one_apply]
  · ext a b
    have h := congrFun (congrFun hQ (Sum.inr a)) (Sum.inr b)
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id] at h ⊢
    rw [h]
    by_cases hab : a = b <;> simp [hab, Matrix.diagonal_apply, Matrix.one_apply]

theorem hasSignature_of_isWittLower {D : D7} {T T' : HSp D} {i : ℕ} (h : IsWittLower T T' i) (τ : D.what₂.Tau)
    {p q : ℕ} (hs : Formalism.UG.HasSignature (gramAt D T' τ) p q) :
    Formalism.UG.HasSignature (gramAt D T τ) (p + i) (q + i) := by
  obtain ⟨hrk, ι, hι, C, ⟨hCli, hCiso⟩, hFC⟩ := h
  have hι' : ∀ x y, T.hT (ι x) (ι y) = T'.hT x y := hι
  let c : Fin i → T.V := fun k => T.frame.equivFun.symm (fun j => C j k)
  have hrc : ∀ k j, T.frame.repr (c k) j = C j k := fun k j => by
    have h1 := congrFun (T.frame.equivFun.apply_symm_apply (fun j => C j k)) j
    rw [Module.Basis.equivFun_apply] at h1
    exact h1
  have hcc : ∀ k l, T.hT (c k) (c l) = 0 := by
    intro k l
    rw [hT_eq_sum_frame_repr]
    simp only [hrc]
    have h0 := congrFun (congrFun hCiso k) l
    rw [Matrix.zero_apply] at h0
    rw [← h0]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hcu : ∀ a k, T.hT (ι (T'.frame a)) (c k) = 0 := by
    intro a k
    rw [hT_eq_sum_frame_repr]
    simp only [hrc]
    have h0 := congrFun (congrFun hFC a) k
    rw [Matrix.zero_apply] at h0
    rw [← h0]
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  let Qu : Matrix (Fin T.rank) (Fin T'.rank) ℂ :=
    Matrix.of fun j a => tauE D τ (T.frame.repr (ι (T'.frame a)) j)
  let Qc : Matrix (Fin T.rank) (Fin i) ℂ := Matrix.of fun j k => tauE D τ (T.frame.repr (c k) j)
  have hUU : Quᴴ * gramAt D T τ * Qu = gramAt D T' τ := by
    refine (gram_tauE_frame_repr_eq_hT T τ (fun a => ι (T'.frame a)) (fun a => ι (T'.frame a))).trans ?_
    ext a b
    simp [hι', gramAt, Formalism.BasicNotions.HSpace.gram]
  have hUC : Quᴴ * gramAt D T τ * Qc = 0 :=
    (gram_tauE_frame_repr_eq_hT T τ (fun a => ι (T'.frame a)) c).trans (by ext a k; simp [hcu])
  have hCC : Qcᴴ * gramAt D T τ * Qc = 0 := (gram_tauE_frame_repr_eq_hT T τ c c).trans (by ext k l; simp [hcc])
  have hGH : (gramAt D T τ)ᴴ = gramAt D T τ := by
    ext a b
    simp only [gramAt, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.BasicNotions.HSpace.gram]
    rw [Complex.star_def, ← GlobalTheory.FockCompare.tauE_star]
    congr 1
    exact T.herm.eq _ _
  have hdet : IsUnit (gramAt D T τ).det := by
    rw [isUnit_iff_ne_zero, show gramAt D T τ = (tauE D τ).mapMatrix T.gram from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (GlobalTheory.FrameComplement.gram_det_ne T)
  obtain ⟨ε0, P0, hP0, hP0G⟩ := GlobalTheory.FrameExists.exists_signFrame (H := gramAt D T τ) hGH hdet
  obtain ⟨P', Q', e0, he0⟩ := exists_numbering_signCompat ε0
  have hGs : Formalism.UG.HasSignature (gramAt D T τ) P' Q' := by
    rw [← hP0G]
    exact hasSignature_of_signCompat hP0 he0
  obtain ⟨hcard, Qf, hQf⟩ := Formalism.UG.P.sig_data _ _ _ hGs
  obtain ⟨hcard', R', hR'⟩ := Formalism.UG.P.sig_data _ _ _ hs
  have hQc : Qc = C.map (tauE D τ) := by
    ext j k
    simp [Qc, hrc]
  have hinj : ∀ x : Fin i → ℂ, Qc *ᵥ x = 0 → x = 0 := by
    have hCinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.mpr hCli
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
      (LinearMap.ker_eq_bot.mpr fun a b hab => hCinj (by simpa [Matrix.toLin'_apply] using hab))
    have hBC : LinearMap.toMatrix' g * C = 1 := by
      have h1 := congrArg LinearMap.toMatrix' hg
      rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1
    intro x hx
    have h2 : ((LinearMap.toMatrix' g).map (tauE D τ) * Qc) *ᵥ x = x := by
      rw [hQc, ← Matrix.map_mul, hBC, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero] at h2
    exact h2.symm
  have hR := submatrix_inl_gram_eq_one_and_inr_eq_neg_one _ R' hR'
  have hF := submatrix_inl_gram_eq_one_and_inr_eq_neg_one _ Qf hQf
  have hA1 : (Qu * R'.submatrix id Sum.inl)ᴴ * gramAt D T τ * (Qu * R'.submatrix id Sum.inl) = 1 := by
    rw [Matrix.conjTranspose_mul, show (R'.submatrix id Sum.inl)ᴴ * Quᴴ * gramAt D T τ *
      (Qu * R'.submatrix id Sum.inl) = (R'.submatrix id Sum.inl)ᴴ * (Quᴴ * gramAt D T τ * Qu) *
      R'.submatrix id Sum.inl by simp only [Matrix.mul_assoc], hUU]
    exact hR.1
  have hAC1 : (Qu * R'.submatrix id Sum.inl)ᴴ * gramAt D T τ * Qc = 0 := by
    rw [Matrix.conjTranspose_mul, show (R'.submatrix id Sum.inl)ᴴ * Quᴴ * gramAt D T τ * Qc =
      (R'.submatrix id Sum.inl)ᴴ * (Quᴴ * gramAt D T τ * Qc) by simp only [Matrix.mul_assoc], hUC,
      Matrix.mul_zero]
  have hA2 : (Qu * R'.submatrix id Sum.inr)ᴴ * (-gramAt D T τ) * (Qu * R'.submatrix id Sum.inr) = 1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.conjTranspose_mul, show (R'.submatrix id Sum.inr)ᴴ * Quᴴ *
      gramAt D T τ * (Qu * R'.submatrix id Sum.inr) = (R'.submatrix id Sum.inr)ᴴ *
      (Quᴴ * gramAt D T τ * Qu) * R'.submatrix id Sum.inr by simp only [Matrix.mul_assoc], hUU, hR.2, neg_neg]
  have hAC2 : (Qu * R'.submatrix id Sum.inr)ᴴ * (-gramAt D T τ) * Qc = 0 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.conjTranspose_mul, show (R'.submatrix id Sum.inr)ᴴ * Quᴴ *
      gramAt D T τ * Qc = (R'.submatrix id Sum.inr)ᴴ * (Quᴴ * gramAt D T τ * Qc) by
      simp only [Matrix.mul_assoc], hUC, Matrix.mul_zero, neg_zero]
  have hCC2 : Qcᴴ * (-gramAt D T τ) * Qc = 0 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hCC, neg_zero]
  have hN2 : (Qf.submatrix id Sum.inl)ᴴ * (-gramAt D T τ) * Qf.submatrix id Sum.inl = -1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hF.1]
  have c1 := card_add_card_add_card_le_of_gram_frames (gramAt D T τ) hGH (Qu * R'.submatrix id Sum.inl) Qc (Qf.submatrix id Sum.inr)
    hA1 hAC1 hCC hinj hF.2
  have c2 := card_add_card_add_card_le_of_gram_frames (-gramAt D T τ) (by rw [Matrix.conjTranspose_neg, hGH])
    (Qu * R'.submatrix id Sum.inr) Qc (Qf.submatrix id Sum.inl) hA2 hAC2 hCC2 hinj hN2
  simp only [Fintype.card_fin] at c1 c2 hcard hcard'
  have hP : P' = p + i := by omega
  have hQ : Q' = q + i := by omega
  rw [hP, hQ] at hGs
  exact hGs

theorem signCompat_of_isWittLower : ∀ (D : D7) (T T' : HSp D) (i : ℕ) (τ : D.what₂.Tau) (fr : Mn T.rank) (ε : Fin T.rank → Bool) (fr' : Mn T'.rank) (ε' : Fin T'.rank → Bool) (r s : ℕ) (e : Ix r s ≃ Fin T.rank), IsWittLower T T' i → frᴴ * Formalism.REAL.Jm ε * fr = gramAt D T τ → IsUnit fr → fr'ᴴ * Formalism.REAL.Jm ε' * fr' = gramAt D T' τ → IsUnit fr' → SignCompat ε e → i ≤ r ∧ i ≤ s ∧ ∃ e' : Ix (r - i) (s - i) ≃ Fin T'.rank, SignCompat ε' e' := by
  intro D T T' i τ fr ε fr' ε' r s e hW hfr hfru hfr' hfr'u hse
  have hG : Formalism.UG.HasSignature (gramAt D T τ) r s := by
    rw [← hfr]
    exact hasSignature_of_signCompat hfru hse
  obtain ⟨p', q', e', he'⟩ := exists_numbering_signCompat ε'
  have hG' : Formalism.UG.HasSignature (gramAt D T' τ) p' q' := by
    rw [← hfr']
    exact hasSignature_of_signCompat hfr'u he'
  have h4 := hasSignature_of_isWittLower hW τ hG'
  obtain ⟨hc1, Q1, hQ1⟩ := Formalism.UG.P.sig_data _ _ _ hG
  obtain ⟨hc2, Q2, hQ2⟩ := Formalism.UG.P.sig_data _ _ _ h4
  have d1 := Formalism.UG.P.sig_dim _ Q1 hQ1 Q2 hQ2
  have d2 := Formalism.UG.P.sig_dim _ Q2 hQ2 Q1 hQ1
  simp only [Fintype.card_fin] at hc1 hc2 d1 d2
  refine ⟨by omega, by omega, ?_⟩
  have hr : r - i = p' := by omega
  have hs' : s - i = q' := by omega
  rw [hr, hs']
  exact ⟨e', he'⟩

end GlobalTheory.WittSign
