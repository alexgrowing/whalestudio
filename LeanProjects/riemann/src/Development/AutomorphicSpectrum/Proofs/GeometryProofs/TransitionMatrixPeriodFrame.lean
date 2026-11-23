import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tau_conj (τ : E →+* ℂ) (a : E) : τ (IsCMField.complexConj E a) = ComplexEmbedding.conjugate τ a := by
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  rfl

theorem transition_unique (D : Datum H) {I : Type} [Fintype I] [DecidableEq I] (x e : I → D.La) (T T' : Matrix I I E)
    (hg : (gramE D e).det ≠ 0) (h : IsTransition D x e T) (h' : IsTransition D x e T') : T = T' := by
  have hmul : T * gramE D e = T' * gramE D e := by
    ext m j
    simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
    rw [← h m (e j), ← h' m (e j)]
  have hu : IsUnit (gramE D e).det := isUnit_iff_ne_zero.mpr hg
  calc T = T * gramE D e * (gramE D e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = T' * gramE D e * (gramE D e)⁻¹ := by rw [hmul]
    _ = T' := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.Ar.Fl.ChgGen

namespace GlobalTheory.CompanionTheory.Ar.Fl

open ChgGen in

theorem constMul_change_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (ρ : ℂ), LinearIndependent (𝓞 E) e → IsTransition (FU.Di i) x e T → T.det ≠ 0 → IsConstMul U τ φ FU i e ρ → IsConstMul U τ φ FU i x (ρ / τ T.det) := by
  intro E _ _ _ H D l Xo c g ty FU i U τ φ e x T ρ he hT hdet hC
  unfold IsConstMul at hC ⊢
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]
  obtain ⟨T₀, hT₀, hgram, -, n, S, hn, hS, hST⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hg : (gramE (FU.Di i) e).det ≠ 0 := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hTT : T₀ = T := transition_unique (FU.Di i) x e T₀ T hg hT₀ hT
  rw [hTT] at hgram hST
  have hconj : (⇑τ ∘ ⇑(IsCMField.complexConj E)) = ⇑(ComplexEmbedding.conjugate τ) :=
    funext fun a => tau_conj τ a
  have hlin : ∀ (σ : E →+* ℂ) (a : Fin D.p ⊕ Fin D.q → ℂ) (z : Fin D.p ⊕ Fin D.q → Fin g → ℂ),
      tyPart ty σ (∑ j, a j • z j) = ∑ j, a j • tyPart ty σ (z j) := by
    intro σ a z
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hinj : ∀ (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ), M.det ≠ 0 →
      ∀ u : Fin D.p ⊕ Fin D.q → Fin g → ℂ, (∀ m, ∑ l, M m l • u l = 0) → u = 0 := by
    intro M hM u hu
    funext l k
    have hv : M *ᵥ (fun l => u l k) = 0 := by
      funext m
      have := congrFun (hu m) k
      simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using this
    have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h2 := congrArg (fun v => M⁻¹ *ᵥ v) hv
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h2
    exact congrFun h2 l
  have hcomb : ∀ (Bm : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ)
      (M : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ) (W : Fin D.q → Fin g → ℂ) (m : Fin D.p ⊕ Fin D.q),
      ∑ j, (Bm * Mᵀ) j m • W j = ∑ l, M m l • ∑ j, Bm j l • W j := by
    intro Bm M W m
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, _root_.smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  intro P y v w V W C Fm B hPer hu hfr hV hW hCa hB hF
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : ∀ m k, P (x m) k = ∑ b, ty k (T m b) * P (e b) k := by
    intro m k
    have h1 : (n : ℂ) * P (x m) k = ∑ b, ty k (T m b) * P (e b) k * n := by
      have := congrArg (fun z => z k) (congrArg P (hS m))
      simp only [_root_.map_nsmul, _root_.map_sum, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [this]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hPer.1 (S m b) (e b) k, hST m b, _root_.map_mul, _root_.map_natCast]
      ring
    rw [← Finset.sum_mul, _root_.mul_comm (n : ℂ)] at h1
    exact mul_right_cancel₀ hn' h1
  have hPσ : ∀ (σ : E →+* ℂ) m, tyPart ty σ (P (x m)) = ∑ b, σ (T m b) • tyPart ty σ (P (e b)) := by
    intro σ m
    funext k
    simp only [tyPart, Finset.sum_apply, Pi.smul_apply, _root_.smul_eq_mul]
    by_cases hk : ty k = σ
    · simp only [if_pos hk]
      rw [hP m k, hk]
    · simp only [if_neg hk, MulZeroClass.mul_zero, Finset.sum_const_zero]
  have hBmat : B = Fm * T.map τ * (gramE (FU.Di i) e).map τ * (T.map (ComplexEmbedding.conjugate τ))ᵀ := by
    have h1 : B = Fm * (gramE (FU.Di i) x).map τ := by
      ext j m
      rw [← hF j m, Matrix.mul_apply]
      simp only [Matrix.map_apply, gramE, Matrix.of_apply]
    rw [h1, hgram, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hconj]
    simp only [Matrix.mul_assoc]
  have hTc : (T.map (ComplexEmbedding.conjugate τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (_root_.map_ne_zero _).mpr hdet
  have ha' : ∀ a, tyPart ty τ (∑ m, (C * T.map τ) a m • P (e m)) = V a := by
    intro a
    rw [← hCa a, hlin, hlin]
    simp only [hPσ τ, Matrix.mul_apply, Matrix.map_apply, Finset.smul_sum, Finset.sum_smul, _root_.smul_smul]
    exact Finset.sum_comm
  have hb' : ∀ m, tyPart ty (ComplexEmbedding.conjugate τ) (P (e m)) =
      ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m • W j := by
    have key := hinj (T.map (ComplexEmbedding.conjugate τ)) hTc
      (fun l => tyPart ty (ComplexEmbedding.conjugate τ) (P (e l)) -
        ∑ j, (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j l • W j) (by
        intro m
        simp only [smul_sub, Finset.sum_sub_distrib, Matrix.map_apply]
        rw [← hPσ (ComplexEmbedding.conjugate τ) m, hB m, hBmat, sub_eq_zero]
        exact hcomb _ _ W m)
    intro m
    exact sub_eq_zero.mp (congrFun key m)
  have hc' : ∀ j m, ∑ r, (Fm * T.map τ) j r * τ (sesq (FU.Di i) (e r) (e m)) =
      (Fm * T.map τ * (gramE (FU.Di i) e).map τ) j m := by
    intro j m
    rw [Matrix.mul_apply (M := Fm * T.map τ)]
    simp only [Matrix.map_apply, gramE, Matrix.of_apply]
  have key := hC P y v w V W (C * T.map τ) (Fm * T.map τ) (Fm * T.map τ * (gramE (FU.Di i) e).map τ)
    hPer hu hfr hV hW ha' hb' hc'
  rw [← Matrix.fromRows_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at key
  have hτ : τ T.det ≠ 0 := (_root_.map_ne_zero τ).mpr hdet
  rw [eq_div_iff hτ, ← key]
  ring

end GlobalTheory.CompanionTheory.Ar.Fl
