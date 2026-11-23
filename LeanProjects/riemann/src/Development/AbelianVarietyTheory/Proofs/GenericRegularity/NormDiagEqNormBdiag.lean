import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NormWcharEqNormBchar

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.BorelDiag

open GlobalTheory.FrameNormLie GlobalTheory.WeightLie

set_option maxHeartbeats 1000000 in

theorem norm_diag_eq_norm_bdiag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom), ∀ γ ∈ (U.X k).Γ, ∀ b ∈ Bor (U.X k).Ψ r, ∀ (hx : rmul (lact γ x.1) b ∈ (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) (U.un k ⟨_, hx⟩) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ‖toC (t (some ⟨τ, i⟩) : CAt σ)‖ = ‖bdiag (U.X k) b (relab c σ τ) i‖ := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k' x γ hγ b hb hx' t hB τ₀ i₀
  obtain ⟨x', hxx, hB⟩ : ∃ x' : (U.X k').dom, x'.1 = rmul (lact γ x.1) b ∧ FrBor t (U.un k' x) (U.un k' x') :=
    ⟨⟨_, hx'⟩, rfl, hB⟩
  obtain ⟨hr, hty0, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨hp0, hty⟩ := hty0 k'
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k' x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  replace hbij : Function.Bijective (relab c σ) := hbij
  replace hrt : ∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := hrt
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k').Ψ (U.X k').cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (U.X k').Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ (U.X k').Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ (U.X k').Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  have hper : ∀ (x : Frame (U.X k').Ψ r) v j, perFr (U.X k') x v (relab c σ (e j).1)
      (e j).2 = perVec (U.X k') idx x v j := by
    intro x v j
    unfold perVec
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ (U.X k').Ψ from hτ), dif_pos hn]
      rfl
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ b ∈ Bor (U.X k').Ψ r, Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ))
      (PerBor.moveMat (U.X k').p0 idx b) := by
    intro b hb j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · rw [if_neg (by omega)] at h2
      exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by simp only; omega⟩
    · rw [if_neg (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      exact ⟨hbij.1 (by rw [← hcc (relab c σ (e j).1), ← b1, ← h1, b2, hcc]), by simp only; omega⟩
  obtain ⟨T, T', hT, hT', hT0, hTT, hTf, hTf'⟩ := exists_tri_pair (U.X k') idx hinj hs x.1 x.2 hγ hb
  rw [← hxx] at hTf'
  have hPv : ∀ a, P a = perVec (U.X k') idx x.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP a j).trans (hper _ _ _)
  have hPv' : ∀ a, P' a = perVec (U.X k') idx x'.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP' a j).trans (hper _ _ _)
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g _ F (ik k') (ik k') P' P p' p
    (by rw [← hPx, ← hPx', hB.1])
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k' x).u τ) _ (hv τ) (cf τ i)
      ((U.un k' x').u τ i)).1 (hPx ▸ hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F _ P' p' _ P h.toLinearMap p hex _ _).1 (hv' τ i)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hAe : ∀ j τ i, A j (e.symm ⟨τ, i⟩) =
      ∑ i', (show ℂ from cf τ i i') * (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) j := by
    intro j τ i
    have := congrFun (hcol τ i) j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply] at this
    exact this
  have hA : Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) A := by
    intro j j' hne
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j'
    rw [hAe] at hne
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hi'
    obtain rfl : j = e.symm ⟨τ, i'⟩ := by
      by_contra hj
      exact h2 (Pi.single_eq_of_ne hj _)
    beta_reduce
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨rfl, ?_⟩
    dsimp only
    by_contra hlt
    exact h1 (hcf2 τ i i' (by rw [Fin.lt_def]; omega))
  have key := UnitDet.eq_of_im_hermForm_eq _ p'.2.2.2.1
    ((T * A)ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * (T * A).map (starRingEnd ℂ)))
    (T'ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * T'.map (starRingEnd ℂ))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← UnitDet.hermForm_mulVec, ← UnitDet.hermForm_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hAv, hAv, ← hh, ← hh, hPv, hPv, hPv', hPv', hTf, hTf', ← hEF, ← hEF, hiso])
  have hdiag : ∀ j, ‖toC (t (some (e j)) : CAt σ)‖ = ‖(PerBor.moveMat (U.X k').p0 idx b j j)⁻¹‖ := by
    intro j
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
    have h1 := norm_diag_eq_norm_diag hinj (hT.mul hA) hT'
      (fun j => by rw [hTT]; exact mul_ne_zero (hT0 j) (inv_ne_zero (moveMat_diag_ne _ idx hb j))) _
      (diagXi_ne _ idx) key (e.symm ⟨τ, i⟩)
    rw [Supp.mul_diag hinj hT hA, hTT, norm_mul, norm_mul, mul_right_inj' (norm_ne_zero_iff.2 (hT0 _)), hAe,
      Finset.sum_eq_single i, Pi.single_eq_same, mul_one, hcf1] at h1
    · rw [Equiv.apply_symm_apply]
      exact h1
    · intro i' _ hi'
      refine mul_eq_zero_of_right _ (Pi.single_eq_of_ne (fun h0 => hi' ?_) _)
      have := e.symm.injective h0
      exact (eq_of_heq (Sigma.mk.inj this).2).symm
    · simp
  have h0 := hdiag (e.symm ⟨τ₀, i₀⟩)
  have h1 := hi (e.symm ⟨τ₀, i₀⟩)
  rw [PerBor.moveMat_diag _ idx hb] at h0
  generalize idx (e.symm ⟨τ₀, i₀⟩) = s at h0 h1
  rw [Equiv.apply_symm_apply] at h0 h1
  obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := s
  dsimp only at h0 h1
  rw [h0]
  unfold bdiag
  rcases h1 with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
  · rw [if_neg (by omega), inv_inv, dif_pos a, dif_pos hn]
  · rw [if_pos (by omega), dif_neg a,
      dif_pos (show conjEmb (relab c σ τ₀) ∈ (U.X k').Ψ from hτ), dif_pos hn]
    rfl

end GlobalTheory.BorelDiag
