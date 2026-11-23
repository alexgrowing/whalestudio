import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomainStatement

open NumberField

namespace GlobalTheory.OrthoFrame

theorem exists_orthoFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  intro E _ _ _ r X
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_rational_frame_mem_flagDomain E r X
  obtain ⟨v, ho, hv⟩ := GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain E r X u hu
  have hs := GlobalTheory.OrthoFrame.sign_of_mem X v ho hv
  choose d hd0 hdΛ using fun j => ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.exists_smul_mem X.Λ (x := v j)
    (by rw [X.Λ_span]; exact Submodule.mem_top)
  have hd0' : ∀ j, ((d j : 𝓞 E) : E) ≠ 0 := fun j h => hd0 j (by exact_mod_cast h)
  set lam : Fin r → Fin r → E := fun j => ((d j : 𝓞 E) : E) • v j with hlam
  have hlamΛ : ∀ j, lam j ∈ X.Λ := fun j => by
    have e : (d j) • v j = ((d j : 𝓞 E) : E) • v j := by
      ext a; simp [Algebra.smul_def]
    rw [hlam]; dsimp only; rw [← e]; exact hdΛ j
  have hlo : ∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0 := by
    intro j k h
    simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, ho j k h,
      mul_zero]
  have hsl : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
      (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re := by
    intro τ j
    have hn : 0 < Complex.normSq (τ.1 (d j : E)) := Complex.normSq_pos.2 ((map_ne_zero τ.1).2 (hd0' j))
    have e : τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j)) =
        (Complex.normSq (τ.1 (d j : E)) : ℂ) * τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j)) := by
      simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, map_mul,
        GlobalTheory.OrthoFrame.emb_cc, ← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have := hs τ j
    calc (0 : ℝ) < Complex.normSq (τ.1 (d j : E)) * (ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
        (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j))).re) := mul_pos hn this
      _ = _ := by ring
  have hΨ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, ?_⟩
      by_contra h'
      exact h ((X.cmType τ0).2 h')
  obtain ⟨τ0, hτ0⟩ := hΨ
  have hdv : (Matrix.of v).det ≠ 0 := by
    have h := (hv ⟨τ0, hτ0⟩).1
    have e : ReciprocityTheory.ChartRestriction.G.FD.mat (GlobalTheory.OrthoFrame.frm X.Ψ v) ⟨τ0, hτ0⟩ = τ0.mapMatrix (Matrix.of v).transpose := by
      ext k a; rfl
    rw [e, ← RingHom.map_det, Matrix.det_transpose] at h
    intro h0; exact h (by rw [h0, map_zero])
  have hdl : (Matrix.of lam).det ≠ 0 := by
    have e : Matrix.of lam = Matrix.diagonal (fun j => ((d j : 𝓞 E) : E)) * Matrix.of v := by
      ext j k; simp only [hlam, Matrix.of_apply, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd0' j) hdv
  refine ⟨GlobalTheory.OrthoFrame.frm X.Ψ lam, GlobalTheory.OrthoFrame.mem_of_sign X lam hlo hdl hsl, lam, hlamΛ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_of_det_ne_zero hdl
  · intro j k hj hk
    exact hlo j k (by intro h; subst h; omega)
  · intro j hj τ
    have := hsl τ j
    simpa [ReciprocityTheory.ChartRestriction.G.FD.sgn, hj] using this
  · intro j hj τ
    have := hsl τ j
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg (not_lt.2 hj)] at this
    linarith
  · intro τ
    rfl

end GlobalTheory.OrthoFrame
