import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_approx_cmType (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : Ψ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ∀ τ : Ψ, dist (w τ) (τ.1 x) < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose z hz using fun τ : Ψ => Metric.denseRange_iff.1
    (GlobalTheory.ShortVec.denseRange_emb τ.1 (IsTotallyComplex.complexEmbedding_not_isReal τ.1)) (w τ) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (v := fun τ : Ψ => (InfinitePlace.mk τ.1).1) (fun τ => InfinitePlace.isNontrivial _)
    (by
      intro σ τ hne h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.eq_iff_isEquiv.2 h) with h1 | h1
      · exact hne (Subtype.ext h1)
      · exact (hΨ σ.1).1 σ.2 (h1 ▸ τ.2)) z hε2
  refine ⟨x, fun τ => ?_⟩
  have h1 : ‖τ.1 (z τ - x)‖ < ε / 2 := by
    rw [← InfinitePlace.apply]; exact hx τ
  rw [map_sub, ← dist_eq_norm] at h1
  have h2 := dist_triangle (w τ) (τ.1 (z τ)) (τ.1 x)
  have h3 := hz τ
  linarith

theorem dom_nonempty {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  choose P hP using X.signature
  refine ⟨fun τ k a => P τ k a, fun τ => ⟨(hP τ).1, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ k a => P τ k a) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    change lminor (gram τ.1 X.Gm (P τ)) i = _
    rw [(hP τ).2, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  unfold sgn
  split_ifs <;> norm_num

theorem exists_frm_mem_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r),
    ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  intro E _ _ _ r X
  obtain ⟨P, hP⟩ := dom_nonempty X
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (FourierCoefficientDomain.isOpen_dom X) P hP
  choose u hu using fun a k : Fin r =>
    exists_approx_cmType X.Ψ X.cmType (fun τ => P τ k a) hε
  refine ⟨u, hb ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff hε]
  intro τ
  rw [dist_pi_lt_iff hε]
  intro k
  rw [dist_pi_lt_iff hε]
  intro a
  exact hu a k τ

end GlobalTheory.OrthoFrame
