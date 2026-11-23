import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZeroStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.LExtInj

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_irreducible_GL_zero : ∃ t : IrrGL k, t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

theorem sum_fst_of_lFactors' {𝔪 : Multiset (Segment k)} {c : ℕ} {x : Fin c → IrrGL k} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL' {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {𝔪 : Multiset (Segment k)}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors' hx).symm.trans hd

theorem eq_of_isL (hM : LanglandsMultisegments) [CharZero k] (𝔪 : Multiset (Segment k)) (x y : IrrGL k)
    (hx : IsL 𝔪 x.rep) (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨t, ht0, ht⟩ := exists_irreducible_GL_zero (k := k)
  have hdeg : x.1 = y.1 := (deg_of_isL' hx).symm.trans (deg_of_isL' hy)
  obtain ⟨nx, cx⟩ := x
  obtain ⟨ny, cy⟩ := y
  obtain rfl : nx = ny := hdeg
  have hd : ∑ a, (![(⟨nx, cx⟩ : IrrGL k), t] a).1 = nx := by simp [Fin.sum_univ_two, ht0]
  have hs := (hM k).2 𝔪 0 ![⟨nx, cx⟩, t] ⟨nx, cy⟩ hd hx ht (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero k (⟨nx, cx⟩ : IrrGL k) t ht0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨nx, cy⟩ : IrrGL k)) (IrrGL.rep (⟨nx, cx⟩ : IrrGL k)) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  obtain ⟨ψ⟩ := hs2.nonempty_equiv cy.rep.irr cx.rep.irr
  congr 1
  rw [← cx.cl_rep, ← cy.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨ψ⟩

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isIrrWD_lpTw {y : WD h} (hy : IsIrrWD y) (s : ℝ) : IsIrrWD (y.lpTw s) := by
  obtain ⟨n, a, rfl, ha⟩ := hy
  exact ⟨n, a.tw s, (WD.lpTw_mk a s).symm, isIrreducible_twist ha _⟩

theorem lpTw_injective {y y' : WD h} {s : ℝ} (e : y.lpTw s = y'.lpTw s) : y = y' := by
  have := congrArg (fun z : WD h => z.lpTw (-s)) e
  simpa only [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero] using this

end GlobalTheory.LocLanglands.LExtInj

end
