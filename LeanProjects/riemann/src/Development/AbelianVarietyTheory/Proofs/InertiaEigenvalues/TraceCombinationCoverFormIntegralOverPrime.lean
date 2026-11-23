import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombinationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLiftStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

noncomputable section

namespace GlobalTheory.TraceIdem

theorem nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [nval]
  rw [nval_of_ne hz, EReal.coe_nonneg]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_nonneg_iff]
  have h1 : valV T.V z ≠ 0 := valV_ne_zero hz
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h' : 0 ≤ vV T.V z := by exact_mod_cast h
      unfold vV at h'
      rw [← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]; omega
    · linarith
  · intro h
    left
    refine ⟨?_, he'.le⟩
    have := (WithZero.log_le_log h1 one_ne_zero).2 h
    rw [WithZero.log_one] at this
    have h' : 0 ≤ vV T.V z := by unfold vV; omega
    exact_mod_cast h'

theorem trace_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  intro D T hL j hj σ hσ a n hD hspan hmu C hU hP la p hla m β hβ hβi y hφ
  obtain ⟨g, hgs, hgp, hgi⟩ := (GlobalTheory.T.exists_integral_cover_form_pullback_combination D T hL j hj σ hσ a n hD C hU hP la m β (fun k => (hβ k).1) y hφ)
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  obtain ⟨N, hN⟩ := GlobalTheory.T.trace_integral_of_small_at_other_places T.Q.c.F C.d.c₂.F p la hla m y
  refine ⟨N, fun b hb v hv => ?_⟩
  have hx : ∀ k, 0 ≤ v (β k) := fun k => hβi k v hv
  obtain ⟨⟨q, T0, io, e, ho, pt, hpt, eta, heta, rfl⟩, rfl⟩ := hv
  have hx' : ∀ k, valV T0.V (evI pt (β k)) ≤ 1 := fun k => (nval_nonneg_iff ho.1 _).1 (hx k)
  have hs : ∀ (s : Finset (Fin m)) (t : Fin m → T.Q.c.F),
      evI pt (∑ k ∈ s, t k • β k) = ∑ k ∈ s, io (t k) * evI pt (β k) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simpa using (isEval_evI pt).zero ()
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evI_add, evI_smul, ih]
  show 0 ≤ nval T0.V e (evI pt _)
  rw [nval_nonneg_iff ho.1, hs]
  exact hN b hb T0 hpt io e ho (fun k => evI pt (β k)) hx'
    (fun T' i e' τ e'' he' hi hT' hτ ho' =>
      GlobalTheory.T.baseSections_values_integral_at_coverLift D T hL j hj σ C hU la a n m β g (fun k => (hβ k).1) hgs hgp y hgi T0 io pt hpt T' i e' τ e'' he' hi hT' hτ ho')

end GlobalTheory.TraceIdem
