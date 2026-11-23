import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false

namespace GlobalTheory.HSShort.FormRatio

open MvPolynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Adelic GlobalTheory.Points GlobalTheory.Twist

theorem exists_forms_of_mem_closure {F K : Type} [Field F] [Field K] {N : ℕ} (φ : F →+* K) (c : Fin N → K) {r : K}
    (hr : r ∈ Subfield.closure (Set.range φ ∪ {r | ∃ i j, r = c i / c j})) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      r * eval₂ φ c Q = eval₂ φ c P := by
  have h0 : ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      0 * eval₂ φ c Q = eval₂ φ c P :=
    ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  induction hr using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨i, j, rfl⟩
    · exact ⟨0, C a, 1, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · by_cases hj : c j = 0
      · rwa [hj, div_zero]
      · exact ⟨1, X i, X j, isHomogeneous_X _ _, isHomogeneous_X _ _, by simpa using hj, by simp [hj]⟩
  | one => exact ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * Q' + Q * P', Q * Q', (hP.mul hQ').add (hQ.mul hP'), hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h2, ← h2']; ring
  | neg x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    exact ⟨d, -P, Q, hP.neg, hQ, h1, by rw [eval₂_neg, ← h2, neg_mul]⟩
  | inv x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    by_cases hx0 : x = 0
    · rwa [hx0, inv_zero]
    · refine ⟨d, Q, P, hQ, hP, h2 ▸ mul_ne_zero hx0 h1, ?_⟩
      rw [← h2, inv_mul_cancel_left₀ hx0]
  | mul x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * P', Q * Q', hP.mul hP', hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_mul, eval₂_mul, ← h2, ← h2']; ring

theorem eq_zero_of_valR_generic {Y : Scheme.{0}} [IsReduced Y] {η : Y} (hη : IsGenericPoint η Set.univ)
    {U : Y.Opens} (f : Γ(Y, U)) (h : valR (resPt η) U f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro y hy
  have h1 : ptOf (resPt η) ∈ Y.basicOpen f := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (Y.basicOpen f).isOpen).2 ⟨y, trivial, hy⟩
  exact ((valR_ne_zero_iff _ (Y.basicOpen_le f h1) f).2 h1 h).elim

theorem exists_forms (F : Type) [Field F] (S : LinSys F) (hS : S.IsVariety) (_ : S.BasePointFree)
    (hb : S.Birational) (W : S.Y.Opens) (a : Γ(S.Y, W)) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧
      (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W →
        valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  have := hS.isIntegral
  obtain ⟨η, hη, hr⟩ := hb
  obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := exists_forms_of_mem_closure (S.baseHom (resPt η)) (S.coords (resPt η))
    (r := valR (resPt η) W a) (hr.ge (Subfield.mem_top _))
  refine ⟨d, P, Q, hP, hQ, fun h => h1 (S.eval₂_coords_eq_zero _ h), fun ha h => ?_, fun K _ _ x hx => ?_⟩
  · rw [S.eval₂_coords_eq_zero _ h] at h2
    exact ha (eq_zero_of_valR_generic hη a ((mul_eq_zero.1 h2).resolve_right h1))
  · set j := S.chartAt (ptOf x.1)
    have hxV : ptOf x.1 ∈ W ⊓ S.L.U j := ⟨hx, S.mem_chartAt _⟩
    have hηV : ptOf (resPt η) ∈ W ⊓ S.L.U j := by
      rw [ptOf_resPt]
      exact (hη.mem_open_set_iff (W ⊓ S.L.U j).isOpen).2 ⟨_, trivial, hxV⟩
    let f : Γ(S.Y, W ⊓ S.L.U j) :=
      (S.Y.presheaf.map (homOfLE inf_le_left).op).hom a *
        (S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hQ) j) +
        -(S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hP) j)
    have hf : ∀ {Ω : Type} [Field Ω] (z : Sp Ω ⟶ S.Y), ptOf z ∈ W ⊓ S.L.U j → valR z _ f =
        valR z W a * valR z _ (zfun (S.form hQ) j) - valR z _ (zfun (S.form hP) j) := fun z hz => by
      have h := (le_iff_ptOf_mem z _).2 hz
      rw [valR_add z _ h, valR_neg z _ h, valR_mul z _ h, valR_res z _ h, valR_res z _ h, valR_res z _ h,
        sub_eq_add_neg]
    have hf0 : f = 0 := by
      obtain ⟨c, -, -, hc⟩ := S.exists_frame_change (resPt η) j hηV.2
      refine eq_zero_of_valR_generic hη f ?_
      rw [hf _ hηV, hc, hc, S.powVal_form, S.powVal_form, ← h2]
      ring
    have h3 := hf x.1 hxV
    rw [hf0, valR_zero _ _ ((le_iff_ptOf_mem _ _).2 hxV), eq_comm, sub_eq_zero] at h3
    have e : ∀ {g : MvPolynomial (Fin S.N) F} (hg : g.IsHomogeneous d),
        valR x.1 _ (zfun (S.form hg) j) = aeval (S.coords x.1) g := fun hg =>
      (S.powVal_form x.1 hg).trans (by rw [LinSys.baseHom_ptOver, aeval_def])
    rwa [e, e] at h3

end GlobalTheory.HSShort.FormRatio
