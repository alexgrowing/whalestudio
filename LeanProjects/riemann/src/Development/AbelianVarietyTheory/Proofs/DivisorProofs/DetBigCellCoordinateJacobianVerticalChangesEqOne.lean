import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.VertDet

theorem det_eq_one_of_key {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (A : Matrix ι ι R) (k : ι → ℕ)
    (h : ∀ a b, a ≠ b → k a ≤ k b → A a b = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp [hd]
  · intro s _ hs
    obtain ⟨i, hi, hk⟩ : ∃ i, s i ≠ i ∧ k (s i) ≤ k i := by
      by_contra hc
      push_neg at hc
      obtain ⟨i₀, hi₀⟩ : ∃ i, s i ≠ i := by
        by_contra h0
        push_neg at h0
        exact hs (Equiv.ext h0)
      have hlt : ∑ i, k i < ∑ i, k (s i) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, hc i₀ hi₀⟩
        by_cases e : s i = i
        · rw [e]
        · exact (hc i e).le
      rw [Equiv.sum_comp s k] at hlt
      exact lt_irrefl _ hlt
    rw [Finset.prod_eq_zero (f := fun j => A (s j) j) (Finset.mem_univ i) (h _ _ hi hk), smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem snd_unip_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] (N : GlobalTheory.FlagTan.FIx Dw → K) (σ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (p q : Fin (Dw.mult σ)) :
    ((GlobalTheory.FlagTan.unip K N σ * M.map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) p q).snd
      = ∑ r, N (some ⟨σ, p, r⟩) * M r q := by
  rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [GlobalTheory.FlagTan.unip, TrivSqZeroExt.snd_mul, mul_comm]

theorem det_vert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (M : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ i j, j < i → M σ i j = 0) → (∀ σ i, M σ i i = 1) → (Matrix.of fun a b : VIx Dw => ((GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) a.1 * (M a.1).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) a.2.1.1 a.2.1.2).snd).det = 1 := by
  intro E _ _ _ H Dw K _ M hM hM1
  refine det_eq_one_of_key _ (fun a => (a.2.1.2 : ℕ)) ?_ ?_
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩ ⟨τ, ⟨i, j⟩, hij⟩ hne hk
    rw [Matrix.of_apply, snd_unip_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases e : (some ⟨σ, p, r⟩ : GlobalTheory.FlagTan.FIx Dw) = GlobalTheory.FlagTan.VIx.toF ⟨τ, ⟨(i, j), hij⟩⟩
    · obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e')
      have hlt : q < r := lt_of_le_of_ne hk (by rintro rfl; exact hne rfl)
      rw [hM _ _ _ hlt, mul_zero]
    · rw [Pi.single_eq_of_ne e, zero_mul]
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩
    rw [Matrix.of_apply, snd_unip_mul, Finset.sum_eq_single q]
    · rw [hM1, mul_one]
      exact Pi.single_eq_same _ _
    · intro r _ hr
      rw [Pi.single_eq_of_ne, zero_mul]
      intro e
      obtain ⟨-, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      exact hr (Prod.mk.inj (eq_of_heq e')).2
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end GlobalTheory.LogPole.VertDet
