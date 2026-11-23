import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairAtTAdjCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero

open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem cslice_continuous (c : Fin r → ℂ) : Continuous (fun x : Mt k r => (c, Matrix.of x)) :=
  continuous_const.prodMk continuous_id

theorem int_cpt_gen (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Θ : RadSp k r z z' π π') (c : Fin r → ℂ) (v : Wq) (K : Set (Mx k r)) (hKc : IsCompact K)
    (hKG : K ⊆ {g | 0 < GGl k r z z' g}) (hc : c ∈ OmX r)
    (f : Mt k r → ℂ) (hf : (f = fun x => ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ) ∨
      (f = fun x => ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ))
    (hΦ0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    Integrable f μ := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) s := by
    intro Ξ
    have h1 := (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s) (fun x hx => by rw [hs] at hx; exact hx)
    exact h1.clm_apply continuousOn_const
  have hcont : ContinuousOn f s := by
    rcases hf with rfl | rfl
    · exact (hA Φ).inner (hA Θ)
    · exact (hA Θ).inner (hA Φ)
  have hzero : ∀ x, (c, Matrix.of x) ∉ DomR k r z z' ∨ Matrix.of x ∉ K → f x = 0 := by
    intro x hx
    have hΦx : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 := by
      rcases hx with hx | hx
      · exact radSp_zero_off Φ (x := (c, Matrix.of x)) hx
      · by_cases hg : Matrix.of x ∈ Glev k r (Fin.last r)
        · exact hΦ0 _ hg hx
        · exact radSp_zero_off Φ (x := (c, Matrix.of x)) (fun h => hg h.2.1)
    rcases hf with h | h
    · subst h
      show ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_left]
    · subst h
      show ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_right]
  obtain ⟨C, hC⟩ : ∃ C : Set (Mt k r), C = (fun g : Mx k r => (Matrix.of.symm g : Mt k r)) '' (K ∩ Glev k r (Fin.last r)) :=
    ⟨_, rfl⟩
  have hCmem : ∀ x, x ∈ C ↔ Matrix.of x ∈ K ∧ Matrix.of x ∈ Glev k r (Fin.last r) := by
    intro x
    rw [hC]
    constructor
    · rintro ⟨g, hg, rfl⟩; simpa using hg
    · intro hx; exact ⟨Matrix.of x, hx, rfl⟩
  have hCc : IsCompact C := by
    rw [hC]
    exact (hKc.inter_right (P.Qx5.Glev_closed _)).image continuous_id
  have hCs : C ⊆ s := by
    intro x hx
    rw [hCmem] at hx
    rw [hs]
    exact ⟨hc, hx.2, hKG hx.1⟩
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hcont.mono hCs)
  have hmeas : Measurable f := measurable_of_continuousOn_zero hsm hcont (fun x hx => hzero x (Or.inl (by rw [hs] at hx; exact hx)))
  have hbound : ∀ x, ‖f x‖ ≤ C.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]; exact hM x hx
    · rw [Set.indicator_of_notMem hx]
      have : f x = 0 := by
        apply hzero
        by_cases hd : (c, Matrix.of x) ∈ DomR k r z z'
        · right; intro hK; exact hx ((hCmem x).2 ⟨hK, hd.2.1⟩)
        · left; exact hd
      rw [this, norm_zero]
  refine Integrable.mono' ?_ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (integrable_indicator_iff hCc.measurableSet).mpr
    (integrableOn_const (hμ.finite_compact C hCc).ne)

end Cpt

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt' (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  obtain ⟨K, hKc, hKG, hK0⟩ := hK
  refine pairAt_t_adj_cpt P z z' π π' hP X μ hμ Φ Ψ c hc ⟨K, hKc, hKG, hK0⟩ Y a b (fun m => ?_) (fun m => ?_)
  · exact int_cpt_gen μ hμ Ψ (X.t Y a b Φ) c _ K hKc hKG hc _ (Or.inl rfl) (fun g hg hgK => (hK0 g hg hgK).2)
  · exact int_cpt_gen μ hμ Φ (X.t (star Y) b a Ψ) c _ K hKc hKG hc _ (Or.inr rfl) (fun g hg hgK => (hK0 g hg hgK).1)

end Adj

end Formalism.FourierDecayAlt.P5.HerA
