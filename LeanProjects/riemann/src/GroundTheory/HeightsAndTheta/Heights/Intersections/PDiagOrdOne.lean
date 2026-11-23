import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagFormDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrderOne

section Length

variable {A : Type*} [CommRing A]

theorem length_eq_one_of_sat (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by
  have hz : ∀ (r : A) (s : W.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk J r) s = 0 ↔ r ∈ W := by
    intro r s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨u, hu⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
      rcases ‹W.IsPrime›.mem_or_mem (hJ hu) with h | h
      · exact absurd h u.2
      rcases ‹W.IsPrime›.mem_or_mem h with h | h
      · exact absurd h s.2
      · exact h
    · intro hr
      obtain ⟨u, hu, hud⟩ := hs r hr
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : u * ((s : A) * r) = u * r * s := by ring
      rw [show ((⟨u, hu⟩ : W.primeCompl) : A) = u from rfl, e]
      exact J.mul_mem_right _ hud
  have hgen : ∀ (q : A) (t : W.primeCompl) (r : A) (s : W.primeCompl) (hr : r ∉ W),
      LocalizedModule.mk (Ideal.Quotient.mk J q) t =
        Localization.mk (q * s) (t * ⟨r, hr⟩) • LocalizedModule.mk (Ideal.Quotient.mk J r) s := by
    intro q t r s hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul]
    congr 1
    ring
  have h1 : LocalizedModule.mk (Ideal.Quotient.mk J 1) (1 : W.primeCompl) ≠ 0 :=
    fun h => ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).2 ((hz 1 1).1 h))
  have : Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨⟨_, 0, h1⟩⟩
  rw [Module.length_eq_one_iff, isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).1 hN
  induction n using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hr : r ∉ W := fun h => hn0 ((hz r s).2 h)
    rw [eq_top_iff]
    intro y _
    induction y using LocalizedModule.induction_on with
    | h m' t =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [hgen q t r s hr]
      exact N.smul_mem _ hnN

end Length

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem isWeightedHomogeneous_multiConeMap (c : (Σ k, ι k) → Φ) {p : MRing ι} {m : K → ℕ}
    (hp : IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) p m) :
    IsWeightedHomogeneous (fun k : K => (Pi.single k 1 : K → ℕ)) (T.multiConeMap c p) m := by
  rw [DiagRAux.multiConeMap_of_homog c p m ((isMultiHomog_iff_weighted p m).2 hp)]
  have := (isWeightedHomogeneous_C (fun k : K => (Pi.single k 1 : K → ℕ)) (aeval c p)).mul
    (IsWeightedHomogeneous.prod Finset.univ (fun k => (X k : MvPolynomial K Φ) ^ m k)
      (fun k => m k • (Pi.single k 1 : K → ℕ)) (fun k _ => (isWeightedHomogeneous_X Φ _ k).pow (m k)))
  convert this using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem component_mem_ker (c : (Σ k, ι k) → Φ) {f : MRing ι} (hf : f ∈ RingHom.ker (T.multiConeMap c))
    (m : K → ℕ) :
    weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f ∈
      RingHom.ker (T.multiConeMap c) := by
  rw [RingHom.mem_ker] at hf ⊢
  have hsum := congrArg (weightedHomogeneousComponent (fun k : K => (Pi.single k 1 : K → ℕ)) m) hf
  rw [← sum_weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum, map_zero] at hsum
  rw [← (isWeightedHomogeneous_multiConeMap c
    (weightedHomogeneousComponent_isWeightedHomogeneous m f)).weightedHomogeneousComponent_same, ← hsum]
  by_cases hm : weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f = 0
  · rw [hm, map_zero, map_zero]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = m
    · rw [hb, hm, map_zero, map_zero]
    · exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
  · rw [Finset.sum_eq_single m]
    · intro b _ hb
      exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset _).2 hm) h

end Graded

end DiagonalOrderOne

open DiagonalOrderOne in

theorem DiagOrdOne.proof (hF : DiagFormDiv.Statement) : DiagOrdOne.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  set P := T.wwIdeal x δ e φ (a 0) (a 1) with hPdef
  set Δ := T.wwIdeal x δ e φ (a 0) (a 0) with hΔdef
  have hΔp : Δ.IsPrime := RingHom.ker_isPrime _
  have hPΔ : P ≤ Δ := DiagonalOrder.wwIdeal_le_diag x δ e φ a ha
  have hhΔ : h ∉ Δ := by
    refine (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).2 ?_
    rw [DiagonalOrder.aeval_diag_eq x δ e φ (a 0) (a 1) hh]
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
  have hJ : P ⊔ Ideal.span {g} ≤ Δ := sup_le hPΔ
    ((Ideal.span_singleton_le_iff_mem _).2 (DiagFormDiv.mem_diag_of_quot x δ e φ a ha hg hh hq))
  have hhom : ∀ (α : T.WBlk → ℕ) (d : MRing (T.wwIdx ι ν κ)), IsMultiHomog d α → d ∈ Δ →
      ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g} := by
    intro α d hd hdΔ
    obtain ⟨γ, β, s, r, hs, hr, hdeg, hsΔ, hv⟩ := hF Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha α d hd hdΔ
    refine ⟨s * h, fun hm => (hΔp.mem_or_mem hm).elim hsΔ hhΔ, ?_⟩
    have hdeg' : β + T.wwDeg n 1 = γ + T.wwDeg (n + 3) 0 + α := by
      funext k
      have := hdeg k
      cases k <;> simp only [T.wwDeg, Pi.add_apply] at this ⊢ <;> omega
    have hm : IsMultiHomog (s * h * d - r * g) (γ + T.wwDeg (n + 3) 0 + α) :=
      exHomog_sub (exHomog_mul (exHomog_mul hs hh) hd) (hdeg' ▸ exHomog_mul hr hg)
    have hmP : s * h * d - r * g ∈ P := by
      by_contra hn
      apply (DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hm).1 hn
      rw [map_sub, map_mul, map_mul, map_mul, hq]
      linear_combination (aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) * hv
    have e' : s * h * d = (s * h * d - r * g) + r * g := by ring
    rw [e']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hmP)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  have hsat : ∀ d ∈ Δ, ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g} := by
    intro d hd
    rw [← sum_weightedHomogeneousComponent (fun q : Σ k, T.wwIdx ι ν κ k => (Pi.single q.1 1 : T.WBlk → ℕ)) d,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp d)]
    refine Finset.sum_induction _ (fun y => ∃ u ∉ Δ, u * y ∈ P ⊔ Ideal.span {g}) ?_ ⟨1, ?_, by simp⟩ ?_
    · rintro y z ⟨u, hu, huy⟩ ⟨v, hv, hvz⟩
      refine ⟨u * v, fun hm => (hΔp.mem_or_mem hm).elim hu hv, ?_⟩
      have e' : u * v * (y + z) = v * (u * y) + u * (v * z) := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ huy) (Ideal.mul_mem_left _ _ hvz)
    · exact fun h1 => hΔp.ne_top ((Ideal.eq_top_iff_one Δ).2 h1)
    · intro m _
      exact hhom m _ ((isMultiHomog_iff_weighted _ m).2 (weightedHomogeneousComponent_isWeightedHomogeneous m d))
        (component_mem_ker _ hd m)
  unfold multAt
  rw [dif_pos hΔp, length_eq_one_of_sat _ Δ hJ hsat]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
