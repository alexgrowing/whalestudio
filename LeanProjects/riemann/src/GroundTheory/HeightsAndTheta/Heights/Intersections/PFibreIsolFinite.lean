import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIsolFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FibreIsolFinite

theorem isolated_finite (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ)) :
    {x : Fin N → ℂ | (∀ s ∈ S, eval x s = 0) ∧
      ∀ᶠ y in 𝓝 x, (∀ s ∈ S, eval y s = 0) → y = x}.Finite := by
  classical
  let m : (Fin N → ℂ) → Ideal (MvPolynomial (Fin N) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have h1 : X i - C (x i) ∈ m y := by
      rw [← hxy]
      exact RingHom.mem_ker.mpr (by simp)
    have h2 : y i - x i = 0 := by simpa using RingHom.mem_ker.mp h1
    exact (sub_eq_zero.mp h2).symm
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span S)).preimage
    (fun a _ b _ h => hinj h)).subset ?_
  rintro x ⟨hx, hiso⟩
  have hIm : Ideal.span S ≤ m x := by
    rw [Ideal.span_le]
    exact fun s hs => RingHom.mem_ker.mpr (hx s hs)
  have : (m x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hmq : m x ≤ q := by
    intro f hf
    refine IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof N q f x hq.1.1
      (fun g hg => RingHom.mem_ker.mp (hqm hg)) ?_
    filter_upwards [hiso] with y hy hyq
    rw [hy fun s hs => hyq s (hq.1.2 (Ideal.subset_span hs))]
    exact RingHom.mem_ker.mp hf
  show m x ∈ (Ideal.span S).minimalPrimes
  rwa [le_antisymm hqm hmq] at hq

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem sameOrbit_comp_smul {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hvb : ∀ p, (v p).1 = κ p.1) {z' : (Σ k', ι' k') → ℂ} {u : (Σ k, ι k) → ℂ}
    (h : SameOrbit (fun p => z' (v p)) u) (c : K' → ℂ) (hc : ∀ k', c k' ≠ 0) :
    SameOrbit (fun p => c (v p).1 * z' (v p)) u := by
  obtain ⟨c₀, hc₀, hz⟩ := h
  refine ⟨fun k => c (κ k) * c₀ k, fun k => mul_ne_zero (hc _) (hc₀ k), funext fun p => ?_⟩
  have h1 : z' (v p) = c₀ p.1 * u p := congrFun hz p
  show c (v p).1 * z' (v p) = c (κ p.1) * c₀ p.1 * u p
  rw [hvb p, h1, mul_assoc]

theorem minor_of_sameOrbit {w u : (Σ k, ι k) → ℂ} (h : SameOrbit w u) (j : ∀ k, ι k)
    (p : Σ k, ι k) : w p * u ⟨p.1, j p.1⟩ = w ⟨p.1, j p.1⟩ * u p := by
  obtain ⟨c, -, rfl⟩ := h
  show c p.1 * u p * u ⟨p.1, j p.1⟩ = c p.1 * u ⟨p.1, j p.1⟩ * u p
  ring

theorem sameOrbit_of_minor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hκ : Function.Injective κ) (hvb : ∀ p, (v p).1 = κ p.1)
    (hvr : ∀ q : Σ k', ι' k', q.1 ∈ Set.range κ → q ∈ Set.range v)
    {b : (Σ k', ι' k') → ℂ} (i' : ∀ k', ι' k') (hb : ∀ k', b ⟨k', i' k'⟩ = 1)
    {u : (Σ k, ι k) → ℂ} (j : ∀ k, ι k) (hj : ∀ k, u ⟨k, j k⟩ ≠ 0)
    (hm : ∀ p, b (v p) * u ⟨p.1, j p.1⟩ = b (v ⟨p.1, j p.1⟩) * u p) :
    SameOrbit (fun p => b (v p)) u := by
  have hne : ∀ k, b (v ⟨k, j k⟩) ≠ 0 := by
    intro k h0
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    have h1 := hm ⟨k₀, i₀⟩
    dsimp only at h1
    rw [hp, hb, h0, zero_mul, one_mul] at h1
    exact hj k₀ h1
  refine ⟨fun k => b (v ⟨k, j k⟩) / u ⟨k, j k⟩, fun k => div_ne_zero (hne k) (hj k),
    funext fun p => ?_⟩
  show b (v p) = b (v ⟨p.1, j p.1⟩) / u ⟨p.1, j p.1⟩ * u p
  rw [div_mul_eq_mul_div, ← hm p, mul_div_assoc, div_self (hj _), mul_one]

theorem proof : FibreIsolFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hB hA u
  obtain ⟨hκ, -, hvb, hvr⟩ := hB
  have hP' : IsMultiHomogIdeal P' := hA.2.1.2.1
  by_cases hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0
  swap
  · refine ⟨∅, fun z' hz' ho _ => absurd ?_ hu⟩
    intro k
    obtain ⟨i', hi'⟩ := hz'.1 (κ k)
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    obtain ⟨c, -, hc⟩ := ho
    refine ⟨i₀, fun h0 => hi' ?_⟩
    have h1 : z' (v ⟨k₀, i₀⟩) = c k₀ * u ⟨k₀, i₀⟩ := congrFun hc ⟨k₀, i₀⟩
    rw [hp, h0, mul_zero] at h1
    exact h1
  choose j hj using hu
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty ((Σ k', ι' k') ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩

  let S : (∀ k', ι' k') → Set (MvPolynomial (Fin N) ℂ) := fun i' =>
    {s | (∃ f ∈ P', s = rename e (map (Int.castRingHom ℂ) f)) ∨
      (∃ k', s = X (e ⟨k', i' k'⟩) - 1) ∨
      ∃ p : Σ k, ι k, s = X (e (v p)) * C (u ⟨p.1, j p.1⟩) - X (e (v ⟨p.1, j p.1⟩)) * C (u p)}
  have hS : ∀ i' (y : Fin N → ℂ), (∀ s ∈ S i', eval y s = 0) ↔
      ((∀ f ∈ P', eval (y ∘ e) (map (Int.castRingHom ℂ) f) = 0) ∧ (∀ k', y (e ⟨k', i' k'⟩) = 1) ∧
        ∀ p, y (e (v p)) * u ⟨p.1, j p.1⟩ = y (e (v ⟨p.1, j p.1⟩)) * u p) := by
    intro i' y
    constructor
    · intro h
      refine ⟨fun f hf => ?_, fun k' => ?_, fun p => ?_⟩
      · have h1 := h _ (Or.inl ⟨f, hf, rfl⟩)
        rwa [eval_rename] at h1
      · have h1 := h _ (Or.inr (Or.inl ⟨k', rfl⟩))
        simp only [map_sub, map_one, eval_X] at h1
        exact sub_eq_zero.mp h1
      · have h1 := h _ (Or.inr (Or.inr ⟨p, rfl⟩))
        simp only [map_sub, map_mul, eval_X, eval_C] at h1
        exact sub_eq_zero.mp h1
    · rintro ⟨h1, h2, h3⟩ s (⟨f, hf, rfl⟩ | ⟨k', rfl⟩ | ⟨p, rfl⟩)
      · rw [eval_rename]
        exact h1 f hf
      · simp only [map_sub, map_one, eval_X]
        rw [h2 k', sub_self]
      · simp only [map_sub, map_mul, eval_X, eval_C]
        rw [h3 p, sub_self]
  have hfin := fun i' => isolated_finite N (S i')
  let T : Finset ((Σ k', ι' k') → ℂ) :=
    Finset.univ.biUnion fun i' : (∀ k', ι' k') => (hfin i').toFinset.image fun y => y ∘ e
  refine ⟨T, fun z' hz' ho hiso => ?_⟩
  choose i' hi' using hz'.1
  obtain ⟨ε, hε, hball⟩ := hiso

  let d : K' → ℂ := fun k' => (z' ⟨k', i' k'⟩)⁻¹
  have hd : ∀ k', d k' ≠ 0 := fun k' => inv_ne_zero (hi' k')
  let a : (Σ k', ι' k') → ℂ := fun q => d q.1 * z' q
  have ha1 : ∀ k', a ⟨k', i' k'⟩ = 1 := fun k' => inv_mul_cancel₀ (hi' k')
  have haP : a ∈ mcPts P' := mcPts_smul hP' d hd hz'
  have hao : SameOrbit (fun p => a (v p)) u := sameOrbit_comp_smul hvb ho d hd
  let w₀ : Fin N → ℂ := a ∘ e.symm
  have hw₀ : w₀ ∘ e = a := funext fun q => by simp [w₀]
  have hw₀Z : ∀ s ∈ S i', eval w₀ s = 0 := by
    refine (hS i' w₀).mpr ⟨by rw [hw₀]; exact haP.2, fun k' => ?_, fun p => ?_⟩
    · simpa [w₀] using ha1 k'
    · simpa [w₀] using minor_of_sameOrbit hao j p
  have hw₀iso : ∀ᶠ y in 𝓝 w₀, (∀ s ∈ S i', eval y s = 0) → y = w₀ := by
    let g : (Fin N → ℂ) → (Σ k', ι' k') → ℂ := fun y q => z' ⟨q.1, i' q.1⟩ * y (e q)
    have hg : Continuous g := continuous_pi fun q => continuous_const.mul (continuous_apply _)
    have hgw : g w₀ = z' := funext fun q => by
      show z' ⟨q.1, i' q.1⟩ * (d (e.symm (e q)).1 * z' (e.symm (e q))) = z' q
      rw [Equiv.symm_apply_apply]
      exact mul_inv_cancel_left₀ (hi' q.1) (z' q)
    have hmem : g ⁻¹' Metric.ball z' ε ∈ 𝓝 w₀ :=
      hg.continuousAt.preimage_mem_nhds (by rw [hgw]; exact Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem] with y hy hyS
    obtain ⟨h1, h2, h3⟩ := (hS i' y).mp hyS
    have hbP : y ∘ e ∈ mcPts P' := ⟨fun k' => ⟨i' k', by simp [h2 k']⟩, h1⟩
    have hbo : SameOrbit (fun p => (y ∘ e) (v p)) u :=
      sameOrbit_of_minor (b := y ∘ e) hκ hvb hvr i' (fun k' => h2 k') j hj h3
    have hgP : g y ∈ mcPts P' := mcPts_smul hP' (fun k' => z' ⟨k', i' k'⟩) hi' hbP
    have hgo : SameOrbit (fun p => g y (v p)) u :=
      sameOrbit_comp_smul hvb hbo (fun k' => z' ⟨k', i' k'⟩) hi'
    obtain ⟨c₁, -, hgz⟩ := hball (g y) hgP hgo hy
    have hc1 : ∀ k', c₁ k' = 1 := fun k' => by
      have h : z' ⟨k', i' k'⟩ * y (e ⟨k', i' k'⟩) = c₁ k' * z' ⟨k', i' k'⟩ := congrFun hgz ⟨k', i' k'⟩
      rw [h2 k', mul_one] at h
      exact mul_right_cancel₀ (hi' k') (h.symm.trans (one_mul _).symm)
    funext x
    have h : z' ⟨(e.symm x).1, i' (e.symm x).1⟩ * y (e (e.symm x)) = c₁ (e.symm x).1 * z' (e.symm x) :=
      congrFun hgz (e.symm x)
    rw [hc1, one_mul, Equiv.apply_symm_apply] at h
    show y x = (z' ⟨(e.symm x).1, i' (e.symm x).1⟩)⁻¹ * z' (e.symm x)
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hi' _), one_mul]
  refine ⟨w₀ ∘ e, Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _,
    Finset.mem_image.mpr ⟨w₀, (hfin i').mem_toFinset.mpr ⟨hw₀Z, hw₀iso⟩, rfl⟩⟩, ?_⟩
  rw [hw₀]
  exact ⟨fun k' => z' ⟨k', i' k'⟩, hi', funext fun q => (mul_inv_cancel_left₀ (hi' q.1) (z' q)).symm⟩

end FibreIsolFinite

end GroundTheory.Heights₂.Heights.Inter
