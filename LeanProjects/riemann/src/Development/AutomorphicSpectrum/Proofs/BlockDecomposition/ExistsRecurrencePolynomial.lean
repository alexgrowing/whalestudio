import Mathlib

open Polynomial

namespace GlobalTheory.CompanionTheory.KillDeg

theorem exists_common_eigvector {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} (f : ι → Module.End ℂ V) (hc : ∀ i j, Commute (f i) (f j))
    (W : Submodule ℂ V) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ w ∈ W, f i w ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i v = μ • v := by
  classical
  let P : ℕ → Prop := fun n => ∃ U : Submodule ℂ V, U ≤ W ∧ U ≠ ⊥ ∧
    (∀ i, ∀ w ∈ U, f i w ∈ U) ∧ Module.finrank ℂ U = n
  have hP : ∃ n, P n := ⟨_, W, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU, hUinv, hUn⟩ := Nat.find_spec hP
  have hmin : ∀ U' : Submodule ℂ V, U' ≤ U → U' ≠ ⊥ → (∀ i, ∀ w ∈ U', f i w ∈ U') → U' = U := by
    intro U' hle hne hinv'
    have h1 : Nat.find hP ≤ Module.finrank ℂ U' :=
      Nat.find_min' hP ⟨U', hle.trans hUW, hne, hinv', rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  let r : Module.End ℂ U := (f i).restrict (hUinv i)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue r
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hxe : f i (x : V) = μ • (x : V) := by
    have := congrArg Subtype.val hx.apply_eq_smul
    simpa [r] using this
  have hx0 : (x : V) ≠ 0 := by
    intro h
    exact hx.2 (Subtype.ext h)
  let U' : Submodule ℂ V := U ⊓ Module.End.eigenspace (f i) μ
  have hU' : U' = U := by
    refine hmin U' inf_le_left ?_ ?_
    · intro hb
      have hxm : (x : V) ∈ U' := ⟨x.2, Module.End.mem_eigenspace_iff.2 hxe⟩
      rw [hb] at hxm
      exact hx0 (by simpa using hxm)
    · intro j w hw
      refine ⟨hUinv j w hw.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hwe : f i w = μ • w := Module.End.mem_eigenspace_iff.1 hw.2
      have hcomm : f i (f j w) = f j (f i w) := by
        have := congrArg (fun e : Module.End ℂ V => e w) (hc i j).eq
        simpa using this
      rw [hcomm, hwe, map_smul]
  have hvm : v ∈ U' := by rw [hU']; exact hvU
  exact ⟨μ, Module.End.mem_eigenspace_iff.1 hvm.2⟩

theorem char_eq_cexp (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : ∃ c : ℂ, ∀ t : ℝ, χ t = Complex.exp (c * t) := by
  let I : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, χ s
  have hI : ∀ x, HasDerivAt I (χ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, I δ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : I = fun _ => 0 := funext hcon
    have h1 := hI 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have hint : ∀ a b : ℝ, IntervalIntegrable χ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hid : ∀ t, χ t * I δ = I (t + δ) - I t := by
    intro t
    have h1 : ∫ s in (0 : ℝ)..δ, χ (t + s) = χ t * I δ := by
      simp only [hm, I]
      exact intervalIntegral.integral_const_mul _ _
    have h2 : ∫ s in (0 : ℝ)..δ, χ (t + s) = ∫ s in (t + 0)..(t + δ), χ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := δ) χ t
    have h3 : I t + ∫ s in t..(t + δ), χ s = I (t + δ) :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    rw [← h1, h2, add_zero, ← h3]
    ring
  let c : ℂ := (χ δ - 1) / I δ
  have hd : ∀ t, HasDerivAt χ (c * χ t) t := by
    intro t
    have h1 : HasDerivAt (fun u => I (u + δ)) (χ (t + δ)) t := by
      simpa using (hI (t + δ)).comp_add_const t δ
    have h2 : HasDerivAt (fun u => (I (u + δ) - I u) / I δ) ((χ (t + δ) - χ t) / I δ) t :=
      (h1.sub (hI t)).div_const _
    have h3 : (fun u => (I (u + δ) - I u) / I δ) = χ := by
      funext u
      rw [← hid u]
      field_simp
    rw [h3] at h2
    have h4 : (χ (t + δ) - χ t) / I δ = c * χ t := by
      simp only [c, hm]
      field_simp
    rwa [h4] at h2
  refine ⟨c, fun t => ?_⟩
  let y : ℝ → ℂ := fun u => χ u * Complex.exp (-(c * u))
  have hy : ∀ u, HasDerivAt y 0 u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => -(c * (u : ℂ))) (-c) u := by
      have h0' : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      have h := h0'.const_mul (-c)
      rw [mul_one] at h
      have he : (fun y : ℝ => -(c * (y : ℂ))) = fun y : ℝ => -c * (y : ℂ) := by
        funext y
        ring
      rw [he]
      exact h
    have h2 := (hd u).mul h1.cexp
    have h3 : c * χ u * Complex.exp (-(c * u)) + χ u * (Complex.exp (-(c * u)) * -c) = 0 := by
      ring
    rw [h3] at h2
    exact h2
  have hy0 : y t = y 0 :=
    is_const_of_deriv_eq_zero (fun u => (hy u).differentiableAt) (fun u => (hy u).deriv) t 0
  have hy1 : y 0 = 1 := by simp [y, h0]
  have h5 : χ t * Complex.exp (-(c * t)) = 1 := by
    have : y t = 1 := hy0.trans hy1
    exact this
  rw [Complex.exp_neg] at h5
  have hne := Complex.exp_ne_zero (c * t)
  field_simp at h5
  exact h5

theorem killPoly_natDegree_le (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ)
    (S : Submodule ℂ (ℝ → ℂ)) (ha : ∀ s t, a (s + t) = a s * a t)
    (hcont : ∀ g, Continuous fun t => F₀ (a t * g)) (hfin : FiniteDimensional ℂ S)
    (hS : ∀ g, (fun t => F₀ (a t * g)) ∈ S) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ Module.finrank ℂ S ∧
      (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
      ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
        ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
          ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g := by
  have ha0 : a 0 = 1 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  let τ : ℝ → G → ℂ := fun t g => F₀ (a t * g)
  let T : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range τ)

  let Λ : Module.Dual ℂ S →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun l g => l ⟨fun t => F₀ (a t * g), hS g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hTle : T ≤ LinearMap.range Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    let ev : Module.Dual ℂ S := (LinearMap.proj t : (ℝ → ℂ) →ₗ[ℂ] ℂ).comp S.subtype
    exact ⟨ev, rfl⟩
  haveI hTfin : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTle
  have hrank : Module.finrank ℂ T ≤ Module.finrank ℂ S :=
    (Submodule.finrank_mono hTle).trans
      ((LinearMap.finrank_range_le Λ).trans_eq (Subspace.dual_finrank_eq))

  let L : ℝ → (G → ℂ) →ₗ[ℂ] (G → ℂ) := fun t => LinearMap.funLeft ℂ ℂ (fun g => a t * g)
  have hLap : ∀ t (F : G → ℂ) g, L t F g = F (a t * g) := fun _ _ _ => rfl
  have hLT : ∀ t, ∀ F ∈ T, L t F ∈ T := by
    intro t F hF
    have hmap : T.map (L t) ≤ T := by
      rw [Submodule.map_span_le]
      rintro _ ⟨s, rfl⟩
      refine Submodule.subset_span ⟨s + t, ?_⟩
      funext g
      simp only [hLap, τ, ha, mul_assoc]
    exact hmap ⟨F, hF, rfl⟩
  let R : ℝ → Module.End ℂ T := fun t => (L t).restrict (hLT t)
  have hRap : ∀ t (F : T) g, (R t F : G → ℂ) g = (F : G → ℂ) (a t * g) := fun _ _ _ => rfl
  have hcomm : ∀ s t, Commute (R s) (R t) := by
    intro s t
    refine LinearMap.ext fun F => Subtype.ext (funext fun g => ?_)
    change (R s (R t F) : G → ℂ) g = (R t (R s F) : G → ℂ) g
    rw [hRap, hRap, hRap, hRap, ← mul_assoc, ← mul_assoc, ← ha, ← ha, add_comm]
  have hpow : ∀ (j : ℕ) (F : T) g, (((R 1) ^ j) F : G → ℂ) g = (F : G → ℂ) (a j * g) := by
    intro j
    induction j with
    | zero =>
      intro F g
      simp [ha0]
    | succ j ih =>
      intro F g
      rw [pow_succ']
      change (R 1 (((R 1) ^ j) F) : G → ℂ) g = _
      rw [hRap, ih, ← mul_assoc, ← ha]
      push_cast
      rfl
  have hint : IsIntegral ℂ (R 1) := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly ℂ (R 1)).natDegree ≤ Module.finrank ℂ T := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly (R 1))
      (LinearMap.charpoly_monic (R 1)).ne_zero
    rwa [LinearMap.charpoly_natDegree] at h1
  refine ⟨minpoly ℂ (R 1), minpoly.monic hint, hdeg.trans hrank, ?_, ?_⟩
  · intro g
    have hz : Polynomial.aeval (R 1) (minpoly ℂ (R 1)) = 0 := minpoly.aeval ℂ (R 1)
    rw [Polynomial.aeval_eq_sum_range] at hz
    let f₀ : T := ⟨τ 0, Submodule.subset_span ⟨0, rfl⟩⟩
    have h1 := congrArg (fun e : Module.End ℂ T => ((e f₀ : T) : G → ℂ) g) hz
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow]
    simp [f₀, τ, ha0]
  · intro z hz
    have hev : (R 1).HasEigenvalue z := Module.End.hasEigenvalue_of_isRoot hz
    obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
    have hWne : Module.End.eigenspace (R 1) z ≠ ⊥ := by
      intro hb
      have hxm : x ∈ Module.End.eigenspace (R 1) z :=
        Module.End.mem_eigenspace_iff.2 hx.apply_eq_smul
      rw [hb] at hxm
      exact hx.2 (by simpa using hxm)
    obtain ⟨v, hvW, hv0, hv⟩ := exists_common_eigvector R hcomm _ hWne (by
      intro t w hw
      refine Module.End.mem_eigenspace_iff.2 ?_
      have hwe : R 1 w = z • w := Module.End.mem_eigenspace_iff.1 hw
      have hc1 : R 1 (R t w) = R t (R 1 w) := by
        have := congrArg (fun e : Module.End ℂ T => e w) (hcomm 1 t).eq
        simpa using this
      rw [hc1, hwe, map_smul])
    have hv1 : R 1 v = z • v := Module.End.mem_eigenspace_iff.1 hvW
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, (v : G → ℂ) g₀ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv0 (Subtype.ext (funext hcon))
    let χ : ℝ → ℂ := fun t => (v : G → ℂ) (a t * g₀) / (v : G → ℂ) g₀
    have hχ : ∀ t g, (v : G → ℂ) (a t * g) = χ t * (v : G → ℂ) g := by
      intro t g
      obtain ⟨μ, hμ⟩ := hv t
      have he : ∀ g, (v : G → ℂ) (a t * g) = μ * (v : G → ℂ) g := by
        intro g
        have := congrArg (fun w : T => (w : G → ℂ) g) hμ
        simpa [hRap] using this
      have hμχ : χ t = μ := by
        simp only [χ]
        rw [he g₀]
        field_simp
      rw [hμχ, he g]
    have hspan : ∀ F ∈ T, ∀ g, Continuous fun t => F (a t * g) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨s, rfl⟩ := hF
        intro g
        have he : (fun t => τ s (a t * g)) = fun t => F₀ (a t * (a s * g)) := by
          funext t
          simp only [τ]
          rw [← mul_assoc, ← mul_assoc, ← ha, ← ha, add_comm]
        rw [he]
        exact hcont _
      | zero =>
        intro g
        exact continuous_const
      | add F₁ F₂ _ _ h₁ h₂ =>
        intro g
        exact (h₁ g).add (h₂ g)
      | smul r F _ h =>
        intro g
        exact (h g).const_smul r
    have hχc : Continuous χ := (hspan _ v.2 g₀).div_const _
    have hχ0 : χ 0 = 1 := by
      simp only [χ, ha0, one_mul]
      exact div_self hg₀
    have hχm : ∀ s t, χ (s + t) = χ s * χ t := by
      intro s t
      have h1 : (v : G → ℂ) (a (s + t) * g₀) = χ s * (χ t * (v : G → ℂ) g₀) := by
        rw [ha, mul_assoc, hχ s, hχ t]
      have h2 := hχ (s + t) g₀
      rw [h2] at h1
      have h3 : χ (s + t) * (v : G → ℂ) g₀ = (χ s * χ t) * (v : G → ℂ) g₀ := by
        rw [h1]
        ring
      exact mul_right_cancel₀ hg₀ h3
    obtain ⟨c, hc⟩ := char_eq_cexp χ hχc hχ0 hχm
    refine ⟨c, ?_, (v : G → ℂ), v.2, ?_, ?_⟩
    · have h1 : (v : G → ℂ) (a 1 * g₀) = z * (v : G → ℂ) g₀ := by
        have := congrArg (fun w : T => (w : G → ℂ) g₀) hv1
        simpa [hRap] using this
      have h2 := hχ 1 g₀
      rw [h1] at h2
      have h3 : z = χ 1 := mul_right_cancel₀ hg₀ h2
      rw [h3, hc 1]
      simp
    · intro h
      exact hv0 (Subtype.ext h)
    · intro t g
      rw [hχ t g, hc t]

end GlobalTheory.CompanionTheory.KillDeg
