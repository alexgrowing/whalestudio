import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology

namespace GlobalTheory

section Affine

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [NormedSpace ℂ V] in

lemma exists_mem_four_of_open_dense {U : Set V} (ho : IsOpen U) (hd : Dense U)
    (e₁ e₂ e₃ e₄ : V ≃ₜ V) : ∃ x, e₁ x ∈ U ∧ e₂ x ∈ U ∧ e₃ x ∈ U ∧ e₄ x ∈ U := by
  have hD : ∀ e : V ≃ₜ V, Dense (e ⁻¹' U) := fun e => hd.preimage e.isOpenMap
  have hO : ∀ e : V ≃ₜ V, IsOpen (e ⁻¹' U) := fun e => ho.preimage e.continuous
  exact ((hD e₁).inter_of_isOpen_left ((hD e₂).inter_of_isOpen_left
    ((hD e₃).inter_of_isOpen_left (hD e₄) (hO e₃)) (hO e₂)) (hO e₁)).nonempty

lemma exists_linear_increment {U : Set V} (ho : IsOpen U) (hd : Dense U) {f : V → ℂ} {c₀ : ℂ}
    (hf : ∀ a ∈ U, ∀ b ∈ U, -a - b ∈ U → c₀ + f a + f b + f (-a - b) = 0)
    {a₀ : V} (ha₀ : a₀ ∈ U) (hdf : DifferentiableAt ℂ f a₀) :
    ∃ L : V →L[ℂ] ℂ, ∀ a t, a ∈ U → a + t ∈ U → f (a + t) - f a = L t := by
  have h1 : ∀ t a b, a ∈ U → a + t ∈ U → b ∈ U → b + t ∈ U → -a - t - b ∈ U →
      f (a + t) - f a = f (b + t) - f b := by
    intro t a b ha hat hb hbt hab
    have e1 : -(a + t) - b = -a - t - b := by abel
    have e2 : -a - (b + t) = -a - t - b := by abel
    have h1 := hf _ hat _ hb (e1 ▸ hab)
    have h2 := hf _ ha _ hbt (e2 ▸ hab)
    rw [e1] at h1
    rw [e2] at h2
    linear_combination h1 - h2
  have h2 : ∀ t a b, a ∈ U → a + t ∈ U → b ∈ U → b + t ∈ U →
      f (a + t) - f a = f (b + t) - f b := by
    intro t a b ha hat hb hbt
    obtain ⟨d, hd1, hd2, hd3, hd4⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight t) (Homeomorph.subLeft (-a - t)) (Homeomorph.subLeft (-b - t))
    rw [h1 t a d ha hat hd1 hd2 hd3, h1 t b d hb hbt hd1 hd2 hd4]
  have h3 : ∀ t : V, ∃ p, p ∈ U ∧ p + t ∈ U := by
    intro t
    obtain ⟨d, hd1, hd2, -⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight t) (Homeomorph.refl V) (Homeomorph.refl V)
    exact ⟨d, hd1, hd2⟩
  choose p hp hpt using h3
  set l : V → ℂ := fun t => f (p t + t) - f (p t) with hl
  have hla : ∀ a t, a ∈ U → a + t ∈ U → f (a + t) - f a = l t := fun a t ha hat =>
    h2 t a (p t) ha hat (hp t) (hpt t)
  have hadd : ∀ s t, l (s + t) = l s + l t := by
    intro s t
    obtain ⟨d, hd1, hd2, hd3, -⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight s) (Homeomorph.addRight (s + t)) (Homeomorph.refl V)
    have hd1' : d ∈ U := hd1
    have hd2' : d + s ∈ U := hd2
    have hd3' : d + (s + t) ∈ U := hd3
    rw [← hla d _ hd1' hd3', ← hla d _ hd1' hd2', ← hla (d + s) t hd2' (by rwa [add_assoc]),
      add_assoc]
    ring
  have hl0 : l 0 = 0 := by simp [hl]
  set L := fderiv ℂ f a₀
  have hL0 : HasFDerivAt l L 0 := by
    have hA : HasFDerivAt (fun t => f (a₀ + t) - f a₀) L 0 := by
      refine HasFDerivAt.sub_const _ ?_
      have : HasFDerivAt f L (a₀ + 0) := by simpa using hdf.hasFDerivAt
      exact (hasFDerivAt_comp_add_left a₀).2 this
    refine hA.congr_of_eventuallyEq ?_
    have : ∀ᶠ t in 𝓝 (0 : V), a₀ + t ∈ U :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (ho.mem_nhds (by simpa using ha₀))
    filter_upwards [this] with t ht
    exact (hla a₀ t ha₀ ht).symm
  have hL : ∀ x, HasFDerivAt l L x := by
    intro x
    have hA : HasFDerivAt (fun t => l x + l (-x + t)) L x := by
      refine HasFDerivAt.const_add _ ?_
      have : HasFDerivAt l L (-x + x) := by simpa using hL0
      exact (hasFDerivAt_comp_add_left (-x)).2 this
    have : (fun t => l x + l (-x + t)) = l := by
      funext t
      rw [← hadd]; congr 1; abel
    rwa [this] at hA
  refine ⟨L, fun a t ha hat => ?_⟩
  have hz : ∀ x, HasFDerivAt (fun t => l t - L t) (0 : V →L[ℂ] ℂ) x := fun x => by
    have := (hL x).sub (L.hasFDerivAt (x := x))
    rw [sub_self] at this
    exact this
  have := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun t => l t - L t)
    (fun x => (hz x).differentiableAt) (fun x => (hz x).fderiv) t 0
  rw [hla a t ha hat]
  simp only [hl0, map_zero, sub_zero] at this
  exact sub_eq_zero.1 this

end Affine

variable {ι : Type} [Fintype ι]

lemma hasFDerivAt_Hf_left (γ v : EuclideanSpace ℂ ι) :
    ∃ A : EuclideanSpace ℂ ι →L[ℂ] ℂ, (∀ c, A c = Hf c γ) ∧ HasFDerivAt (fun v => Hf v γ) A v := by
  have h : ∀ c : EuclideanSpace ℂ ι, innerSL ℂ γ c = Hf c γ := fun c => by
    simp [Hf, PiLp.inner_apply]
  refine ⟨innerSL ℂ γ, h, ?_⟩
  have : (fun v => Hf v γ) = innerSL ℂ γ := by funext v; exact (h v).symm
  rw [this]
  exact (innerSL ℂ γ).hasFDerivAt

lemma fderiv_sec_add (Y : GT ι) {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (a c : EuclideanSpace ℂ ι) :
    fderiv ℂ θ (a + γ) c * θ a = θ (a + γ) * (Real.pi * Hf c γ * θ a + fderiv ℂ θ a c) := by
  obtain ⟨hd, hl⟩ := hθ
  obtain ⟨A, hA, hA'⟩ := hasFDerivAt_Hf_left γ a
  have h1 : HasFDerivAt (fun v => θ (v + γ)) (fderiv ℂ θ (a + γ)) a :=
    (hasFDerivAt_comp_add_right γ).2 (hd _).hasFDerivAt
  have h2 := ((((hA'.const_mul (((1 : ℕ) : ℂ) * Real.pi)).add_const
    (((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2)).cexp).const_mul (Y.ka γ)).mul (hd a).hasFDerivAt
  have h3 : (fun v => θ (v + γ)) = _ := funext (hl γ hγ)
  rw [h3] at h1
  have h4 := congrArg (fun B => B c) (h1.unique h2)
  rw [h4, hl γ hγ a]
  simp [hA]
  ring

theorem level_three_separates_tangents {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (c₀ : ℂ) (c : EuclideanSpace ℂ ι)
    (h : ∀ a b, c₀ * (θ a * θ b * θ (-a - b)) + fderiv ℂ (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) 0 c = 0) : c = 0 ∧ c₀ = 0 := by
  have hd : Differentiable ℂ θ := hθ.1
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ =>
    SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem
  set U : Set (EuclideanSpace ℂ ι) := {x | θ x ≠ 0} with hU
  have ho : IsOpen U := isOpen_ne_fun hd.continuous continuous_const
  have hden : Dense U := by
    intro x
    by_contra hx
    apply h0
    refine han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hy'
    exact hy (subset_closure hy')
  have hder : ∀ a b, fderiv ℂ (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) 0 c =
      fderiv ℂ θ a c * θ b * θ (-a - b) + θ a * fderiv ℂ θ b c * θ (-a - b)
        + θ a * θ b * fderiv ℂ θ (-a - b) c := by
    intro a b
    have ht : ∀ x, HasFDerivAt (fun v => θ (v + x)) (fderiv ℂ θ x) 0 := fun x =>
      (hasFDerivAt_comp_add_right x).2 (by simpa using (hd x).hasFDerivAt)
    have e : (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) =
        ((fun v => θ (v + a)) * fun v => θ (v + b)) * fun v => θ (v + (-a - b)) := by
      funext v
      simp only [Pi.mul_apply]
      congr 2
      abel
    rw [e, (((ht a).mul (ht b)).mul (ht (-a - b))).fderiv]
    simp
    ring
  set f : EuclideanSpace ℂ ι → ℂ := fun x => fderiv ℂ θ x c / θ x with hfdef
  have hf : ∀ a ∈ U, ∀ b ∈ U, -a - b ∈ U → c₀ + f a + f b + f (-a - b) = 0 := by
    intro a ha b hb hab
    have ha' : θ a ≠ 0 := ha
    have hb' : θ b ≠ 0 := hb
    have hab' : θ (-a - b) ≠ 0 := hab
    have := h a b
    rw [hder] at this
    simp only [hfdef]
    field_simp
    linear_combination this
  obtain ⟨a₀, ha₀⟩ := hden.nonempty
  have ha₀' : θ a₀ ≠ 0 := ha₀
  have hdf : DifferentiableAt ℂ f a₀ := by
    simp only [hfdef, div_eq_mul_inv]
    exact (((han a₀ trivial).fderiv.differentiableAt).clm_apply (differentiableAt_const c)).mul
      ((hd a₀).inv ha₀')
  obtain ⟨L, hL⟩ := exists_linear_increment ho hden hf ha₀ hdf
  have hlat : ∀ γ ∈ lat Y.b, L γ = Real.pi * Hf c γ := by
    intro γ hγ
    have hne : θ (a₀ + γ) ≠ 0 := by
      rw [hθ.2 γ hγ]
      have : Y.ka γ ≠ 0 := by
        intro hk
        have := Y.ka_abs γ hγ
        simp [hk] at this
      exact mul_ne_zero (mul_ne_zero this (exp_ne_zero _)) ha₀'
    rw [← hL a₀ γ ha₀ hne]
    have := fderiv_sec_add Y hθ hγ a₀ c
    simp only [hfdef]
    field_simp
    linear_combination this
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    simp [Hf, PiLp.inner_apply]
  let M : EuclideanSpace ℂ ι →ₗ[ℝ] ℂ :=
    { toFun := fun v => Real.pi * inner ℂ v c
      map_add' := fun x y => by rw [inner_add_left]; ring
      map_smul' := fun r x => by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
        simp
        ring }
  have hM : (L : EuclideanSpace ℂ ι →ₗ[ℂ] ℂ).restrictScalars ℝ = M := by
    refine Y.b.ext fun i => ?_
    have := hlat (Y.b i) (Submodule.subset_span ⟨i, rfl⟩)
    rw [hH] at this
    exact this
  have hLM : ∀ v, L v = Real.pi * inner ℂ v c := fun v => LinearMap.congr_fun hM v
  have hc : c = 0 := by
    have h1 := hLM (I • c)
    rw [map_smul, hLM, inner_smul_left, conj_I, smul_eq_mul] at h1
    have h2 : (2 * I * Real.pi) * inner ℂ c c = 0 := by linear_combination h1
    have h3 : (2 * I * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    exact inner_self_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left h3)
  refine ⟨hc, ?_⟩
  obtain ⟨d, hd1, hd2, -⟩ := exists_mem_four_of_open_dense ho hden (Homeomorph.refl _)
    (Homeomorph.subLeft (-a₀)) (Homeomorph.refl _) (Homeomorph.refl _)
  have := hf a₀ ha₀ d hd1 hd2
  simpa [hfdef, hc] using this

end GlobalTheory
