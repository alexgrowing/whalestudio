import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAbsOfLeAbs

namespace GlobalTheory.QuasiPshTruncation

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem two_le_inf' : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem levi_add_const (f : (ι → ℂ) → ℝ) (k : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + k) z w = levi f z w := by
  have h : fderiv ℝ (fun y => f y + k) = fderiv ℝ f := funext fun y => fderiv_add_const k
  unfold levi
  rw [h]

theorem levi_real_comp {f : (ι → ℂ) → ℝ} {g : ℝ → ℝ} {z : ι → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiff ℝ 2 g) (w : ι → ℂ) :
    levi (g ∘ f) z w = deriv g (f z) * levi f z w +
      deriv (deriv g) (f z) * ((fderiv ℝ f z w) ^ 2 + (fderiv ℝ f z (Complex.I • w)) ^ 2) / 4 := by
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).1 hg).2.2
  have hg2 : HasDerivAt (deriv g) (deriv (deriv g) (f z)) (f z) :=
    ((hg1.differentiable (by norm_num)) (f z)).hasDerivAt
  have hfd : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (deriv g ∘ f) (deriv (deriv g) (f z) • fderiv ℝ f z) z :=
    hg2.comp_hasFDerivAt z hfd
  have hev : fderiv ℝ (g ∘ f) =ᶠ[𝓝 z] (deriv g ∘ f) • fderiv ℝ f := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact ((hgd (f y)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD := ((hc.smul hf').congr_of_eventuallyEq hev).fderiv
  unfold levi
  rw [hD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

theorem levi_nonneg_add_comp {φ F : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {z w : ι → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hF : ContDiffAt ℝ 2 F z) (hG : ContDiff ℝ 2 G)
    (hG1 : 0 ≤ deriv G (F z)) (hG1' : deriv G (F z) ≤ 1) (hG2 : 0 ≤ deriv (deriv G) (F z))
    (h0 : 0 ≤ levi φ z w) (h1 : 0 ≤ levi (fun y => φ y + F y) z w) :
    0 ≤ levi (fun y => φ y + G (F y)) z w := by
  have hGF : ContDiffAt ℝ 2 (G ∘ F) z := hG.contDiffAt.comp z hF
  have e1 := levi_add_smul 1 hφ hGF w
  have e2 := levi_add_smul 1 hφ hF w
  simp only [one_mul, Function.comp_apply] at e1 e2
  rw [e1, levi_real_comp hF hG w]
  rw [e2] at h1
  have hq : 0 ≤ (fderiv ℝ F z w) ^ 2 + (fderiv ℝ F z (Complex.I • w)) ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hG1') h0, mul_nonneg hG1 h1, mul_nonneg hG2 hq]

theorem regMax_slice {m : ℝ × ℝ → ℝ} (hmC : ContDiff ℝ (⊤ : ℕ∞) m) (hconv : ConvexOn ℝ Set.univ m)
    (hmono : Monotone m) (htr : ∀ a b c, m (a + c, b + c) = m (a, b) + c) (c k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => m (t, c) - k) ∧ (∀ t, 0 ≤ deriv (fun t => m (t, c) - k) t) ∧
      (∀ t, deriv (fun t => m (t, c) - k) t ≤ 1) ∧
      ∀ t, 0 ≤ deriv (deriv (fun t => m (t, c) - k)) t := by
  set G : ℝ → ℝ := fun t => m (t, c) - k with hG
  have hGC : ContDiff ℝ (⊤ : ℕ∞) G :=
    (hmC.comp (contDiff_id.prodMk contDiff_const)).sub contDiff_const
  have hGd : Differentiable ℝ G := hGC.differentiable (by simp)
  have hGm : Monotone G := by
    intro a b hab
    have := hmono (show ((a, c) : ℝ × ℝ) ≤ (b, c) from ⟨hab, le_rfl⟩)
    simp only [hG]; linarith
  have hGl : Monotone (fun t => t - G t) := by
    intro a b hab
    have h1 := hmono (show ((b, c) : ℝ × ℝ) ≤ (a + (b - a), c + (b - a)) from
      ⟨by simp, by simp; linarith⟩)
    have h2 := htr a c (b - a)
    simp only [hG]; linarith
  have hGconv : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h := hconv.2 (Set.mem_univ (x, c)) (Set.mem_univ (y, c)) ha hb hab
    have e : a • ((x, c) : ℝ × ℝ) + b • (y, c) = (a • x + b • y, c) := by
      ext
      · simp
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [← add_mul, hab, one_mul]
    rw [e] at h
    simp only [hG, smul_eq_mul] at h ⊢
    have hk : a * k + b * k = k := by rw [← add_mul, hab, one_mul]
    nlinarith
  refine ⟨hGC, fun t => hGm.deriv_nonneg, fun t => ?_, fun t => ?_⟩
  · have h := (hGl.deriv_nonneg (x := t))
    have e : deriv (fun t => t - G t) t = 1 - deriv G t :=
      deriv_sub differentiableAt_id (hGd t) |>.trans (by simp)
    rw [e] at h
    linarith
  · have hmd : Monotone (deriv G) := by
      have := hGconv.monotoneOn_deriv (fun x _ => hGd x)
      exact monotoneOn_univ.1 this
    exact hmd.deriv_nonneg

theorem exists_truncation : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Om : LocPot X) (Z : Set X) (u : X → ℝ) (M : ℝ), 2 ≤ M → IsClosed Z →
    IsPotential A Om → IsPsh A Om → A.SmoothOn Zᶜ u → (∀ x ∈ Zᶜ, u x ≤ 0) →
    (∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Om.U x ∩ Zᶜ), ∀ w : Fin e → ℂ,
      0 ≤ levi ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) y w) →
    (∀ a : ℝ, closure {x | x ∈ Zᶜ ∧ -a ≤ u x} ⊆ Zᶜ) →
    ∃ (v : X → ℝ) (η : ℝ), A.Smooth v ∧ IsPsh A (Om + LocPot.ofFun v) ∧
      (∀ x, -M ≤ v x ∧ v x ≤ 0) ∧ 0 ≤ η ∧ η ≤ 1 / 4 ∧
      (∀ x ∈ Zᶜ, -M + 2 ≤ u x → v x = u x - η) ∧ ∀ x ∈ Zᶜ, u x - η ≤ v x := by
  intro e X _ _ _ A Om Z u M hM hZ hpot hpsh hsm hneg hlevi hcl
  obtain ⟨m, hmC, hmconv, hmmono, hmb, hm1, hm2, hmtr⟩ :=
    GlobalTheory.RegularisedMaxTwo.exists_regMaxTwo (1 / 4) (by norm_num)
  set c : ℝ := -M + 1 with hc
  set G : ℝ → ℝ := fun t => m (t, c) - 1 / 4 with hG
  obtain ⟨hGC, hG1, hG1', hG2⟩ := regMax_slice hmC hmconv hmmono hmtr c (1 / 4)
  have hGC2 : ContDiff ℝ 2 G := hGC.of_le two_le_inf'
  have hGlow : ∀ t, t + 1 / 2 ≤ c → G t = c - 1 / 4 := by
    intro t ht
    simp only [hG]
    rw [hm2 t c (by linarith)]
  classical
  let v : X → ℝ := fun x => if x ∈ Z then c - 1 / 4 else G (u x)
  set K := closure {x | x ∈ Zᶜ ∧ -M ≤ u x} with hKdef
  have hK : K ⊆ Zᶜ := hcl M
  have hKc : IsOpen Kᶜ := isClosed_closure.isOpen_compl
  have hvK : ∀ x ∈ Kᶜ, v x = c - 1 / 4 := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · simp [v, hxZ]
    · have hux : u x < -M := by
        by_contra h
        push_neg at h
        exact hx (subset_closure ⟨hxZ, h⟩)
      simp only [v, hxZ, if_false]
      exact hGlow _ (by linarith)
  have hvZ : ∀ x ∈ Zᶜ, v x = G (u x) := by
    intro x hx
    have hx' : x ∉ Z := hx
    simp [v, hx']
  refine ⟨v, 1 / 4, ?_, ?_, ?_, by norm_num, le_rfl, ?_, ?_⟩
  · intro j y hy
    apply ContDiffAt.contDiffWithinAt
    have hyt : y ∈ (A.chart j).target := hy.1
    by_cases hp : (A.chart j).symm y ∈ Z
    · have hO := (A.chart j).isOpen_inter_preimage_symm hKc
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Kᶜ :=
        ⟨hyt, fun h => hK h hp⟩
      have hev : (v ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun _ => c - 1 / 4 := by
        filter_upwards [hO.mem_nhds hyO] with y' hy' using hvK _ hy'.2
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hO := (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ := ⟨hyt, hp⟩
      have hu : ContDiffAt ℝ ∞ (u ∘ (A.chart j).symm) y := (hsm j).contDiffAt (hO.mem_nhds hyO)
      have hev : (v ∘ (A.chart j).symm) =ᶠ[𝓝 y] G ∘ (u ∘ (A.chart j).symm) := by
        filter_upwards [hO.mem_nhds hyO] with y' hy' using hvZ _ hy'.2
      exact (hGC.contDiffAt.comp y hu).congr_of_eventuallyEq hev
  · intro x j y hy w
    have hyt : y ∈ (A.chart j).target := hy.1
    have hyU : (A.chart j).symm y ∈ Om.U x := hy.2.1
    have hOφ := (A.chart j).isOpen_inter_preimage_symm (Om.isOpen_U x)
    have hφ : ContDiffAt ℝ 2 (Om.φ x ∘ (A.chart j).symm) y :=
      ((hpot.1 x j).contDiffAt (hOφ.mem_nhds ⟨hyt, hyU⟩)).of_le two_le_inf'
    have hφ0 : 0 ≤ levi (Om.φ x ∘ (A.chart j).symm) y w := hpsh x j y ⟨hyt, hyU⟩ w
    show 0 ≤ levi ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) y w
    by_cases hp : (A.chart j).symm y ∈ Z
    · have hO := (A.chart j).isOpen_inter_preimage_symm hKc
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Kᶜ :=
        ⟨hyt, fun h => hK h hp⟩
      have hev : ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
          fun z => (Om.φ x ∘ (A.chart j).symm) z + (c - 1 / 4) := by
        filter_upwards [hO.mem_nhds hyO] with y' hy'
        simp only [Function.comp_apply, hvK _ hy'.2]
      rw [levi_congr hev, levi_add_const]
      exact hφ0
    · have hO := (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
      have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ := ⟨hyt, hp⟩
      have hu : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
        ((hsm j).contDiffAt (hO.mem_nhds hyO)).of_le two_le_inf'
      have hev : ((fun z => Om.φ x z + v z) ∘ (A.chart j).symm) =ᶠ[𝓝 y]
          fun z => (Om.φ x ∘ (A.chart j).symm) z + G ((u ∘ (A.chart j).symm) z) := by
        filter_upwards [hO.mem_nhds hyO] with y' hy'
        simp only [Function.comp_apply, hvZ _ hy'.2]
      rw [levi_congr hev]
      exact levi_nonneg_add_comp hφ hu hGC2 (hG1 _) (hG1' _) (hG2 _) hφ0
        (hlevi x j y ⟨hyt, hyU, hp⟩ w)
  · intro x
    by_cases hx : x ∈ Z
    · simp only [v, hx, if_true]
      constructor <;> linarith
    · simp only [v, hx, if_false, hG]
      have hb := hmb (u x) c
      have hu := hneg x hx
      have hmx : max (u x) c ≤ 0 := max_le hu (by linarith)
      constructor
      · linarith [le_max_right (u x) c, hb.1]
      · linarith [hb.2]
  · intro x hx hux
    rw [hvZ x hx]
    simp only [hG]
    rw [hm1 (u x) c (by linarith)]
  · intro x hx
    rw [hvZ x hx]
    simp only [hG]
    linarith [le_max_left (u x) c, (hmb (u x) c).1]

end

end GlobalTheory.QuasiPshTruncation
