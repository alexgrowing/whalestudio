import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical Topology ContDiff

namespace GlobalTheory.LatJet.An.Chain

variable {I : Type} [Fintype I]

theorem iterD_ofFn {f : (I → ℂ) → ℂ} {U : Set (I → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℂ ω f U) :
    ∀ (k : ℕ) (s : Fin k → I), ∀ z ∈ U,
      iterD (List.ofFn s) f z = iteratedFDeriv ℂ k f z (fun a => Pi.single (s a) 1) := by
  intro k
  induction k with
  | zero => intro s z _; simp [iterD]
  | succ k ih =>
    intro s z hz
    have hev : iterD (List.ofFn (Fin.tail s)) f =ᶠ[𝓝 z]
        fun w => iteratedFDeriv ℂ k f w (fun a => Pi.single (Fin.tail s a) 1) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) (ih (Fin.tail s))
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k f) z :=
      (((hf.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right (m := 1) (i := k) le_top)).differentiableAt one_ne_zero
    have e1 : iterD (List.ofFn s) f z = partialD (s 0) (iterD (List.ofFn (Fin.tail s)) f) z := by
      rw [List.ofFn_succ]; rfl
    rw [e1, partialD, hev.lineDeriv_eq, (hd.continuousMultilinear_apply_const _).lineDeriv_eq_fderiv,
      fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
    rfl

theorem iterD_ofFn_zero {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) (s : Fin k → I) :
    iterD (List.ofFn s) f 0 = iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  exact iterD_ofFn Metric.isOpen_ball (hfr.contDiffOn Metric.isOpen_ball.uniqueDiffOn) k s 0
    (Metric.mem_ball_self hr)

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem prod_get (a : I → ℂ) (l : List I) : ∏ b : Fin l.length, a (l.get b) = ∏ i, a i ^ l.count i := by
  rw [show (∏ b : Fin l.length, a (l.get b)) = (l.map a).prod by simpa using Fin.prod_univ_fun_getElem l a]
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [List.count_cons, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single j (fun b _ hb => by simp [beq_iff_eq, Ne.symm hb]) (by simp)]
    simp

theorem iteratedFDeriv_coord {f : (I → ℂ) → I → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) (i : I)
    (m : Fin k → I → ℂ) : iteratedFDeriv ℂ k (fun z => f z i) 0 m = iteratedFDeriv ℂ k f 0 m i := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).iteratedFDeriv_comp_left hf
    (i := k) le_top
  exact congrArg (fun L => L m) h

theorem iteratedFDeriv_comp_clm {f : (I → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : (I → ℂ) →L[ℂ] (I → ℂ))
    (k : ℕ) : iteratedFDeriv ℂ k (f ∘ A) 0 = (iteratedFDeriv ℂ k f 0).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (k : WithTop ℕ∞)) le_top (fun _ => rfl)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hs : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hpre : IsOpen (A ⁻¹' Metric.ball (0 : I → ℂ) r) := hs.preimage A.continuous
  have h0' : (0 : I → ℂ) ∈ A ⁻¹' Metric.ball (0 : I → ℂ) r := by simpa using h0
  have key := A.iteratedFDerivWithin_comp_right (hfu.mono hball) hs.uniqueDiffOn hpre.uniqueDiffOn h0'
    (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre h0', map_zero, iteratedFDerivWithin_of_isOpen k hs h0] at key
  exact key

theorem iteratedFDeriv_comp_congr {g : (I → ℂ) → ℂ} {f₁ f₂ : (I → ℂ) → I → ℂ}
    (hg : ContDiffAt ℂ ω g 0) (h₁ : ContDiffAt ℂ ω f₁ 0) (h₂ : ContDiffAt ℂ ω f₂ 0)
    (e₁ : f₁ 0 = 0) (e₂ : f₂ 0 = 0) (N : ℕ)
    (h : ∀ k ≤ N, iteratedFDeriv ℂ k f₁ 0 = iteratedFDeriv ℂ k f₂ 0) :
    ∀ k ≤ N, iteratedFDeriv ℂ k (g ∘ f₁) 0 = iteratedFDeriv ℂ k (g ∘ f₂) 0 := by
  intro k hk
  rw [iteratedFDeriv_comp (by rw [e₁]; exact hg) h₁ le_top, iteratedFDeriv_comp (by rw [e₂]; exact hg) h₂ le_top, e₁, e₂]
  unfold FormalMultilinearSeries.taylorComp
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : (fun m => ftaylorSeries ℂ f₁ 0 (c.partSize m)) = fun m => ftaylorSeries ℂ f₂ 0 (c.partSize m) :=
    funext fun m => h _ ((c.partSize_le m).trans hk)
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, hc]

theorem jetChain_of_jetCalc : JetCalc → JetChain := by
  intro hC I _ n J ζ a g hζ hζ0 hg hjet ν u hu
  obtain ⟨h1, h2, -, h4, h5, -, -⟩ := hC I n J
  let Λ : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i => a i • ContinuousLinearMap.proj i
  have hΛ : ∀ z i, Λ z i = a i * z i := fun z i => by simp [Λ]
  have hpr : ∀ i, AnalyticAt ℂ (fun z : I → ℂ => z i) 0 := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
  have hΛjet : ∀ i, jet J (fun z => Λ z i) = a i • J.t i := by
    intro i
    have e : (fun z : I → ℂ => Λ z i) = (fun _ => a i) * (fun z => z i) := by funext z; simp [hΛ]
    rw [e, (h2 _ _ analyticAt_const (hpr i)).1, h4, h5, Algebra.smul_def]
  have hζi : ∀ i, AnalyticAt ℂ (fun z => ζ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (ζ 0)).comp hζ
  have hΛi : ∀ i, AnalyticAt ℂ (fun z => Λ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (Λ 0)).comp (Λ.analyticAt 0)
  have hD : ∀ i k, k ≤ n + 1 → iteratedFDeriv ℂ k (fun z => ζ z i) 0 = iteratedFDeriv ℂ k (fun z => Λ z i) 0 := by
    intro i k hk
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ I) fun s => ?_
    simp only [ContinuousMultilinearMap.coe_coe, Pi.basisFun_apply]
    rw [← iterD_ofFn_zero (hζi i) k s, ← iterD_ofFn_zero (hΛi i) k s]
    have hν : ∑ j, (List.ofFn s).count j ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [← h1 _ (hζi i) ⟨_, hν⟩ _ (fun _ => rfl), ← h1 _ (hΛi i) ⟨_, hν⟩ _ (fun _ => rfl), hjet i, hΛjet i]
  have hDv : ∀ k ≤ n + 1, iteratedFDeriv ℂ k ζ 0 = iteratedFDeriv ℂ k Λ 0 := by
    intro k hk
    ext m i
    rw [← iteratedFDeriv_coord hζ.contDiffAt, ← iteratedFDeriv_coord (Λ.analyticAt 0).contDiffAt, hD i k hk]
  have hk : u.length ≤ n + 1 := by
    rw [← sum_count u]; simp only [hu]; exact ν.2
  have hgz : AnalyticAt ℂ (g ∘ ζ) 0 := by
    refine AnalyticAt.comp ?_ hζ
    rw [hζ0]; exact hg
  rw [h1 _ hgz ν u hu]
  have e : ∀ f, iterD u f 0 = iterD (List.ofFn u.get) f 0 := by intro f; rw [List.ofFn_get]
  rw [e, e, iterD_ofFn_zero hgz, iterD_ofFn_zero hg,
    iteratedFDeriv_comp_congr hg.contDiffAt hζ.contDiffAt (Λ.analyticAt 0).contDiffAt hζ0 (map_zero Λ) (n + 1)
      hDv _ hk, iteratedFDeriv_comp_clm hg.contDiffAt]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun b : Fin u.length => Λ (Pi.single (u.get b) 1)) = fun b => a (u.get b) • Pi.single (u.get b) 1 := by
    funext b; ext i; rw [hΛ]
    by_cases h : i = u.get b
    · subst h; simp
    · simp only [List.get_eq_getElem] at h; simp [Pi.single_apply, h]
  rw [hv, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, prod_get, mul_comm]
  simp only [hu]

end GlobalTheory.LatJet.An.Chain
