import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.EpowCongr

noncomputable section

open MeasureTheory Matrix Finset Set Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Partial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_snd' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) (v : Mat n) :
    fderiv ℝ (fun y => U (s, y)) x v = fderiv ℝ U (s, x) (0, v) := by
  have h : HasFDerivAt (fun y : Mat n => U (s, y)) ((fderiv ℝ U (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) x :=
    hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [h.fderiv]
  rfl

theorem hasDerivAt_fst' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) :
    HasDerivAt (fun t => U (t, x)) (fderiv ℝ U (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × Mat n)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hU.hasFDerivAt.comp_hasDerivAt s hp

theorem fderiv_apply_const' {F : ℝ × Mat n → (ℝ × Mat n →L[ℝ] W)} {q : ℝ × Mat n} (hF : DifferentiableAt ℝ F q)
    (w d : ℝ × Mat n) : fderiv ℝ (fun q' => F q' w) q d = fderiv ℝ F q d w := by
  have h : HasFDerivAt (fun q' => F q' w) ((ContinuousLinearMap.apply ℝ W w).comp (fderiv ℝ F q)) q :=
    (ContinuousLinearMap.apply ℝ W w).hasFDerivAt.comp q hF.hasFDerivAt
  exact congrFun (congrArg DFunLike.coe h.fderiv) d

theorem mixed' {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) (a b : ℝ × Mat n) :
    fderiv ℝ (fun q' => fderiv ℝ U q' a) q b = fderiv ℝ (fun q' => fderiv ℝ U q' b) q a := by
  have hd := hU.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hdq : DifferentiableAt ℝ (fderiv ℝ U) q :=
    (hd.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hs := (hU.contDiffAt (hO.mem_nhds hq)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  rw [fderiv_apply_const' hdq, fderiv_apply_const' hdq]
  exact hs b a

theorem pd_smooth {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) (a : ℝ × Mat n) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ U q a) O :=
  (hU.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem diffAt_of {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) : DifferentiableAt ℝ U q :=
  (hU.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)

end Partial

theorem dc_add_smul (hG : GelComm) {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    (F₁ F₂ : Mat n → E.V) (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) (c : ℂ) :
    ∀ x ∈ GLs n, DC ε Fr (c • (F₁ + F₂)) x = c • (DC ε Fr F₁ x + DC ε Fr F₂ x) := by
  intro x hx
  have hs : ContDiffOn ℝ ∞ (F₁ + F₂) (GLs n) := h₁.add h₂
  simp only [DC]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GlobalTheory.CompanionTheory.RCalc.Rd_smul c (hb p) hs hx, Pi.smul_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add (hb p) h₁ h₂ hx, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, map_add, map_smul, smul_add]
  abel

theorem om_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ∀ x ∈ GLs n, Om (DC ε Fr f) x = DC ε Fr (Om f) x := by
  intro x hx
  have ht := (hG n E.V E.V true 2 f hf).1
  have hfa := (hG n E.V E.V false 2 f hf).1
  have e : Om f = (2 : ℂ) • (gel true 2 f + gel false 2 f) := rfl
  rw [e, dc_add_smul hG _ _ ht hfa 2 x hx]
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [gel_DC hG h f hf true 2 x hx, gel_DC hG h f hf false 2 x hx]

theorem dCwave_of (hin : DCinCE) : DCwave := by
  intro hG n lam E Fr ε ι S Γ T hCx u hu
  obtain ⟨hsm, hCE, heq, h0⟩ := hu
  set O : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hOdef
  have hO : IsOpen O := isOpen_univ.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs
  set Ψ : ℝ × Mat n → E.V := Function.uncurry u with hΨ
  have hmem : ∀ s, ∀ x ∈ GLs n, ((s, x) : ℝ × Mat n) ∈ O := fun s x hx => ⟨Set.mem_univ _, hx⟩
  set A : ℝ × Mat n → E.V := fun q => fderiv ℝ Ψ q (1, 0) with hA
  have hAs : ContDiffOn ℝ ∞ A O := pd_smooth hO hsm (1, 0)
  set B : ℝ × Mat n → E.V := fun q => fderiv ℝ A q (1, 0) with hB
  have hBs : ContDiffOn ℝ ∞ B O := pd_smooth hO hAs (1, 0)
  set D : Fin n × Fin n → (E.V →L[ℂ] E.V) := fun p => fderiv ℝ Fr 1 (hb p) with hD

  have hslice : ∀ s, ∀ x ∈ GLs n, DC ε Fr (u s) x =
      ∑ p, ε (hb p) (fderiv ℝ Ψ (s, x) (0, x * hb p) + D p (Ψ (s, x))) := by
    intro s x hx
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show u s = fun y => Ψ (s, y) from rfl, fderiv_snd' (diffAt_of hO hsm (hmem s x hx))]

  have hΨA : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => u t x) (A (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := Ψ) (diffAt_of hO hsm (hmem s x hx))
  have hAB : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => A (t, x)) (B (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := A) (diffAt_of hO hAs (hmem s x hx))
  have hBom : ∀ s, ∀ x ∈ GLs n, B (s, x) = Om (u s) x := by
    intro s x hx
    rw [← heq s x hx, iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun t => u t x) = fun t => A (t, x) := funext fun t => (hΨA t x hx).deriv
    rw [h1, (hAB s x hx).deriv]
  have hdpsi : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ Ψ (t, x) w) (fderiv ℝ A (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ Ψ q w) (s, x) := diffAt_of hO (pd_smooth hO hsm w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hsm (hmem s x hx) w (1, 0)] at this
  have hdA : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ A (t, x) w) (fderiv ℝ B (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ A q w) (s, x) := diffAt_of hO (pd_smooth hO hAs w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hAs (hmem s x hx) w (1, 0)] at this
  refine ⟨?_, fun t => hin n lam E Fr ε ι S Γ T hCx (u t) (hCE t), ?_, ?_⟩
  ·
    have hsm' : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n =>
        ∑ p, ε (hb p) (fderiv ℝ Ψ q (0, q.2 * hb p) + D p (Ψ q))) O := by
      refine ContDiffOn.sum fun p _ => ?_
      refine ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn ?_
      refine ContDiffOn.add ?_ (((D p).restrictScalars ℝ).contDiff.comp_contDiffOn hsm)
      have hv : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((0 : ℝ), q.2 * hb p)) :=
        contDiff_const.prodMk ((GlobalTheory.CompanionTheory.RCalc.mulR (hb p)).contDiff.comp contDiff_snd)
      exact (hsm.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply hv.contDiffOn
    refine hsm'.congr fun q hq => ?_
    obtain ⟨s, x⟩ := q
    exact hslice s x hq.2
  · intro t g hg
    have hf : ∀ s, (fun s => DC ε Fr (u s) g) s = ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
      fun s => hslice s g hg
    have hf1 : ∀ s, HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g)))) s := by
      intro s
      have : (fun s => DC ε Fr (u s) g) = fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
        funext hf
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdpsi _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hΨA s g hg)))
    have hf2 : ∀ s, HasDerivAt (fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))))
        (∑ p, ε (hb p) (fderiv ℝ B (s, g) (0, g * hb p) + D p (B (s, g)))) s := by
      intro s
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdA _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hAB s g hg)))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have e1 : deriv (fun s => DC ε Fr (u s) g) =
        fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))) := funext fun s => (hf1 s).deriv
    rw [e1, (hf2 t).deriv]
    have hu2 : ContDiffOn ℝ ∞ (u t) (GLs n) := (hCE t).1
    have hom : ContDiffOn ℝ ∞ (Om (u t)) (GLs n) := by
      have ht := (hG n E.V E.V true 2 (u t) hu2).1
      have hfa := (hG n E.V E.V false 2 (u t) hu2).1
      exact (ht.add hfa).const_smul (2 : ℂ)
    rw [om_DC hG hCx (u t) hu2 g hg]
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hBe : EqOn (fun y => B (t, y)) (Om (u t)) (GLs n) := fun y hy => hBom t y hy
    have hev : (fun y => B (t, y)) =ᶠ[𝓝 g] Om (u t) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) hBe
    rw [← fderiv_snd' (diffAt_of hO hBs (hmem t g hg)), hev.fderiv_eq, hBom t g hg]
  · intro g hg
    have hf1 : HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (0, g) (0, g * hb p) + D p (A (0, g)))) 0 := by
      have : (fun s => DC ε Fr (u s) g) =
          fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) := funext fun s => hslice s g hg
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
        ((hdpsi _ 0 g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hΨA 0 g hg)))
    rw [hf1.deriv]
    have hA0 : ∀ x ∈ GLs n, A (0, x) = 0 := fun x hx => by rw [← (hΨA 0 x hx).deriv]; exact h0 x hx
    have hev : (fun y => A (0, y)) =ᶠ[𝓝 g] fun _ => (0 : E.V) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hA0 y hy
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← fderiv_snd' (diffAt_of hO hAs (hmem 0 g hg)), hev.fderiv_eq, hA0 g hg]
    simp

end PositivityTheory.RgBcC.LfSt.ChainOf2
