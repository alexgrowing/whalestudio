import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmulRApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

noncomputable section

open Finset Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.NFRO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

section Main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem zeta_muZ (hB : RadBase k r z z' μsec π π') {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    zetaL k r z z' (Fin.last r) (muZ k r μsec ζ) = ζ := by
  have hz : inWb k r z := hB.2.1
  have hz' : inWb k r z' := hB.2.2.1
  have hS := (hB.2.2.2.2.2.1.2 ζ hζ).2
  have e1 : fvec k r z (Fin.last r) = z := by simp [fvec]
  have e2 : fvec k r z' (Fin.last r) = z' := by simp [fvec]
  unfold zetaL muZ
  rw [e1, e2, ← TwoByOneBlock.jV_wbPart hz, ← TwoByOneBlock.jV_wbPart hz', TwoByOneBlock.emb_mulVec_jV, TwoByOneBlock.herm_jV]
  exact hS

theorem isOpen_QR : IsOpen (QR k r z z') := by
  have h1 : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l : Fin r, {x : Fin r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  exact (h1.preimage continuous_fst).inter (h2.preimage continuous_snd)

theorem radR_mulZ (hB : RadBase k r z z' μsec π π') (f : ℂ → ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k r z z' π π') {x : (Fin r → ℂ) × ℂ} (hx : x ∈ QR k r z z') :
    radR k r z z' μsec (mulZ k r z z' f Φ) x = f x.2 • radR k r z z' μsec Φ x := by
  simp only [radR, Set.indicator_of_mem hx, mulZ_eq f hΦ, zeta_muZ hB hx.2]

theorem radR_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F G : Fn k r E) (x : (Fin r → ℂ) × ℂ) :
    radR k r z z' μsec (F - G) x = radR k r z z' μsec F x - radR k r z z' μsec G x := by
  unfold radR
  by_cases hx : x ∈ QR k r z z' <;> simp [hx]

theorem radR_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F G : Fn k r E) (x : (Fin r → ℂ) × ℂ) :
    radR k r z z' μsec (F + G) x = radR k r z z' μsec F x + radR k r z z' μsec G x := by
  unfold radR
  by_cases hx : x ∈ QR k r z z' <;> simp [hx]

theorem radR_zero' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (x : (Fin r → ℂ) × ℂ) :
    radR k r z z' μsec (0 : Fn k r E) x = 0 := by
  unfold radR
  by_cases hx : x ∈ QR k r z z' <;> simp [hx]

theorem mulZ_congr {f g : ℂ → ℂ} (h : Set.EqOn f g {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : Fn k r E) : mulZ k r z z' f Φ = mulZ k r z z' g Φ := by
  funext c g0
  simp only [mulZ]
  by_cases hx : (c, g0) ∈ DomR k r z z'
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have h2 : 0 < GGl k r z z' g0 := hx.2.2
    unfold GGl at h2
    show f (zetaL k r z z' (Fin.last r) g0) • Φ c g0 = g (zetaL k r z z' (Fin.last r) g0) • Φ c g0
    rw [h (show Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) g0) by linarith)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem mulZ_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f g : ℂ → ℂ) (Φ : Fn k r E) :
    mulZ k r z z' f (mulZ k r z z' g Φ) = mulZ k r z z' (fun ζ => f ζ * g ζ) Φ := by
  funext c g0
  by_cases hx : (c, g0) ∈ DomR k r z z'
  · simp only [mulZ, Set.indicator_of_mem hx, mul_smul]
  · simp only [mulZ, Set.indicator_of_notMem hx]

theorem mulZ_add_left {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f g : ℂ → ℂ) (Φ : Fn k r E) :
    mulZ k r z z' (fun ζ => f ζ + g ζ) Φ = mulZ k r z z' f Φ + mulZ k r z z' g Φ := by
  funext c g0
  by_cases hx : (c, g0) ∈ DomR k r z z'
  · simp only [mulZ, Pi.add_apply, Set.indicator_of_mem hx, add_smul]
  · simp only [mulZ, Pi.add_apply, Set.indicator_of_notMem hx, add_zero]

theorem mulZ_add_right (f : ℂ → ℂ) (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) :
    mulZ k r z z' f (Φ + Ψ) = mulZ k r z z' f Φ + mulZ k r z z' f Ψ := by
  simpa using mulZ_lin (z := z) (z' := z') f Φ Ψ 1

theorem mulZ_const (c : ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    mulZ k r z z' (fun _ => c) Φ = c • Φ := by
  rw [mulZ_eq _ hΦ]
  rfl

theorem wirt_add {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    dZ (fun ζ => f ζ + g ζ) w = dZ f w + dZ g w ∧ dZb (fun ζ => f ζ + g ζ) w = dZb f w + dZb g w := by
  apply dZ_dZb_of
  intro v
  rw [(hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, fderiv_wirt]
  ring

theorem wirt_mul {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    dZ (fun ζ => f ζ * g ζ) w = f w * dZ g w + g w * dZ f w ∧
      dZb (fun ζ => f ζ * g ζ) w = f w * dZb g w + g w * dZb f w := by
  apply dZ_dZb_of
  intro v
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_wirt]
  ring

variable (T : Module.End ℂ (RadSp k r z z' π π')) (a b : ℂ)

def Good (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} ∧
    ∀ Φ Ψ : RadSp k r z z' π π', (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (Φ : Fn k r (Wq →L[ℂ] Wp)) →
      (T Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (T Φ : Fn k r (Wq →L[ℂ] Wp)) +
        mulZ k r z z' (fun ζ => a * dZ f ζ + b * dZb f ζ) (Φ : Fn k r (Wq →L[ℂ] Wp))

variable {T a b}

theorem isOpen_U : IsOpen {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem good_congr {f g : ℂ → ℂ} (h : Good T a b f) (e : ∀ ζ, f ζ = g ζ) : Good T a b g := by
  obtain rfl : f = g := funext e
  exact h

theorem good_const (c : ℂ) : Good T a b (fun _ => c) := by
  refine ⟨contDiffOn_const, fun Φ Ψ h => ?_⟩
  have hΨ : Ψ = c • Φ := Subtype.ext (by rw [h, mulZ_const c Φ.2]; rfl)
  have e : (fun ζ => a * dZ (fun _ : ℂ => c) ζ + b * dZb (fun _ : ℂ => c) ζ) = fun _ => (0 : ℂ) := by
    funext ζ
    simp [dZ, dZb]
  rw [hΨ, map_smul, e, mulZ_const c (T Φ).2, mulZ_const 0 Φ.2, zero_smul, add_zero]
  rfl

theorem good_id (ha : ∀ Φ Ψ : RadSp k r z z' π π', (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (Φ : Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (T Φ : Fn k r (Wq →L[ℂ] Wp)) + a • (Φ : Fn k r (Wq →L[ℂ] Wp))) :
    Good T a b id := by
  refine ⟨contDiff_id.contDiffOn, fun Φ Ψ h => ?_⟩
  rw [ha Φ Ψ h]
  have hd : ∀ ζ, dZ id ζ = 1 ∧ dZb id ζ = 0 := fun ζ => dZ_dZb_of (fun v => by rw [fderiv_id]; simp)
  have e : (fun ζ => a * dZ id ζ + b * dZb id ζ) = fun _ => a := by
    funext ζ
    simp [(hd ζ).1, (hd ζ).2]
  rw [e, mulZ_const a Φ.2]

theorem good_conj (hb : ∀ Φ Ψ : RadSp k r z z' π π', (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (T Φ : Fn k r (Wq →L[ℂ] Wp)) + b • (Φ : Fn k r (Wq →L[ℂ] Wp))) :
    Good T a b (starRingEnd ℂ) := by
  have ec : (⇑(starRingEnd ℂ) : ℂ → ℂ) = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) := by
    funext w
    simp
  refine ⟨by rw [ec]; exact Complex.conjCLE.contDiff.contDiffOn, fun Φ Ψ h => ?_⟩
  rw [hb Φ Ψ h]
  have hd : ∀ ζ, dZ (starRingEnd ℂ) ζ = 0 ∧ dZb (starRingEnd ℂ) ζ = 1 := fun ζ =>
    dZ_dZb_of (fun v => by rw [ec, ContinuousLinearEquiv.fderiv]; simp)
  have e : (fun ζ => a * dZ (starRingEnd ℂ) ζ + b * dZb (starRingEnd ℂ) ζ) = fun _ => b := by
    funext ζ
    simp [(hd ζ).1, (hd ζ).2]
  rw [e, mulZ_const b Φ.2]

theorem good_add {f g : ℂ → ℂ} (hf : Good T a b f) (hg : Good T a b g) : Good T a b (fun ζ => f ζ + g ζ) := by
  refine ⟨hf.1.add hg.1, fun Φ Ψ h => ?_⟩
  let Ψf : RadSp k r z z' π π' := ⟨mulZ k r z z' f Φ, mulZ_mem hf.1 Φ.2⟩
  let Ψg : RadSp k r z z' π π' := ⟨mulZ k r z z' g Φ, mulZ_mem hg.1 Φ.2⟩
  have hΨ : Ψ = Ψf + Ψg := Subtype.ext (by rw [h, mulZ_add_left]; rfl)
  have hL : Set.EqOn (fun ζ => a * dZ (fun ζ => f ζ + g ζ) ζ + b * dZb (fun ζ => f ζ + g ζ) ζ)
      (fun ζ => (a * dZ f ζ + b * dZb f ζ) + (a * dZ g ζ + b * dZb g ζ))
      {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} := by
    intro w hw
    have hfd := (hf.1.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hw)
    have hgd := (hg.1.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hw)
    simp only [(wirt_add hfd hgd).1, (wirt_add hfd hgd).2]
    ring
  rw [hΨ, map_add, Submodule.coe_add, hf.2 Φ Ψf rfl, hg.2 Φ Ψg rfl, mulZ_congr hL]
  simp only [mulZ_add_left]
  abel

theorem good_mul {f g : ℂ → ℂ} (hf : Good T a b f) (hg : Good T a b g) : Good T a b (fun ζ => f ζ * g ζ) := by
  refine ⟨hf.1.mul hg.1, fun Φ Ψ h => ?_⟩
  let Ψg : RadSp k r z z' π π' := ⟨mulZ k r z z' g Φ, mulZ_mem hg.1 Φ.2⟩
  have eg : (Ψg : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' g Φ := rfl
  have h1 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (mulZ k r z z' g Φ) := by rw [h, mulZ_mul]
  have hL : Set.EqOn (fun ζ => a * dZ (fun ζ => f ζ * g ζ) ζ + b * dZb (fun ζ => f ζ * g ζ) ζ)
      (fun ζ => f ζ * (a * dZ g ζ + b * dZb g ζ) + (a * dZ f ζ + b * dZb f ζ) * g ζ)
      {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} := by
    intro w hw
    have hfd := (hf.1.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hw)
    have hgd := (hg.1.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hw)
    simp only [(wirt_mul hfd hgd).1, (wirt_mul hfd hgd).2]
    ring
  rw [hf.2 Ψg Ψ h1, hg.2 Φ Ψg rfl, eg, mulZ_add_right, mulZ_mul, mulZ_mul, mulZ_mul, mulZ_congr hL,
    mulZ_add_left, add_assoc]

theorem good_pow {f : ℂ → ℂ} (hf : Good T a b f) (n : ℕ) : Good T a b (fun ζ => f ζ ^ n) := by
  induction n with
  | zero => exact good_congr (good_const 1) (fun ζ => by simp)
  | succ n ih => exact good_congr (good_mul ih hf) (fun ζ => by ring)

theorem good_mono (ha : ∀ Φ Ψ : RadSp k r z z' π π', (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (Φ : Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (T Φ : Fn k r (Wq →L[ℂ] Wp)) + a • (Φ : Fn k r (Wq →L[ℂ] Wp)))
    (hb : ∀ Φ Ψ : RadSp k r z z' π π', (Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (T Φ : Fn k r (Wq →L[ℂ] Wp)) + b • (Φ : Fn k r (Wq →L[ℂ] Wp)))
    (ζ0 c : ℂ) (j l : ℕ) : Good T a b (fun x => c * mono ζ0 j l x) := by
  have h1 := good_add (good_id (b := b) ha) (good_const (T := T) (a := a) (b := b) (-ζ0))
  have h2 := good_add (good_conj (a := a) hb) (good_const (T := T) (a := a) (b := b) (-star ζ0))
  refine good_congr (good_mul (good_const c) (good_mul (good_pow h1 j) (good_pow h2 l))) (fun x => ?_)
  simp only [mono, id, sub_eq_add_neg]
  rfl

end Main

theorem radOrder0_of (hMem : RadRedMem) (hInj : RadRedInj) : RadOrder0 := by
  intro Wp Wq _ _ _ _ _ _ k r z z' μsec π π' hB T a b hT ha hb f hf Φ Ψ hΨ
  obtain ⟨n, A, -, hA⟩ := hT
  have hUo : IsOpen {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} := isOpen_U
  have hQo : IsOpen (QR k r z z') := isOpen_QR
  have hg : ContDiffOn ℝ ∞ (fun ζ => a * dZ f ζ + b * dZb f ζ) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} :=
    (contDiffOn_const.mul (contDiffOn_dZ hUo hf)).add (contDiffOn_const.mul (contDiffOn_dZb hUo hf))
  have hsm : ContDiffOn ℝ ∞ (radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp))) (QR k r z z') :=
    (hMem Wp Wq k r z z' μsec π π' hB _ Φ.2).1
  let D : RadSp k r z z' π π' := T Ψ - mulZEnd hf (T Φ) - mulZEnd hg Φ
  have eD : (D : Fn k r (Wq →L[ℂ] Wp)) = (T Ψ : Fn k r (Wq →L[ℂ] Wp)) - mulZ k r z z' f (T Φ : Fn k r (Wq →L[ℂ] Wp)) -
      mulZ k r z z' (fun ζ => a * dZ f ζ + b * dZb f ζ) (Φ : Fn k r (Wq →L[ℂ] Wp)) := rfl
  have key : radR k r z z' μsec (D : Fn k r (Wq →L[ℂ] Wp)) =
      radR k r z z' μsec ((0 : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) := by
    funext x
    rw [Submodule.coe_zero, radR_zero']
    by_cases hx : x ∈ QR k r z z'
    swap
    · simp [radR, hx]

    have hΛeq : ∀ h : ℂ → ℂ, ContDiffOn ℝ ∞ h {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} →
        ∀ Ψh : RadSp k r z z' π π', (Ψh : Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' h (Φ : Fn k r (Wq →L[ℂ] Wp)) →
        (∑ j ∈ Finset.range (n + 1), A j x (iteratedFDeriv ℝ j
            (fun y => h y.2 • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) y) x)) -
          h x.2 • radR k r z z' μsec (T Φ : Fn k r (Wq →L[ℂ] Wp)) x -
          (a * dZ h x.2 + b * dZb h x.2) • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x =
        radR k r z z' μsec (T Ψh : Fn k r (Wq →L[ℂ] Wp)) x -
          h x.2 • radR k r z z' μsec (T Φ : Fn k r (Wq →L[ℂ] Wp)) x -
          (a * dZ h x.2 + b * dZb h x.2) • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x := by
      intro h _ Ψh hΨh
      rw [hA Ψh x hx]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      have hev : (fun y => h y.2 • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) y) =ᶠ[𝓝 x]
          radR k r z z' μsec (Ψh : Fn k r (Wq →L[ℂ] Wp)) :=
        Filter.eventually_of_mem (hQo.mem_nhds hx) fun y hy => by rw [hΨh, radR_mulZ hB h Φ.2 hy]
      rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    have hJ : JetR {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} x.2 (fun h =>
        (∑ j ∈ Finset.range (n + 1), A j x (iteratedFDeriv ℝ j
            (fun y => h y.2 • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) y) x)) -
          h x.2 • radR k r z z' μsec (T Φ : Fn k r (Wq →L[ℂ] Wp)) x -
          (a * dZ h x.2 + b * dZb h x.2) • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x) := by
      have hI : ∀ j ∈ Finset.range (n + 1), JetR {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} x.2 (fun h =>
          A j x (iteratedFDeriv ℝ j (fun y => h y.2 • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) y) x)) :=
        fun j _ => jetR_map (A j x).toLinearMap
          (jetR_iter (ContinuousLinearMap.snd ℝ (Fin r → ℂ) ℂ) hUo hQo (fun y hy => hy.2) hx j
            (Wq →L[ℂ] Wp) _ hsm)
      refine jetR_sub (jetR_sub (jetR_sum _ hI)
        (jetR_congr (jetR_word [] (cl 1 (radR k r z z' μsec (T Φ : Fn k r (Wq →L[ℂ] Wp)) x)))
          (fun h _ => by simp [cl_apply, wd])))
        (jetR_congr (jetR_add (jetR_word [false] (cl a (radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x)))
          (jetR_word [true] (cl b (radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x))))
          (fun h _ => by simp [cl_apply, wd, add_smul]))
    have hmono : ∀ (c : ℂ) (j l : ℕ), (fun h : ℂ → ℂ =>
        (∑ j ∈ Finset.range (n + 1), A j x (iteratedFDeriv ℝ j
            (fun y => h y.2 • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) y) x)) -
          h x.2 • radR k r z z' μsec (T Φ : Fn k r (Wq →L[ℂ] Wp)) x -
          (a * dZ h x.2 + b * dZb h x.2) • radR k r z z' μsec (Φ : Fn k r (Wq →L[ℂ] Wp)) x)
        (fun y => c * mono x.2 j l y) = 0 := by
      intro c j l
      have hG := good_mono ha hb x.2 c j l
      let Ψh : RadSp k r z z' π π' := ⟨mulZ k r z z' _ Φ, mulZ_mem hG.1 Φ.2⟩
      beta_reduce
      rw [hΛeq _ hG.1 Ψh rfl, hG.2 Φ Ψh rfl, radR_add, radR_mulZ hB _ (T Φ).2 hx, radR_mulZ hB _ Φ.2 hx]
      abel
    have h0 := jetR_zero hUo hx.2 hJ hmono f hf
    rw [hΛeq f hf Ψ hΨ] at h0
    rw [eD, radR_sub, radR_sub, radR_mulZ hB _ (T Φ).2 hx, radR_mulZ hB _ Φ.2 hx]
    exact h0
  have hD0 := hInj Wp Wq k r z z' μsec π π' hB _ D.2 _ (0 : RadSp k r z z' π π').2 key
  rw [eD, Submodule.coe_zero, sub_sub, sub_eq_zero] at hD0
  exact hD0

end Formalism.FourierDecayAlt.P.NFRO

namespace Formalism.FourierDecayAlt.P

theorem nf_radOrder0_of_radRed : Formalism.FourierDecayAlt.NF.RadRedMem → Formalism.FourierDecayAlt.NF.RadRedInj → Formalism.FourierDecayAlt.NF.RadOrder0 :=
  NFRO.radOrder0_of

theorem radical_order_zero : Formalism.FourierDecayAlt.NF.RadOrder0 :=
  nf_radOrder0_of_radRed radical_reduction_mem radical_reduction_injective

end Formalism.FourierDecayAlt.P
