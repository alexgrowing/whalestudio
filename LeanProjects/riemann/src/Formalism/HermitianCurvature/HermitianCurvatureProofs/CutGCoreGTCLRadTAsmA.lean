import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

def Ann {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}

theorem ann_open {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Ann z z') :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exists_pr {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) :
    ∃ Pr : V →ₗ[ℂ] V, (∀ x, Pr x ∈ S) ∧ ∀ x ∈ S, Pr x = x := by
  obtain ⟨q, hq⟩ := S.exists_isCompl
  refine ⟨S.subtype ∘ₗ S.linearProjOfIsCompl q hq, fun x => (S.linearProjOfIsCompl q hq x).2, fun x hx => ?_⟩
  exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨x, hx⟩)

def e2 : Fin 2 → ℂ := ![1, Complex.I]

def crd : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]

theorem sum_crd (v : ℂ) : ∑ t : Fin 2, crd t v • e2 t = v := by
  simp only [Fin.sum_univ_two, crd, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul, mul_one]
  exact Complex.re_add_im v

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ml_expand {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) E) (v : ℂ) :
    m (fun _ => v) = ∑ s : Fin j → Fin 2, (∏ i, crd (s i) v) • m (fun i => e2 (s i)) := by
  have h : (fun _ : Fin j => v) = fun _ => ∑ t : Fin 2, crd t v • e2 t := funext fun _ => (sum_crd v).symm
  rw [h, m.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact m.map_smul_univ (fun i => crd (s i) v) (fun i => e2 (s i))

end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def fibS (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (ζ : ℂ) : Submodule ℂ (Wq →L[ℂ] Wp) where
  carrier := NF.Fib k r z z' μs π π' ζ
  add_mem' := by
    intro X X' hX hX' p hp
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX p hp, hX' p hp]
  zero_mem' := by
    intro p _
    simp
  smul_mem' := by
    intro s X hX p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX p hp]

theorem radR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ : Q.Fn k r E) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ NF.QR k r z z') : NF.radR k r z z' μs Φ q = Φ q.1 (NF.muZ k r μs q.2) := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq]

theorem radR_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ + Ψ) = NF.radR k r z z' μs Φ + NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ - Ψ) = NF.radR k r z z' μs Φ - NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (s : ℂ) (Φ : Q.Fn k r E) :
    NF.radR k r z z' μs (s • Φ) = s • NF.radR k r z z' μs Φ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} :
    NF.radR k r z z' μs (0 : Q.Fn k r E) = 0 := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

end

end

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

def phiP (z z' : Fin (2 * r + k + 1) → ℂ) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) (p : ℂ → (Wq →L[ℂ] Wp)) :
    (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp) :=
  (NF.QR k r z z').indicator fun q => Pr (p q.2)

def Gd (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  NF.RadBase k r z z' μs π π' ∧ ∀ x, ∀ ζ ∈ Ann z z', Pr x ∈ NF.Fib k r z z' μs π π' ζ

theorem pr_contDiff (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : ContDiff ℝ ∞ (fun x => Pr x) :=
  (LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)).contDiff

theorem phiP_mem (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    phiP z z' Pr p ∈ NF.RadSec k r z z' μs π π' := by
  refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine ((pr_contDiff Pr).comp (hp.comp contDiff_snd)).contDiffOn.congr fun q hq => ?_
    simp only [phiP, Set.indicator_of_mem hq, Function.comp]
  · simp only [phiP, Set.indicator_of_mem hq]
    exact hG.2 _ _ hq.2
  · simp only [phiP, Set.indicator_of_notMem hq]

def PhiP (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (p : ℂ → (Wq →L[ℂ] Wp)) : Q.RadSp k r z z' π π' :=
  if h : Gd z z' μs π π' Pr ∧ ContDiff ℝ ∞ p then
    ⟨Classical.choose (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2)),
     (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2))).1⟩
  else 0

theorem radR_PhiP (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    NF.radR k r z z' μs ((PhiP z z' μs π π' Pr p : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) =
      phiP z z' Pr p := by
  unfold PhiP
  rw [dif_pos ⟨hG, hp⟩]
  exact (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' hG.1 (phiP z z' Pr p)
      (phiP_mem hG hp))).2

theorem eq_of_radR (hG : Gd z z' μs π π' Pr) {Φ Ψ : Q.RadSp k r z z' π π'}
    (h : NF.radR k r z z' μs (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp))) :
    Φ = Ψ :=
  Subtype.ext (Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq k r z z' μs π π' hG.1 Φ Φ.2 Ψ Ψ.2 h)

theorem PhiP_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') :
    PhiP z z' μs π π' Pr (fun ζ => p ζ + p' ζ) = PhiP z z' μs π π' Pr p + PhiP z z' μs π π' Pr p' := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.add hp'), Submodule.coe_add, radR_add, radR_PhiP hG hp, radR_PhiP hG hp']
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) :
    PhiP z z' μs π π' Pr (fun ζ => s • p ζ) = s • PhiP z z' μs π π' Pr p := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.const_smul s), Submodule.coe_smul, radR_smul, radR_PhiP hG hp]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_zero (hG : Gd z z' μs π π' Pr) : PhiP z z' μs π π' Pr (fun _ => 0) = 0 := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG contDiff_const, Submodule.coe_zero, radR_zero]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

def VV (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (p : ℂ → (Wq →L[ℂ] Wp)) (ζ : ℂ) : Wq →L[ℂ] Wp :=
  NF.radR k r z z' μs ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c0, ζ)

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem VV_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => p ζ + p' ζ) ζ = VV z z' μs π π' Pr T c0 p ζ + VV z z' μs π π' Pr T c0 p' ζ := by
  unfold VV
  rw [PhiP_add hG hp hp', map_add, Submodule.coe_add, radR_add]
  rfl

theorem VV_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  unfold VV
  rw [PhiP_smul hG hp, map_smul, Submodule.coe_smul, radR_smul]
  rfl

theorem VV_smulR (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℝ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  have h := VV_smul (T := T) (c0 := c0) hG hp (s : ℂ) ζ
  simp only [Complex.coe_smul] at h
  exact h

theorem VV_zero (hG : Gd z z' μs π π' Pr) (ζ : ℂ) : VV z z' μs π π' Pr T c0 (fun _ => 0) ζ = 0 := by
  unfold VV
  rw [PhiP_zero hG, map_zero, Submodule.coe_zero, radR_zero]
  rfl

theorem VV_sum (hG : Gd z z' μs π π' Pr) {ι : Type} (s : Finset ι) (p : ι → ℂ → (Wq →L[ℂ] Wp))
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => ∑ i ∈ s, p i ζ) ζ = ∑ i ∈ s, VV z z' μs π π' Pr T c0 (p i) ζ := by
  induction s using Finset.induction_on with
  | empty => simpa using VV_zero (T := T) (c0 := c0) hG ζ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [VV_add hG (hp i) (ContDiff.sum fun j _ => hp j), ih]

theorem VV_smooth (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hc0 : c0 ∈ OmX r) :
    ContDiffOn ℝ ∞ (VV z z' μs π π' Pr T c0 p) (Ann z z') := by
  have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq k r z z' μs π π' hG.1
    ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp))
    (T (PhiP z z' μs π π' Pr p)).2
  exact hm.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc0, hζ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
