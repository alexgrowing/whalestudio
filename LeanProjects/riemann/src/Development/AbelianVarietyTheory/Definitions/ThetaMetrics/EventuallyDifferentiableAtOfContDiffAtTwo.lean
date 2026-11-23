import Mathlib

open Complex Filter Topology ComplexConjugate

noncomputable section

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]

theorem realCLM_map_complex_smul (L : E →L[ℝ] F) (c : ℂ) (v : E) :
    L (c • v) = (c.re : ℂ) • L v + (c.im : ℂ) • L (I • v) := by
  have h : c • v = c.re • v + c.im • (I • v) := by
    conv_lhs => rw [← re_add_im c]
    rw [add_smul, mul_smul, ← Complex.coe_algebraMap, algebraMap_smul, algebraMap_smul]
  rw [h, map_add, map_smul, map_smul, ← Complex.coe_algebraMap, algebraMap_smul, algebraMap_smul]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in

theorem I_smul_I_smul (v : E) : I • I • v = -v := by
  rw [smul_smul, I_mul_I, neg_smul, one_smul]

def linPart (L : E →L[ℝ] F) : E →L[ℂ] F where
  toFun v := (1 / 2 : ℂ) • (L v - I • L (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    rw [smul_comm I c v, realCLM_map_complex_smul L c, realCLM_map_complex_smul L c,
      I_smul_I_smul, map_neg, RingHom.id_apply]
    have hc : c = c.re + c.im * I := (re_add_im c).symm
    generalize (c.re : ℂ) = a at *
    generalize (c.im : ℂ) = b at *
    subst hc
    match_scalars
    · ring
    · linear_combination (b / 2) * I_mul_I
  cont := by fun_prop

def antilinPart (L : E →L[ℝ] F) : E →L⋆[ℂ] F where
  toFun v := (1 / 2 : ℂ) • (L v + I • L (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    rw [smul_comm I c v, realCLM_map_complex_smul L c, realCLM_map_complex_smul L c,
      I_smul_I_smul, map_neg]
    have hc : conj c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (c.re : ℂ) = a at *
    generalize (c.im : ℂ) = b at *
    match_scalars
    · ring
    · linear_combination (b / 2) * I_mul_I
  cont := by fun_prop

theorem linPart_apply (L : E →L[ℝ] F) (v : E) :
    linPart L v = (1 / 2 : ℂ) • (L v - I • L (I • v)) := rfl

theorem antilinPart_apply (L : E →L[ℝ] F) (v : E) :
    antilinPart L v = (1 / 2 : ℂ) • (L v + I • L (I • v)) := rfl

theorem linPart_add_antilinPart (L : E →L[ℝ] F) (v : E) :
    linPart L v + antilinPart L v = L v := by
  rw [linPart_apply, antilinPart_apply]; module

theorem linPart_apply_of_map_I {L : E →L[ℝ] F} {v : E} (h : L (I • v) = I • L v) :
    linPart L v = L v := by
  rw [linPart_apply, h, I_smul_I_smul]; module

theorem antilinPart_apply_of_map_I {L : E →L[ℝ] F} {v : E} (h : L (I • v) = I • L v) :
    antilinPart L v = 0 := by
  rw [antilinPart_apply, h, I_smul_I_smul]; module

theorem linPart_restrictScalars (L : E →L[ℂ] F) : linPart (L.restrictScalars ℝ) = L := by
  ext v; exact linPart_apply_of_map_I (by simp)

theorem antilinPart_restrictScalars (L : E →L[ℂ] F) : antilinPart (L.restrictScalars ℝ) = 0 := by
  ext v; exact antilinPart_apply_of_map_I (by simp)

theorem norm_antilinPart_le (L : E →L[ℝ] F) : ‖antilinPart L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [antilinPart_apply, norm_smul]
  have h1 := L.le_opNorm v
  have h2 := L.le_opNorm (I • v)
  have h3 := norm_add_le (L v) (I • L (I • v))
  rw [norm_smul] at h2 h3
  simp only [norm_I, one_mul] at h2 h3
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]; linarith

theorem norm_linPart_le (L : E →L[ℝ] F) : ‖linPart L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [linPart_apply, norm_smul]
  have h1 := L.le_opNorm v
  have h2 := L.le_opNorm (I • v)
  have h3 := norm_sub_le (L v) (I • L (I • v))
  rw [norm_smul] at h2 h3
  simp only [norm_I, one_mul] at h2 h3
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]; linarith

variable (E F) in

def linPartCLM : (E →L[ℝ] F) →L[ℝ] (E →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := linPart
      map_add' := fun L M => by
        ext v; simp only [linPart_apply, ContinuousLinearMap.add_apply]; module
      map_smul' := fun c L => by
        ext v; simp only [linPart_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        rw [smul_comm I c, ← smul_sub, smul_comm] }
    1 fun L => by rw [one_mul]; exact norm_linPart_le L

variable (E F) in

def antilinPartCLM : (E →L[ℝ] F) →L[ℝ] (E →L⋆[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := antilinPart
      map_add' := fun L M => by
        ext v; simp only [antilinPart_apply, ContinuousLinearMap.add_apply]; module
      map_smul' := fun c L => by
        ext v; simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        rw [smul_comm I c, ← smul_add, smul_comm] }
    1 fun L => by rw [one_mul]; exact norm_antilinPart_le L

@[simp] theorem linPartCLM_apply (L : E →L[ℝ] F) : linPartCLM E F L = linPart L := rfl

@[simp] theorem antilinPartCLM_apply (L : E →L[ℝ] F) : antilinPartCLM E F L = antilinPart L := rfl

def del (f : E → F) (z : E) : E →L[ℂ] F := linPart (fderiv ℝ f z)

def dbar (f : E → F) (z : E) : E →L⋆[ℂ] F := antilinPart (fderiv ℝ f z)

def ddbar (u : E → F) (z : E) : E →L[ℂ] E →L⋆[ℂ] F := del (dbar u) z

def leviForm (u : E → ℝ) (z : E) : E →L[ℂ] E →L⋆[ℂ] ℂ := ddbar (fun x => (u x : ℂ)) z

def IsPshC2On (u : E → ℝ) (s : Set E) : Prop :=
  ∀ z ∈ s, ContDiffAt ℝ 2 u z ∧ ∀ v, 0 ≤ (leviForm u z v v).re

section FirstOrder

variable {f g : E → F} {z : E}

theorem del_apply (f : E → F) (z v : E) :
    del f z v = (1 / 2 : ℂ) • (fderiv ℝ f z v - I • fderiv ℝ f z (I • v)) := rfl

theorem dbar_apply (f : E → F) (z v : E) :
    dbar f z v = (1 / 2 : ℂ) • (fderiv ℝ f z v + I • fderiv ℝ f z (I • v)) := rfl

theorem del_add_dbar (f : E → F) (z v : E) : del f z v + dbar f z v = fderiv ℝ f z v :=
  linPart_add_antilinPart _ _

theorem del_eq_of_hasFDerivAt {L : E →L[ℝ] F} (h : HasFDerivAt f L z) : del f z = linPart L := by
  rw [del, h.fderiv]

theorem dbar_eq_of_hasFDerivAt {L : E →L[ℝ] F} (h : HasFDerivAt f L z) :
    dbar f z = antilinPart L := by
  rw [dbar, h.fderiv]

theorem del_congr (h : f =ᶠ[𝓝 z] g) : del f z = del g z := by rw [del, del, h.fderiv_eq]

theorem dbar_congr (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by rw [dbar, dbar, h.fderiv_eq]

theorem del_eq_fderiv (hf : DifferentiableAt ℂ f z) : del f z = fderiv ℂ f z := by
  rw [del, hf.fderiv_restrictScalars ℝ, linPart_restrictScalars]

theorem dbar_eq_zero (hf : DifferentiableAt ℂ f z) : dbar f z = 0 := by
  rw [dbar, hf.fderiv_restrictScalars ℝ, antilinPart_restrictScalars]

@[simp] theorem del_const (c : F) (z : E) : del (fun _ => c) z = 0 := by
  ext v; simp [del_apply]

@[simp] theorem dbar_const (c : F) (z : E) : dbar (fun _ => c) z = 0 := by
  ext v; simp [dbar_apply]

theorem del_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    del (fun x => f x + g x) z = del f z + del g z := by
  rw [del, fderiv_fun_add hf hg]; exact (linPartCLM E F).map_add _ _

theorem dbar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun x => f x + g x) z = dbar f z + dbar g z := by
  rw [dbar, fderiv_fun_add hf hg]; exact (antilinPartCLM E F).map_add _ _

theorem del_neg (f : E → F) (z : E) : del (fun x => -f x) z = -del f z := by
  rw [del, fderiv_fun_neg]; exact (linPartCLM E F).map_neg _

theorem dbar_neg (f : E → F) (z : E) : dbar (fun x => -f x) z = -dbar f z := by
  rw [dbar, fderiv_fun_neg]; exact (antilinPartCLM E F).map_neg _

theorem del_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    del (fun x => f x - g x) z = del f z - del g z := by
  rw [del, fderiv_fun_sub hf hg]; exact (linPartCLM E F).map_sub _ _

theorem dbar_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun x => f x - g x) z = dbar f z - dbar g z := by
  rw [dbar, fderiv_fun_sub hf hg]; exact (antilinPartCLM E F).map_sub _ _

theorem del_sum {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (A i) z) :
    del (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, del (A i) z := by
  rw [del, fderiv_fun_sum h]; exact map_sum (linPartCLM E F) _ _

theorem dbar_sum {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (A i) z) :
    dbar (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, dbar (A i) z := by
  rw [dbar, fderiv_fun_sum h]; exact map_sum (antilinPartCLM E F) _ _

theorem del_smul {c : E → ℂ} (hc : DifferentiableAt ℝ c z) (hf : DifferentiableAt ℝ f z) (v : E) :
    del (fun x => c x • f x) z v = c z • del f z v + del c z v • f z := by
  simp only [del_apply, fderiv_fun_smul hc hf, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem dbar_smul {c : E → ℂ} (hc : DifferentiableAt ℝ c z) (hf : DifferentiableAt ℝ f z) (v : E) :
    dbar (fun x => c x • f x) z v = c z • dbar f z v + dbar c z v • f z := by
  simp only [dbar_apply, fderiv_fun_smul hc hf, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem del_mul {a b : E → ℂ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : E) :
    del (fun x => a x * b x) z v = a z * del b z v + del a z v * b z := del_smul ha hb v

theorem dbar_mul {a b : E → ℂ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : E) :
    dbar (fun x => a x * b x) z v = a z * dbar b z v + dbar a z v * b z := dbar_smul ha hb v

theorem del_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    del (fun x => c • f x) z = c • del f z := by
  ext v; simpa using del_smul (differentiableAt_const c) hf v

theorem dbar_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    dbar (fun x => c • f x) z = c • dbar f z := by
  ext v; simpa using dbar_smul (differentiableAt_const c) hf v

theorem del_clm_comp (T : F →L[ℂ] G) (hf : DifferentiableAt ℝ f z) (v : E) :
    del (fun x => T (f x)) z v = T (del f z v) := by
  rw [del_eq_of_hasFDerivAt (f := fun x => T (f x))
    ((T.restrictScalars ℝ).hasFDerivAt.comp z hf.hasFDerivAt)]
  simp [linPart_apply, del_apply]

theorem dbar_conj (a : E → ℂ) (z v : E) :
    dbar (fun x => conj (a x)) z v = conj (del a z v) := by
  have h : fderiv ℝ (fun x => conj (a x)) z = (conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a z) :=
    conjCLE.comp_fderiv (f := a)
  simp [dbar_apply, del_apply, h, map_ofNat]

theorem del_conj (a : E → ℂ) (z v : E) :
    del (fun x => conj (a x)) z v = conj (dbar a z v) := by
  have h : fderiv ℝ (fun x => conj (a x)) z = (conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a z) :=
    conjCLE.comp_fderiv (f := a)
  simp [dbar_apply, del_apply, h, sub_eq_add_neg, map_ofNat]

theorem dbar_ofReal (u : E → ℝ) (z v : E) :
    dbar (fun x => (u x : ℂ)) z v = conj (del (fun x => (u x : ℂ)) z v) := by
  simpa using dbar_conj (fun x => (u x : ℂ)) z v

theorem del_comp {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℝ φ z) (v : E) :
    del (fun x => u (φ x)) z v = del u (φ z) (del φ z v) + dbar u (φ z) (dbar φ z v) := by
  have h : HasFDerivAt (fun x => u (φ x)) _ z := hu.hasFDerivAt.comp z hφ.hasFDerivAt
  rw [del_apply, h.fderiv, del_apply φ, dbar_apply φ]
  simp only [ContinuousLinearMap.comp_apply, ← del_add_dbar u, map_smul, map_sub, map_add,
    map_smulₛₗ, conj_I, map_div₀, map_one, map_ofNat]
  module

theorem del_comp_holo {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℂ φ z) (v : E) :
    del (fun x => u (φ x)) z v = del u (φ z) (fderiv ℂ φ z v) := by
  rw [del_eq_of_hasFDerivAt (f := fun x => u (φ x))
    (hu.hasFDerivAt.comp z (hφ.hasFDerivAt.restrictScalars ℝ))]
  simp [linPart_apply, del_apply]

theorem dbar_comp_holo {u : F → G} {φ : E → F} (hu : DifferentiableAt ℝ u (φ z))
    (hφ : DifferentiableAt ℂ φ z) (v : E) :
    dbar (fun x => u (φ x)) z v = dbar u (φ z) (fderiv ℂ φ z v) := by
  rw [dbar_eq_of_hasFDerivAt (f := fun x => u (φ x))
    (hu.hasFDerivAt.comp z (hφ.hasFDerivAt.restrictScalars ℝ))]
  simp [antilinPart_apply, dbar_apply]

theorem fderiv_ofReal_apply {u : E → ℝ} (hu : DifferentiableAt ℝ u z) (v : E) :
    fderiv ℝ (fun x => (u x : ℂ)) z v = (fderiv ℝ u z v : ℂ) := by
  have h : HasFDerivAt (fun x => (u x : ℂ)) _ z := ofRealCLM.hasFDerivAt.comp z hu.hasFDerivAt
  rw [h.fderiv]
  simp

theorem del_ofReal_comp {t : E → ℝ} {h : ℝ → ℝ} {h' : ℝ} (hh : HasDerivAt h h' (t z))
    (ht : DifferentiableAt ℝ t z) (v : E) :
    del (fun x => (h (t x) : ℂ)) z v = h' * del (fun x => (t x : ℂ)) z v := by
  have h1 : HasFDerivAt (fun x => h (t x)) _ z := hh.comp_hasFDerivAt z ht.hasFDerivAt
  rw [del_apply, del_apply, fderiv_ofReal_apply h1.differentiableAt,
    fderiv_ofReal_apply h1.differentiableAt, fderiv_ofReal_apply ht, fderiv_ofReal_apply ht,
    h1.fderiv]
  simp; ring

theorem dbar_ofReal_comp {t : E → ℝ} {h : ℝ → ℝ} {h' : ℝ} (hh : HasDerivAt h h' (t z))
    (ht : DifferentiableAt ℝ t z) (v : E) :
    dbar (fun x => (h (t x) : ℂ)) z v = h' * dbar (fun x => (t x : ℂ)) z v := by
  rw [dbar_ofReal, del_ofReal_comp hh ht, dbar_ofReal]; simp

theorem contDiffAt_dbar {m n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f z) (h : m + 1 ≤ n) :
    ContDiffAt ℝ m (dbar f) z :=
  (antilinPartCLM E F).contDiff.contDiffAt.comp z (hf.fderiv_right h)

theorem contDiffAt_del {m n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f z) (h : m + 1 ≤ n) :
    ContDiffAt ℝ m (del f) z :=
  (linPartCLM E F).contDiff.contDiffAt.comp z (hf.fderiv_right h)

end FirstOrder

section SecondOrder

variable {u u' : E → F} {z : E}

theorem differentiableAt_fderiv_of_contDiffAt_two (hu : ContDiffAt ℝ 2 u z) :
    DifferentiableAt ℝ (fderiv ℝ u) z :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

theorem eventually_differentiableAt_of_contDiffAt_two {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (hu : ContDiffAt 𝕜 2 u z) :
    ∀ᶠ x in 𝓝 z, DifferentiableAt 𝕜 u x :=
  (hu.eventually (by simp)).mono fun _ hx => hx.differentiableAt two_ne_zero

theorem differentiableAt_dbar (hu : ContDiffAt ℝ 2 u z) : DifferentiableAt ℝ (dbar u) z :=
  (contDiffAt_dbar (m := 1) hu (by norm_num)).differentiableAt one_ne_zero

theorem differentiableAt_dbar_apply (hu : ContDiffAt ℝ 2 u z) (w : E) :
    DifferentiableAt ℝ (fun x => dbar u x w) z := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  simp only [dbar_apply]
  exact ((h.clm_apply (differentiableAt_const _)).add
    ((h.clm_apply (differentiableAt_const _)).const_smul I)).const_smul (1 / 2 : ℂ)

theorem ddbar_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    ddbar u z v w = (1 / 4 : ℂ) • (fderiv ℝ (fderiv ℝ u) z v w
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • w) + I • fderiv ℝ (fderiv ℝ u) z v (I • w)
      - I • fderiv ℝ (fderiv ℝ u) z (I • v) w) := by
  have h : HasFDerivAt (dbar u) _ z := (antilinPartCLM E F).hasFDerivAt.comp z
    (differentiableAt_fderiv_of_contDiffAt_two hu).hasFDerivAt
  rw [ddbar, del_apply, h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, antilinPartCLM_apply, antilinPart_apply]
  match_scalars
  · ring
  · ring
  · ring
  · linear_combination (-1 / 4) * I_mul_I

theorem fderiv_fderiv_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    fderiv ℝ (fun x => fderiv ℝ u x w) z v = fderiv ℝ (fderiv ℝ u) z v w := by
  rw [fderiv_clm_apply (differentiableAt_fderiv_of_contDiffAt_two hu) (differentiableAt_const _)]
  simp

theorem ddbar_eq_del_dbar (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    ddbar u z v w = del (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  rw [ddbar_apply hu]
  simp only [dbar_apply]
  rw [del_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul I)),
    del_add (h1 _) ((h1 _).fun_const_smul I),
    del_const_smul _ (h1 _)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, del_apply,
    fderiv_fderiv_apply hu]
  match_scalars
  · ring
  · linear_combination (1 / 4) * I_mul_I
  · ring
  · ring

theorem ddbar_eq_dbar_del (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    ddbar u z v w = dbar (fun x => del u x v) z w := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  rw [ddbar_apply hu]
  simp only [del_apply]
  rw [dbar_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul I)),
    dbar_sub (h1 _) ((h1 _).fun_const_smul I),
    dbar_const_smul _ (h1 _)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, dbar_apply,
    fderiv_fderiv_apply hu]
  rw [hs.eq w, hs.eq w, hs.eq (I • w), hs.eq (I • w)]
  match_scalars
  · ring
  · linear_combination (1 / 4) * I_mul_I
  · ring
  · ring

theorem ddbar_apply_self (hu : ContDiffAt ℝ 2 u z) (v : E) :
    ddbar u z v v = (1 / 4 : ℂ) • (fderiv ℝ (fderiv ℝ u) z v v
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • v)) := by
  rw [ddbar_apply hu, (hu.isSymmSndFDerivAt (by simp)).eq v (I • v), add_sub_cancel_right]

theorem ddbar_congr (h : u =ᶠ[𝓝 z] u') : ddbar u z = ddbar u' z :=
  del_congr (h.eventuallyEq_nhds.mono fun _ hx => dbar_congr hx)

@[simp] theorem ddbar_const (c : F) (z : E) : ddbar (fun _ => c) z = 0 := by
  have : dbar (fun _ : E => c) = fun _ => 0 := funext fun x => dbar_const c x
  rw [ddbar, this, del_const]

theorem ddbar_add (hu : ContDiffAt ℝ 2 u z) (hu' : ContDiffAt ℝ 2 u' z) :
    ddbar (fun x => u x + u' x) z = ddbar u z + ddbar u' z := by
  rw [ddbar, ddbar, ddbar, ← del_add (differentiableAt_dbar hu) (differentiableAt_dbar hu')]
  refine del_congr ?_
  filter_upwards [eventually_differentiableAt_of_contDiffAt_two hu,
    eventually_differentiableAt_of_contDiffAt_two hu'] with x h1 h2 using dbar_add h1 h2

theorem ddbar_const_smul (c : ℂ) (hu : ContDiffAt ℝ 2 u z) :
    ddbar (fun x => c • u x) z = c • ddbar u z := by
  rw [ddbar, ddbar, ← del_const_smul c (differentiableAt_dbar hu)]
  refine del_congr ?_
  filter_upwards [eventually_differentiableAt_of_contDiffAt_two hu] with x h1
    using dbar_const_smul c h1

theorem ddbar_neg (u : E → F) (z : E) : ddbar (fun x => -u x) z = -ddbar u z := by
  have : dbar (fun x : E => -u x) = fun x => -dbar u x := funext fun x => dbar_neg u x
  rw [ddbar, this, del_neg, ddbar]

theorem ddbar_sub (hu : ContDiffAt ℝ 2 u z) (hu' : ContDiffAt ℝ 2 u' z) :
    ddbar (fun x => u x - u' x) z = ddbar u z - ddbar u' z := by
  simp only [sub_eq_add_neg]
  rw [ddbar_add hu hu'.neg, ddbar_neg]

theorem ddbar_sum {ι : Type*} {t : Finset ι} {A : ι → E → F}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    ddbar (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, ddbar (A i) z := by
  simp only [ddbar]
  rw [← del_sum fun i hi => differentiableAt_dbar (h i hi)]
  refine del_congr ?_
  filter_upwards [(Finset.eventually_all t).2
    fun i hi => eventually_differentiableAt_of_contDiffAt_two (h i hi)] with x h1
    using dbar_sum h1

theorem ddbar_eq_zero_of_holomorphic (hu : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ u x) :
    ddbar u z = 0 := by
  rw [ddbar, ← del_const (0 : E →L⋆[ℂ] F) z]
  exact del_congr (hu.mono fun _ hx => dbar_eq_zero hx)

theorem ddbar_conj {a : E → ℂ} (ha : ContDiffAt ℝ 2 a z) (v w : E) :
    ddbar (fun x => conj (a x)) z v w = conj (ddbar a z w v) := by
  have ha' : ContDiffAt ℝ 2 (fun x => conj (a x)) z := conjCLE.contDiff.contDiffAt.comp z ha
  rw [ddbar_eq_del_dbar ha', ddbar_eq_dbar_del ha, ← del_conj]
  simp only [dbar_conj]

theorem ddbar_comp_holo {u : F → G} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    ddbar (fun x => u (φ x)) z v w = ddbar u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) := by
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrict_scalars ℝ
  have hφ1 : DifferentiableAt ℂ φ z := hφ.differentiableAt two_ne_zero
  have hc : ContDiffAt ℝ 2 (fun x => u (φ x)) z := hu.comp z hφR
  rw [ddbar_eq_del_dbar hc]
  have he : (fun x => dbar (fun x => u (φ x)) x w) =ᶠ[𝓝 z]
      fun x => antilinPart (fderiv ℝ u (φ x)) (fderiv ℂ φ x w) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hφ,
      hφ.continuousAt.eventually (eventually_differentiableAt_of_contDiffAt_two hu)] with x h1 h2
    exact dbar_comp_holo h2 h1 w
  have hψ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x w) z :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have hA : HasFDerivAt (fun x => fderiv ℝ u (φ x)) _ z :=
    (differentiableAt_fderiv_of_contDiffAt_two hu).hasFDerivAt.comp z
      (hφ1.hasFDerivAt.restrictScalars ℝ)
  have hψ' := hψ.hasFDerivAt.restrictScalars ℝ
  have h1 := hA.clm_apply hψ'
  have h2 := hA.clm_apply (hψ'.const_smul I)
  have h3 := (h1.add (h2.const_smul I)).const_smul (1 / 2 : ℂ)
  rw [del_congr he, ddbar_apply hu]
  simp only [antilinPart_apply]
  erw [del_eq_of_hasFDerivAt h3]
  simp only [linPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, I_smul_I_smul, map_neg, Pi.smul_apply]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_sq]; ring1)

end SecondOrder

section Levi

variable {u u' : E → ℝ} {z : E}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem contDiffAt_ofReal_comp {n : WithTop ℕ∞} (hu : ContDiffAt ℝ n u z) :
    ContDiffAt ℝ n (fun x => (u x : ℂ)) z := ofRealCLM.contDiff.contDiffAt.comp z hu

theorem leviForm_eq_del_dbar (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    leviForm u z v w = del (fun x => dbar (fun y => (u y : ℂ)) x w) z v :=
  ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu) v w

theorem fderiv_fderiv_ofReal_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    fderiv ℝ (fderiv ℝ fun x => (u x : ℂ)) z v w = (fderiv ℝ (fderiv ℝ u) z v w : ℂ) := by
  have h := differentiableAt_fderiv_of_contDiffAt_two (F := ℂ) (contDiffAt_ofReal_comp hu)
  have h' : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ (fun x => fderiv ℝ u x w) z := h'.clm_apply (differentiableAt_const _)
  have he : (fun x => fderiv ℝ (fun x => (u x : ℂ)) x w) =ᶠ[𝓝 z]
      fun x => ((fderiv ℝ u x w : ℝ) : ℂ) :=
    (hu.eventually (by simp)).mono fun _ hx => fderiv_ofReal_apply (hx.differentiableAt two_ne_zero) w
  rw [← fderiv_fderiv_apply (contDiffAt_ofReal_comp hu), he.fderiv_eq, fderiv_ofReal_apply h1,
    fderiv_clm_apply h' (differentiableAt_const _)]
  simp

theorem leviForm_apply (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    leviForm u z v w = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z v w
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • w) + I * fderiv ℝ (fderiv ℝ u) z v (I • w)
      - I * fderiv ℝ (fderiv ℝ u) z (I • v) w) := by
  rw [leviForm, ddbar_apply (contDiffAt_ofReal_comp hu)]
  simp only [fderiv_fderiv_ofReal_apply hu, smul_eq_mul]

theorem leviForm_apply_self (hu : ContDiffAt ℝ 2 u z) (v : E) :
    leviForm u z v v = ((1 / 4 * (fderiv ℝ (fderiv ℝ u) z v v
      + fderiv ℝ (fderiv ℝ u) z (I • v) (I • v)) : ℝ) : ℂ) := by
  rw [leviForm, ddbar_apply_self (contDiffAt_ofReal_comp hu)]
  simp only [fderiv_fderiv_ofReal_apply hu, smul_eq_mul]
  push_cast; ring

theorem leviForm_conj_symm (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    conj (leviForm u z v w) = leviForm u z w v := by
  rw [leviForm, ← ddbar_conj (contDiffAt_ofReal_comp hu)]
  simp only [conj_ofReal]

theorem im_leviForm_apply_self (hu : ContDiffAt ℝ 2 u z) (v : E) : (leviForm u z v v).im = 0 := by
  rw [leviForm_apply_self hu, ofReal_im]

theorem leviForm_congr (h : u =ᶠ[𝓝 z] u') : leviForm u z = leviForm u' z :=
  ddbar_congr (h.mono fun _ hx => by simp only [hx])

@[simp] theorem leviForm_const (c : ℝ) (z : E) : leviForm (fun _ => c) z = 0 := ddbar_const _ _

theorem leviForm_add (hu : ContDiffAt ℝ 2 u z) (hu' : ContDiffAt ℝ 2 u' z) :
    leviForm (fun x => u x + u' x) z = leviForm u z + leviForm u' z := by
  simp only [leviForm, ofReal_add]
  exact ddbar_add (contDiffAt_ofReal_comp hu) (contDiffAt_ofReal_comp hu')

theorem leviForm_sub (hu : ContDiffAt ℝ 2 u z) (hu' : ContDiffAt ℝ 2 u' z) :
    leviForm (fun x => u x - u' x) z = leviForm u z - leviForm u' z := by
  simp only [leviForm, ofReal_sub]
  exact ddbar_sub (contDiffAt_ofReal_comp hu) (contDiffAt_ofReal_comp hu')

theorem leviForm_neg (u : E → ℝ) (z : E) : leviForm (fun x => -u x) z = -leviForm u z := by
  simp only [leviForm, ofReal_neg]
  exact ddbar_neg _ _

theorem leviForm_const_mul (c : ℝ) (hu : ContDiffAt ℝ 2 u z) :
    leviForm (fun x => c * u x) z = (c : ℂ) • leviForm u z := by
  simp only [leviForm, ofReal_mul]
  exact ddbar_const_smul (c : ℂ) (contDiffAt_ofReal_comp hu)

theorem leviForm_add_const (c : ℝ) (hu : ContDiffAt ℝ 2 u z) :
    leviForm (fun x => u x + c) z = leviForm u z := by
  rw [leviForm_add hu contDiffAt_const, leviForm_const, add_zero]

theorem leviForm_sum {ι : Type*} {t : Finset ι} {A : ι → E → ℝ}
    (h : ∀ i ∈ t, ContDiffAt ℝ 2 (A i) z) :
    leviForm (fun x => ∑ i ∈ t, A i x) z = ∑ i ∈ t, leviForm (A i) z := by
  simp only [leviForm, ofReal_sum]
  exact ddbar_sum fun i hi => contDiffAt_ofReal_comp (h i hi)

theorem leviForm_comp_holo {u : F → ℝ} {φ : E → F} (hu : ContDiffAt ℝ 2 u (φ z))
    (hφ : ContDiffAt ℂ 2 φ z) (v w : E) :
    leviForm (fun x => u (φ x)) z v w = leviForm u (φ z) (fderiv ℂ φ z v) (fderiv ℂ φ z w) :=
  ddbar_comp_holo (u := fun y => (u y : ℂ)) (contDiffAt_ofReal_comp hu) hφ v w

theorem leviForm_re_eq_zero {f : E → ℂ} (hf : ContDiffAt ℂ 2 f z) :
    leviForm (fun x => (f x).re) z = 0 := by
  have hR : ContDiffAt ℝ 2 f z := hf.restrict_scalars ℝ
  have hc : ContDiffAt ℝ 2 (fun x => conj (f x)) z := conjCLE.contDiff.contDiffAt.comp z hR
  have h0 := ddbar_eq_zero_of_holomorphic (eventually_differentiableAt_of_contDiffAt_two hf)
  have : (fun x => ((f x).re : ℂ)) = fun x => (1 / 2 : ℂ) • (f x + conj (f x)) := by
    funext x; rw [add_conj]; simp
  rw [leviForm, this, ddbar_const_smul _ (hR.add hc), ddbar_add hR hc]
  ext v w
  simp [ddbar_conj hR, h0]

theorem leviForm_real_comp {t : E → ℝ} {h : ℝ → ℝ} (hh : ContDiffAt ℝ 2 h (t z))
    (ht : ContDiffAt ℝ 2 t z) (v w : E) :
    leviForm (fun x => h (t x)) z v w = ((deriv h (t z) : ℝ) : ℂ) * leviForm t z v w
      + ((deriv (deriv h) (t z) : ℝ) : ℂ) *
        (del (fun x => (t x : ℂ)) z v * dbar (fun x => (t x : ℂ)) z w) := by
  have hc : ContDiffAt ℝ 2 (fun x => h (t x)) z := hh.comp z ht
  have ht1 : DifferentiableAt ℝ t z := ht.differentiableAt two_ne_zero
  have he : (fun x => dbar (fun y => (h (t y) : ℂ)) x w) =ᶠ[𝓝 z]
      fun x => ((deriv h (t x) : ℝ) : ℂ) * dbar (fun y => (t y : ℂ)) x w := by
    filter_upwards [ht.eventually (by simp),
      ht.continuousAt.eventually (hh.eventually (by simp))] with x h1 h2
    exact dbar_ofReal_comp (h2.differentiableAt two_ne_zero).hasDerivAt
      (h1.differentiableAt two_ne_zero) w
  have hd : DifferentiableAt ℝ (deriv h) (t z) := by
    have := ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const (1 : ℝ))
    simpa only [fderiv_apply_one_eq_deriv] using this
  have hd' : DifferentiableAt ℝ (fun x => ((deriv h (t x) : ℝ) : ℂ)) z :=
    ofRealCLM.differentiableAt.comp z (hd.comp z ht1)
  rw [leviForm_eq_del_dbar hc, del_congr he,
    del_mul hd' (differentiableAt_dbar_apply (contDiffAt_ofReal_comp ht) w),
    del_ofReal_comp hd.hasDerivAt ht1, leviForm_eq_del_dbar ht, mul_assoc]

def leviMatrix {ι : Type*} (u : E → ℝ) (z : E) (b : ι → E) : Matrix ι ι ℂ :=
  Matrix.of fun i j => leviForm u z (b i) (b j)

@[simp] theorem leviMatrix_apply {ι : Type*} (u : E → ℝ) (z : E) (b : ι → E) (i j : ι) :
    leviMatrix u z b i j = leviForm u z (b i) (b j) := rfl

theorem leviMatrix_isHermitian {ι : Type*} (hu : ContDiffAt ℝ 2 u z) (b : ι → E) :
    (leviMatrix u z b).IsHermitian := by
  ext i j
  exact leviForm_conj_symm hu _ _

end Levi

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]

omit [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H] in

theorem inner_self_eq_ofReal_norm_sq (v : H) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; simp

theorem fderiv_normSq_apply (z v : H) :
    fderiv ℝ (fun x : H => ((‖x‖ ^ 2 : ℝ) : ℂ)) z v = inner ℂ z v + inner ℂ v z := by
  have : (fun x : H => ((‖x‖ ^ 2 : ℝ) : ℂ)) = fun x => inner ℂ x x := by
    funext x; rw [inner_self_eq_ofReal_norm_sq]
  rw [this, fderiv_inner_apply ℂ differentiableAt_fun_id differentiableAt_fun_id]
  simp

theorem del_normSq (z v : H) : del (fun x : H => ((‖x‖ ^ 2 : ℝ) : ℂ)) z v = inner ℂ z v := by
  rw [del_apply, fderiv_normSq_apply, fderiv_normSq_apply, inner_smul_left, inner_smul_right]
  simp only [conj_I, smul_eq_mul]
  linear_combination (inner ℂ v z / 2 - inner ℂ z v / 2) * I_mul_I

theorem dbar_normSq (z w : H) : dbar (fun x : H => ((‖x‖ ^ 2 : ℝ) : ℂ)) z w = inner ℂ w z := by
  rw [dbar_ofReal, del_normSq, inner_conj_symm]

theorem leviForm_normSq (z v w : H) : leviForm (fun x : H => ‖x‖ ^ 2) z v w = inner ℂ w v := by
  rw [leviForm_eq_del_dbar (contDiff_norm_sq ℂ).contDiffAt]
  simp only [dbar_normSq]
  have h : HasFDerivAt (fun x : H => inner ℂ w x) (innerSL ℂ w) z := (innerSL ℂ w).hasFDerivAt
  rw [del_eq_fderiv h.differentiableAt, h.fderiv, innerSL_apply_apply]

theorem leviForm_comp_normSq {h : ℝ → ℝ} {z : H} (hh : ContDiffAt ℝ 2 h (‖z‖ ^ 2)) (v w : H) :
    leviForm (fun x : H => h (‖x‖ ^ 2)) z v w = ((deriv h (‖z‖ ^ 2) : ℝ) : ℂ) * inner ℂ w v
      + ((deriv (deriv h) (‖z‖ ^ 2) : ℝ) : ℂ) * (inner ℂ z v * inner ℂ w z) := by
  rw [leviForm_real_comp (t := fun x : H => ‖x‖ ^ 2) hh (contDiff_norm_sq ℂ).contDiffAt,
    leviForm_normSq, del_normSq, dbar_normSq]

theorem deriv_log_add_const (δ : ℝ) : deriv (fun t : ℝ => Real.log (t + δ)) = fun t => (t + δ)⁻¹ := by
  funext t
  rw [deriv_comp_add_const Real.log δ t, Real.deriv_log]

theorem deriv_deriv_log_add_const (δ t : ℝ) :
    deriv (deriv fun t : ℝ => Real.log (t + δ)) t = -((t + δ) ^ 2)⁻¹ := by
  rw [deriv_log_add_const, deriv_comp_add_const (fun x : ℝ => x⁻¹) δ t, deriv_inv]

theorem leviForm_log_normSq_add {δ : ℝ} {z : H} (hz : ‖z‖ ^ 2 + δ ≠ 0) (v w : H) :
    leviForm (fun x : H => Real.log (‖x‖ ^ 2 + δ)) z v w =
      inner ℂ w v / ((‖z‖ ^ 2 + δ : ℝ) : ℂ)
        - inner ℂ z v * inner ℂ w z / ((‖z‖ ^ 2 + δ : ℝ) : ℂ) ^ 2 := by
  rw [leviForm_comp_normSq (h := fun t => Real.log (t + δ))
    ((contDiffAt_id.add contDiffAt_const).log hz), deriv_deriv_log_add_const, deriv_log_add_const]
  push_cast; ring

variable {φ : E → H} {z : E}

theorem contDiffAt_log_normSq_add_comp {δ : ℝ} (hφ : ContDiffAt ℂ 2 φ z)
    (hz : ‖φ z‖ ^ 2 + δ ≠ 0) : ContDiffAt ℝ 2 (fun x => Real.log (‖φ x‖ ^ 2 + δ)) z :=
  (((hφ.restrict_scalars ℝ).norm_sq ℂ).add contDiffAt_const).log hz

theorem leviForm_log_normSq_add_comp {δ : ℝ} (hφ : ContDiffAt ℂ 2 φ z)
    (hz : ‖φ z‖ ^ 2 + δ ≠ 0) (v w : E) :
    leviForm (fun x => Real.log (‖φ x‖ ^ 2 + δ)) z v w =
      inner ℂ (fderiv ℂ φ z w) (fderiv ℂ φ z v) / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ)
        - inner ℂ (φ z) (fderiv ℂ φ z v) * inner ℂ (fderiv ℂ φ z w) (φ z)
          / ((‖φ z‖ ^ 2 + δ : ℝ) : ℂ) ^ 2 := by
  rw [leviForm_comp_holo (u := fun y : H => Real.log (‖y‖ ^ 2 + δ))
    (((contDiff_norm_sq ℂ).contDiffAt.add contDiffAt_const).log hz) hφ,
    leviForm_log_normSq_add hz]

theorem leviForm_log_normSq_comp (hφ : ContDiffAt ℂ 2 φ z) (hz : φ z ≠ 0) (v w : E) :
    leviForm (fun x => Real.log (‖φ x‖ ^ 2)) z v w =
      inner ℂ (fderiv ℂ φ z w) (fderiv ℂ φ z v) / (‖φ z‖ : ℂ) ^ 2
        - inner ℂ (φ z) (fderiv ℂ φ z v) * inner ℂ (fderiv ℂ φ z w) (φ z) / (‖φ z‖ : ℂ) ^ 4 := by
  have := leviForm_log_normSq_add_comp (δ := 0) hφ (by simpa using hz) v w
  simp only [add_zero] at this
  rw [this]; push_cast; ring

theorem leviForm_log_normSq_eq_zero {f : E → ℂ} (hf : ContDiffAt ℂ 2 f z) (hz : f z ≠ 0) :
    leviForm (fun x => Real.log (‖f x‖ ^ 2)) z = 0 := by
  ext v w
  rw [leviForm_log_normSq_comp hf hz, ← conj_mul', show (‖f z‖ : ℂ) ^ 4 = (conj (f z) * f z) ^ 2 by
    rw [conj_mul']; ring]
  have : conj (f z) ≠ 0 := by simpa using hz
  simp only [inner, ContinuousLinearMap.zero_apply, star_def]
  field_simp
  ring

end Inner

section Psh

variable {u u' : E → ℝ} {s t : Set E}

theorem IsPshC2On.mono (h : IsPshC2On u t) (hst : s ⊆ t) : IsPshC2On u s :=
  fun z hz => h z (hst hz)

theorem IsPshC2On.contDiffAt (h : IsPshC2On u s) {z : E} (hz : z ∈ s) : ContDiffAt ℝ 2 u z :=
  (h z hz).1

theorem IsPshC2On.nonneg (h : IsPshC2On u s) {z : E} (hz : z ∈ s) (v : E) :
    0 ≤ (leviForm u z v v).re := (h z hz).2 v

theorem IsPshC2On.add (h : IsPshC2On u s) (h' : IsPshC2On u' s) :
    IsPshC2On (fun x => u x + u' x) s := fun z hz =>
  ⟨(h z hz).1.add (h' z hz).1, fun v => by
    rw [leviForm_add (h z hz).1 (h' z hz).1]
    exact add_nonneg ((h z hz).2 v) ((h' z hz).2 v)⟩

theorem IsPshC2On.const_mul (h : IsPshC2On u s) {c : ℝ} (hc : 0 ≤ c) :
    IsPshC2On (fun x => c * u x) s := fun z hz =>
  ⟨contDiffAt_const.mul (h z hz).1, fun v => by
    rw [leviForm_const_mul c (h z hz).1]
    simpa using mul_nonneg hc ((h z hz).2 v)⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]

theorem isPshC2On_normSq (s : Set H) : IsPshC2On (fun x : H => ‖x‖ ^ 2) s := fun z _ =>
  ⟨(contDiff_norm_sq ℂ).contDiffAt, fun v => by
    rw [leviForm_normSq, inner_self_eq_ofReal_norm_sq, ofReal_re]; positivity⟩

end Psh

section Circle

open Real MeasureTheory Set Metric

end Circle

open scoped Laplacian in

theorem leviForm_one_one_eq_laplacian {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    leviForm u z 1 1 = ((Δ u z / 4 : ℝ) : ℂ) := by
  rw [leviForm_apply_self hu, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]
  ring

example (z v : ℂ) : dbar (fun x : ℂ => conj x) z v = conj v ∧ del (fun x : ℂ => conj x) z v = 0 := by
  rw [dbar_conj (fun x => x), del_conj (fun x => x), del_eq_fderiv differentiableAt_fun_id,
    dbar_eq_zero differentiableAt_fun_id]
  simp

example (z : ℂ) : leviForm (fun x : ℂ => ‖x‖ ^ 2) z I 1 = I := by
  rw [leviForm_normSq]; simp

example (z : ℂ) : leviForm (fun x : ℂ => Real.log (‖x‖ ^ 2 + 1)) z 1 1 =
    1 / ((‖z‖ ^ 2 + 1 : ℝ) : ℂ) ^ 2 := by
  have h : ‖z‖ ^ 2 + 1 ≠ 0 := by positivity
  have h' : ((‖z‖ ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  rw [leviForm_log_normSq_add h]
  simp only [inner, star_def, map_one, one_mul, mul_one, conj_mul']
  field_simp
  push_cast
  ring

example (n : ℕ) (z : EuclideanSpace ℂ (Fin n)) :
    IsPshC2On (fun x : EuclideanSpace ℂ (Fin n) => ‖x‖ ^ 2) Set.univ ∧
    leviMatrix (fun x : EuclideanSpace ℂ (Fin n) => ‖x‖ ^ 2) z
      (fun i => EuclideanSpace.single i 1) = 1 := by
  refine ⟨isPshC2On_normSq _, ?_⟩
  ext i j
  simp [leviForm_normSq, Matrix.one_apply, EuclideanSpace.inner_single_left, eq_comm]

example : ¬ IsPshC2On (fun x : ℂ => -‖x‖ ^ 2) {0} := fun h => by
  have := h.nonneg rfl 1
  rw [leviForm_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply,
    leviForm_normSq] at this
  norm_num at this

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (z v w : V) :
    leviForm (fun x : V => ‖x‖ ^ 2) z v w = inner ℂ w v := leviForm_normSq z v w

example (n : ℕ) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) (hu : ContDiffAt ℝ 2 u z) :
    (leviMatrix u z fun i => Pi.single i 1).IsHermitian := leviMatrix_isHermitian hu _

end GlobalTheory
