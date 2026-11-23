import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Adelic
import GroundTheory.AutomorphicForms.GL2Classical.Iwasawa
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} (k : ℤ)

theorem σ_of_det_pos {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℂ) : σ h z = z := by
  rw [σ, if_pos hpos]
  rfl

theorem denom_mul_of_det_pos (g : GL (Fin 2) ℝ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℍ) :
    denom (g * h) z = denom g ((h • z : ℍ) : ℂ) * denom h z := by
  rw [denom_cocycle_σ, σ_of_det_pos hpos]

theorem sqrt_div_normSq {a : ℝ} (w : ℂ) :
    Real.sqrt (a / Complex.normSq w) = Real.sqrt a / ‖w‖ := by
  rw [Real.sqrt_div' _ (Complex.normSq_nonneg w), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg w)]

theorem div_norm_zpow_neg (w : ℂ) : (w / (‖w‖ : ℂ)) ^ (-k) = w ^ (-k) * (‖w‖ : ℂ) ^ k := by
  rw [div_eq_mul_inv, mul_zpow, _root_.inv_zpow', neg_neg]

def archLift (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)

theorem apply_mapGL_smul {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) (z : ℍ) :
    f (Matrix.SpecialLinearGroup.mapGL ℝ s • z) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) (z : ℂ) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn'' (SlashInvariantForm.mk f hf) (Subgroup.mem_map_of_mem _ hs) z

theorem archLift_mapGL_mul {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    archLift k f (Matrix.SpecialLinearGroup.mapGL ℝ s * h) = archLift k f h := by
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ s * h).det.val = h.det.val := by
    rw [map_mul, Matrix.SpecialLinearGroup.det_mapGL, one_mul]
  have hne : denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hA : denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ^ k *
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hne, add_neg_cancel, zpow_zero]
  rw [archLift, archLift, hdet, mul_smul, apply_mapGL_smul k hf hs, denom_mul_of_det_pos _ hpos,
    mul_zpow]
  linear_combination ((Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)) * hA

theorem archLift_mul_kGL (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (w : ℂ)
    (hw : w ≠ 0) :
    archLift k f (h * kGL w hw) = (w / (‖w‖ : ℂ)) ^ (-k) * archLift k f h := by
  have hdet : (h * kGL w hw).det.val = h.det.val * Complex.normSq w := by
    rw [map_mul, Units.val_mul, det_kGL]
  have hsq : Real.sqrt (h.det.val * Complex.normSq w) = Real.sqrt h.det.val * ‖w‖ := by
    rw [Real.sqrt_mul hpos.le, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [archLift, archLift, hdet, hsq, mul_smul, kGL_smul_I, denom_mul_of_det_pos _ (det_kGL_pos w hw),
    kGL_smul_I, denom_kGL, div_norm_zpow_neg, Complex.ofReal_mul, mul_zpow, mul_zpow]
  ring

theorem archLift_add (f f' : ℍ → ℂ) (h : GL (Fin 2) ℝ) :
    archLift k (f + f') h = archLift k f h + archLift k f' h := by
  simp only [archLift, Pi.add_apply]
  ring

theorem archLift_smul (c : ℂ) (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) :
    archLift k (c • f) h = c * archLift k f h := by
  simp only [archLift, Pi.smul_apply, smul_eq_mul]
  ring

theorem archLift_borelGL (f : ℍ → ℂ) (z : ℍ) :
    archLift k f (borelGL z) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [archLift, det_borelGL, borelGL_smul_I, denom_borelGL, _root_.one_zpow, mul_one]

variable (N) [NeZero N]

def decompGL (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Classical.choose (Classical.choose_spec (exists_decomposition N g))

theorem decompGL_spec (g : AdelicGL ℚ 2) :
    0 < (decompGL N g).det.val ∧ ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb (decompGL N g) * finEmb ℚ 2 u :=
  ⟨(Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).1,
    Classical.choose (exists_decomposition N g),
    (Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).2⟩

def adelicLift (f : ℍ → ℂ) (g : AdelicGL ℚ 2) : ℂ :=
  archLift k f (decompGL N g)

variable {N k}

theorem archLift_eq_of_decomp {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ₁ γ₂ : GL (Fin 2) ℚ} {h₁ h₂ : GL (Fin 2) ℝ} {u₁ u₂ : FiniteAdelicGL ℚ 2}
    (hpos₁ : 0 < h₁.det.val) (hpos₂ : 0 < h₂.det.val) (hu₁ : u₁ ∈ Gamma0Level N)
    (hu₂ : u₂ ∈ Gamma0Level N)
    (heq : diagonal ℚ 2 γ₁ * realEmb h₁ * finEmb ℚ 2 u₁ =
      diagonal ℚ 2 γ₂ * realEmb h₂ * finEmb ℚ 2 u₂) :
    archLift k f h₁ = archLift k f h₂ := by
  have hc := congrArg (prodEquiv ℚ 2) heq
  simp only [map_mul, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one,
    one_mul, Prod.mk.injEq] at hc
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = γ₂⁻¹ * γ₁ := ⟨_, rfl⟩
  have hreal : toReal δ * h₁ = h₂ := realInf_injective (by
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.1, inv_mul_cancel_left])
  have hfin : finiteDiagonal ℚ 2 δ = u₂ * u₁⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.2, inv_mul_cancel_left]
  have hδ : finiteDiagonal ℚ 2 δ ∈ Gamma0Level N := hfin ▸ mul_mem hu₂ (inv_mem hu₁)
  have hdetδ : 0 < (δ.det.val : ℚ) := by
    have hprod : (toReal δ).det.val * h₁.det.val = h₂.det.val := by
      rw [← hreal, MonoidHom.map_mul Matrix.GeneralLinearGroup.det, Units.val_mul]
    rw [det_toReal] at hprod
    have hb : 0 < ((δ.det.val : ℚ) : ℝ) * h₁.det.val := hprod ▸ hpos₂
    have : (0 : ℝ) < ((δ.det.val : ℚ) : ℝ) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact_mod_cast this
  obtain ⟨s, hs, hsδ⟩ := exists_mem_Gamma0_of_mem N hδ hdetδ
  rw [← hreal, ← hsδ, toReal_mapGL]
  exact (archLift_mapGL_mul k hf hs hpos₁).symm

theorem adelicLift_apply {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (γ : GL (Fin 2) ℚ)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    adelicLift N k f (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u) = archLift k f h := by
  obtain ⟨hpos', γ', u', hu', heq⟩ := decompGL_spec N (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u)
  exact archLift_eq_of_decomp hf hpos' hpos hu' hu heq.symm

theorem adelicLift_realEmb {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    adelicLift N k f (realEmb h) = archLift k f h := by
  have := adelicLift_apply hf 1 hpos (one_mem (Gamma0Level N))
  rwa [map_one, map_one, one_mul, mul_one] at this

theorem adelicLift_borelGL {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (z : ℍ) :
    adelicLift N k f (realEmb (borelGL z)) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [adelicLift_realEmb hf (det_borelGL_pos z), archLift_borelGL]

variable (N k)

structure IsWeightLevel (φ : AdelicGL ℚ 2 → ℂ) : Prop where
  isLeftInvariant : IsLeftInvariant φ
  right_level : ∀ g, ∀ u ∈ Gamma0Level N, φ (g * finEmb ℚ 2 u) = φ g
  right_kGL : ∀ g (w : ℂ) (hw : w ≠ 0), φ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * φ g

def weightLevelSpace : Submodule ℂ (AdelicGL ℚ 2 → ℂ) where
  carrier := {φ | IsWeightLevel N k φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' {φ ψ} hφ hψ := ⟨hφ.isLeftInvariant.add hψ.isLeftInvariant,
    fun g u hu => by simp [hφ.right_level g u hu, hψ.right_level g u hu],
    fun g w hw => by simp [hφ.right_kGL g w hw, hψ.right_kGL g w hw, mul_add]⟩
  smul_mem' c φ hφ := ⟨hφ.isLeftInvariant.smul c,
    fun g u hu => by simp [hφ.right_level g u hu],
    fun g w hw => by simp [hφ.right_kGL g w hw]; ring⟩

variable {N k}

theorem IsWeightLevel.apply_decomp {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    φ (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u) = φ (realEmb h) := by
  rw [hφ.right_level _ u hu]
  exact hφ.isLeftInvariant γ _

theorem IsWeightLevel.apply_realEmb {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    φ (realEmb h) = (denom h (I : ℂ) / (‖denom h (I : ℂ)‖ : ℂ)) ^ (-k) *
      φ (realEmb (borelGL (h • I))) := by
  conv_lhs => rw [eq_borelGL_mul_kGL hpos, map_mul]
  exact hφ.right_kGL _ _ _

theorem isWeightLevel_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    IsWeightLevel N k (adelicLift N k f) where
  isLeftInvariant δ g := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    conv_lhs => rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul]
    rw [adelicLift_apply hf _ hpos hu]
    rfl
  right_level g v hv := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    conv_lhs => rw [hg, mul_assoc, ← map_mul]
    rw [adelicLift_apply hf _ hpos (mul_mem hu hv)]
    rfl
  right_kGL g w hw := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    have key : ∀ h : GL (Fin 2) ℝ, g = diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u →
        g * realEmb (kGL w hw) = diagonal ℚ 2 γ * realEmb (h * kGL w hw) * finEmb ℚ 2 u := by
      intro h hgh
      rw [hgh, map_mul, mul_assoc _ (finEmb ℚ 2 u), ← realEmb_mul_finEmb_comm, ← mul_assoc,
        mul_assoc (diagonal ℚ 2 γ)]
    have := key _ hg
    have hpos' : 0 < (decompGL N g * kGL w hw).det.val := by
      rw [map_mul, Units.val_mul]
      exact mul_pos hpos (det_kGL_pos w hw)
    rw [this, adelicLift_apply hf _ hpos' hu, archLift_mul_kGL k f hpos]
    rfl

variable (k)

def descend (φ : AdelicGL ℚ 2 → ℂ) (z : ℍ) : ℂ :=
  (Real.sqrt z.im : ℂ) ^ (-k) * φ (realEmb (borelGL z))

variable {k}

theorem descend_slash {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) : descend k φ ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s = descend k φ := by
  funext z
  set g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg1 : g.det.val = 1 := by rw [Matrix.SpecialLinearGroup.det_mapGL]; rfl
  have hgpos : 0 < g.det.val := by rw [hg1]; exact one_pos
  set j := denom g z
  have hj : j ≠ 0 := denom_ne_zero g z

  have hA : φ (realEmb (g * borelGL z)) = φ (realEmb (borelGL z)) := by
    have h1 := hφ.isLeftInvariant (Matrix.SpecialLinearGroup.mapGL ℚ s) (realEmb (borelGL z))
    rw [diagonal_eq, toReal_mapGL, mul_assoc, ← realEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul,
      hφ.right_level _ _ (finiteDiagonal_mapGL_mem_Gamma0Level N hs)] at h1
    exact h1

  have hpos : 0 < (g * borelGL z).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hgpos (det_borelGL_pos z)
  have hsmul : (g * borelGL z) • I = g • z := by rw [mul_smul, borelGL_smul_I]
  have hden : denom (g * borelGL z) (I : ℂ) = j := by
    rw [denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one]
  have hB : φ (realEmb (borelGL z)) =
      (j / (‖j‖ : ℂ)) ^ (-k) * φ (realEmb (borelGL (g • z))) := by
    rw [← hA, hφ.apply_realEmb hpos, hsmul, hden]
  have him : (g • z).im = z.im / Complex.normSq j := by
    rw [im_smul_eq_div_normSq, hg1, abs_one, one_mul]
  have hn : (‖j‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hj)
  have hnk : (‖j‖ : ℂ) ^ (-k) * (‖j‖ : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hn, neg_add_cancel, zpow_zero]
  rw [slash_apply, σ_of_det_pos hgpos, hg1, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one,
    descend, descend, him,
    sqrt_div_normSq, Complex.ofReal_div, div_zpow, hB, div_norm_zpow_neg, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right hnk]
  ring

theorem descend_slash_eq {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), descend k φ ∣[k] γ = descend k φ := by
  intro γ hγ
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
  exact descend_slash hφ hs

theorem descend_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    descend k (adelicLift N k f) = f := by
  funext z
  have hy : (Real.sqrt z.im : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 z.im_pos).ne'
  rw [descend, adelicLift_borelGL hf, ← mul_assoc, ← zpow_add₀ hy, neg_add_cancel, zpow_zero,
    one_mul]

theorem adelicLift_descend {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    adelicLift N k (descend k φ) = φ := by
  funext g
  obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
  set h := decompGL N g
  set j := denom h (I : ℂ)
  have hj : j ≠ 0 := denom_ne_zero h I
  have hn : (‖j‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hj)
  have hnk : (‖j‖ : ℂ) ^ (-k) * (‖j‖ : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hn, neg_add_cancel, zpow_zero]
  have hd : (Real.sqrt h.det.val : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hdk : (Real.sqrt h.det.val : ℂ) ^ k * (Real.sqrt h.det.val : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hd, add_neg_cancel, zpow_zero]
  have hφg : φ g = φ (realEmb h) := by
    conv_lhs => rw [hg]
    exact hφ.apply_decomp γ h hu
  change archLift k (descend k φ) h = φ g
  rw [hφg, hφ.apply_realEmb hpos, archLift, descend, im_smul_I hpos, sqrt_div_normSq,
    Complex.ofReal_div, div_zpow, div_norm_zpow_neg, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hnk]
  linear_combination ((‖j‖ : ℂ) ^ k * φ (realEmb (borelGL (h • I))) * j ^ (-k)) * hdk

variable (N k)

def liftEquiv :
    SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k ≃ₗ[ℂ] weightLevelSpace N k where
  toFun f := ⟨adelicLift N k f,
    isWeightLevel_adelicLift fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ⟩
  map_add' f f' := by
    ext g
    simp only [Submodule.coe_add, Pi.add_apply, adelicLift, FunLike.coe_add]
    exact archLift_add k f f' _
  map_smul' c f := by
    ext g
    simp only [Submodule.coe_smul, Pi.smul_apply, adelicLift, FunLike.coe_smul,
      RingHom.id_apply, smul_eq_mul]
    exact archLift_smul k c f _
  invFun φ := SlashInvariantForm.mk (descend k φ) (descend_slash_eq φ.2)
  left_inv f := SlashInvariantForm.ext fun z => congrFun
    (descend_adelicLift fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ) z
  right_inv φ := Subtype.ext (adelicLift_descend φ.2)

variable {N k}

@[simp]
theorem liftEquiv_apply (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) = adelicLift N k f :=
  rfl

@[simp]
theorem liftEquiv_symm_apply (φ : weightLevelSpace N k) (z : ℍ) :
    (liftEquiv N k).symm φ z = descend k φ z :=
  rfl

end GL2Classical

end

end GroundTheory.Automorphic
