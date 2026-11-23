import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.KFinite

open NumberField IsDedekindDomain Matrix Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold ContDiff

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global

def archToReal (e : archGroup ℚ 2) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom ((archEquiv ℚ 2).symm e)

theorem archToReal_mul (e e' : archGroup ℚ 2) : archToReal (e * e') = archToReal e * archToReal e' := by
  simp only [archToReal, map_mul]

theorem infEmb_eq_realEmb (e : archGroup ℚ 2) : infEmb ℚ 2 e = realEmb (archToReal e) := by
  apply (prodEquiv ℚ 2).injective
  rw [prodEquiv_infEmb, prodEquiv_realEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) rfl
  exact (RationalIdeles.realEquiv.symm_apply_apply _).symm

theorem det_archToReal_expG_pos (X : archLie ℚ 2) :
    0 < (archToReal ((isExpLieAlgebra ℚ 2).expG X)).det.val := by
  have hX : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have hsq : (isExpLieAlgebra ℚ 2).expG X =
      (isExpLieAlgebra ℚ 2).expG ((1 / 2 : ℝ) • X) * (isExpLieAlgebra ℚ 2).expG ((1 / 2 : ℝ) • X) := by
    apply Subtype.ext
    apply Units.ext
    change NormedSpace.exp ((X : archLie ℚ 2) : ArchMatrix ℚ 2) = NormedSpace.exp _ * NormedSpace.exp _
    conv_lhs => rw [hX]
    exact exp_add_of_commute' ℝ (Commute.refl _)
  rw [hsq, archToReal_mul, map_mul, Units.val_mul]
  exact mul_self_pos.2 (Units.ne_zero _)

def archLin : ArchMatrix ℚ 2 →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  AddMonoidHom.toRealLinearMap
    { toFun := fun M i j => RationalIdeles.realEquiv ((archMatrixEquiv ℚ 2).symm M i j)
      map_zero' := by funext i j; simp
      map_add' := fun M M' => by funext i j; simp [Matrix.add_apply] }
    (continuous_pi fun i => continuous_pi fun j => RationalIdeles.continuous_realEquiv.comp
      ((continuous_apply j).comp ((continuous_apply i).comp (continuous_archMatrixEquiv_symm ℚ 2))))

def entryLift (k : ℤ) (F : ℂ → ℂ) (m : Fin 2 → Fin 2 → ℝ) : ℂ :=
  (Real.sqrt (m 0 0 * m 1 1 - m 0 1 * m 1 0) : ℂ) ^ k *
    F (((m 0 0 : ℂ) * Complex.I + m 0 1) * ((m 1 0 : ℂ) * Complex.I + m 1 1)⁻¹) *
      ((m 1 0 : ℂ) * Complex.I + m 1 1) ^ (-k)

theorem archLift_eq_entryLift (k : ℤ) (f : ℍ → ℂ) {x : GL (Fin 2) ℝ} (hx : 0 < x.det.val) :
    archLift k f x = entryLift k (f ∘ ofComplex) (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [archLift]
  unfold entryLift
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Function.comp_apply,
    ← div_eq_mul_inv]
  have h1 : ((x • UpperHalfPlane.I : ℍ) : ℂ) =
      ((x : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * Complex.I + (x : Matrix (Fin 2) (Fin 2) ℝ) 0 1) /
        ((x : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I + (x : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
    rw [coe_smul_of_det_pos hx, num, denom, coe_I]
  rw [← h1, ofComplex_apply]
  simp only [denom, coe_I]

theorem contDiffAt_entryLift (k : ℤ) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    {m : Fin 2 → Fin 2 → ℝ} (hm : 0 < m 0 0 * m 1 1 - m 0 1 * m 1 0) :
    ContDiffAt ℝ ∞ (entryLift k F) m := by
  have hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun m : Fin 2 → Fin 2 → ℝ => m i j) := fun i j =>
    contDiff_apply_apply ℝ ℝ i j
  have hcC : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun m : Fin 2 → Fin 2 → ℝ => ((m i j : ℝ) : ℂ)) := fun i j =>
    Complex.ofRealCLM.contDiff.comp (hc i j)
  set D : (Fin 2 → Fin 2 → ℝ) → ℝ := fun m => m 0 0 * m 1 1 - m 0 1 * m 1 0
  have hD : ContDiff ℝ ∞ D := ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  set den : (Fin 2 → Fin 2 → ℝ) → ℂ := fun m => (m 1 0 : ℂ) * Complex.I + m 1 1
  set num : (Fin 2 → Fin 2 → ℝ) → ℂ := fun m => (m 0 0 : ℂ) * Complex.I + m 0 1
  have hden : ContDiff ℝ ∞ den := ((hcC 1 0).mul contDiff_const).add (hcC 1 1)
  have hnum : ContDiff ℝ ∞ num := ((hcC 0 0).mul contDiff_const).add (hcC 0 1)
  have hden0 : den m ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [den] at h1 h2
    rw [h1, h2] at hm
    simp at hm
  have hq : 0 < (num m * (den m)⁻¹).im := by
    rw [← div_eq_mul_inv, Complex.div_im]
    have hns : 0 < Complex.normSq (den m) := Complex.normSq_pos.2 hden0
    simp only [num, den, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [← sub_div]
    apply div_pos _ hns
    nlinarith

  have h1 : ContDiffAt ℝ ∞ (fun m : Fin 2 → Fin 2 → ℝ => (Real.sqrt (D m) : ℂ) ^ k) m := by
    have hs : ContDiffAt ℝ ∞ (fun m => (Real.sqrt (D m) : ℂ)) m :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp m ((Real.contDiffAt_sqrt hm.ne').comp m hD.contDiffAt)
    have hs0 : (Real.sqrt (D m) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hm).ne'
    have hz : ContDiffAt ℝ ∞ (fun z : ℂ => z ^ k) (Real.sqrt (D m) : ℂ) :=
      (((differentiableOn_zpow k {0}ᶜ (Or.inl (by simp))).analyticOnNhd isOpen_compl_singleton _
        hs0).contDiffAt).restrict_scalars ℝ
    exact hz.comp m hs
  have h2 : ContDiffAt ℝ ∞ (fun m => F (num m * (den m)⁻¹)) m := by
    have hinv : ContDiffAt ℝ ∞ (fun m => (den m)⁻¹) m := (contDiffAt_inv ℝ hden0).comp m hden.contDiffAt
    have hqd : ContDiffAt ℝ ∞ (fun m => num m * (den m)⁻¹) m := hnum.contDiffAt.mul hinv
    have hFd : ContDiffAt ℝ ∞ F (num m * (den m)⁻¹) :=
      ((hF.contDiffOn (isOpen_lt continuous_const Complex.continuous_im)).contDiffAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hq)).restrict_scalars ℝ
    exact hFd.comp m hqd
  have h3 : ContDiffAt ℝ ∞ (fun m => den m ^ (-k)) m := by
    have hz : ContDiffAt ℝ ∞ (fun z : ℂ => z ^ (-k)) (den m) :=
      (((differentiableOn_zpow (-k) {0}ᶜ (Or.inl (by simp))).analyticOnNhd isOpen_compl_singleton _
        hden0).contDiffAt).restrict_scalars ℝ
    exact hz.comp m hden.contDiffAt
  exact (h1.mul h2).mul h3

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem isArchSmooth_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f) :
    IsArchSmooth (adelicLift N k f) := by
  intro g
  rw [(isExpLieAlgebra ℚ 2).isSmoothFun_iff]
  intro x
  set g' := g * infEmb ℚ 2 x
  obtain ⟨hpos, γ, u, hu, hg'⟩ := decompGL_spec N g'
  set h := decompGL N g'
  set P : archLie ℚ 2 → (Fin 2 → Fin 2 → ℝ) := fun Y i j =>
    ∑ a, (h : Matrix (Fin 2) (Fin 2) ℝ) i a * archLin (NormedSpace.exp ((Y : ArchMatrix ℚ 2))) a j
  have hP : ContDiff ℝ ∞ P := by
    have hE : ContDiff ℝ ∞ (fun Y : archLie ℚ 2 => archLin (NormedSpace.exp ((Y : ArchMatrix ℚ 2)))) :=
      archLin.contDiff.comp ((contDiff_exp ℝ (ArchMatrix ℚ 2)).comp (archLie ℚ 2).subtypeL.contDiff)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    exact ContDiff.sum fun a _ => contDiff_const.mul
      ((contDiff_apply_apply ℝ ℝ a j).comp hE)
  have hPval : ∀ Y : archLie ℚ 2, P Y =
      ((h * archToReal ((isExpLieAlgebra ℚ 2).expG Y) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro Y
    funext i j
    rw [Units.val_mul, Matrix.mul_apply]
    rfl
  have hdet : ∀ Y : archLie ℚ 2, 0 < (h * archToReal ((isExpLieAlgebra ℚ 2).expG Y)).det.val := by
    intro Y
    rw [map_mul, Units.val_mul]
    exact mul_pos hpos (det_archToReal_expG_pos Y)
  have hval : ∀ Y : archLie ℚ 2,
      archSlice (adelicLift N k f) g (x * (isExpLieAlgebra ℚ 2).expG Y) =
        entryLift k (f ∘ ofComplex) (P Y) := by
    intro Y
    rw [archSlice_apply, map_mul, ← mul_assoc, show g * infEmb ℚ 2 x = g' from rfl, hg',
      infEmb_eq_realEmb, mul_assoc _ _ (realEmb _),
      ← realEmb_mul_finEmb_comm, ← mul_assoc, mul_assoc (diagonal ℚ 2 γ), ← map_mul,
      adelicLift_apply hf γ (hdet Y) hu, archLift_eq_entryLift k f (hdet Y), hPval]
  have hF : DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} := mdifferentiable_iff.1 hhol
  rw [show (fun Y : archLie ℚ 2 => archSlice (adelicLift N k f) g (x * (isExpLieAlgebra ℚ 2).expG Y)) =
      entryLift k (f ∘ ofComplex) ∘ P from funext hval]
  refine contDiff_iff_contDiffAt.2 fun Y => (contDiffAt_entryLift k hF ?_).comp Y hP.contDiffAt
  have := hdet Y
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ← hPval] at this
  exact this

theorem isSmooth_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f) :
    IsSmooth (adelicLift N k f) :=
  ⟨isArchSmooth_adelicLift hf hhol, (isWeightLevel_adelicLift hf).eventually_finEmb⟩

end GL2Classical

end

end GroundTheory.Automorphic
