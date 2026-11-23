import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHaar

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisForm (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    LinearMap.BilinForm ℝ (heisY h v x₀ w₀) :=
  LinearMap.mk₂ ℝ (fun y z => ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re)
    (fun y y' z => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_left, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_left,
        Complex.conj_ofReal, Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])
    (fun y z z' => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_right, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_right,
        Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem heisForm_apply (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re := rfl

theorem heisForm_comm (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hH, -⟩ := hyperbolic_at_place h v hp w
  rw [← hForm_conj hH, Complex.conj_re]

theorem heisForm_nondegenerate (hp : IsHyperbolicPair h x₀ w₀) :
    (heisForm h v x₀ w₀).Nondegenerate := by
  classical
  have left : ∀ y : heisY h v x₀ w₀, (∀ z, heisForm h v x₀ w₀ y z = 0) → y = 0 := by
    intro y hy
    apply Subtype.ext
    funext w
    change (y : InfinitePlace E → ι → ℂ) w = 0
    obtain ⟨hH, hd, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
    have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
      rw [← hForm_conj hH, hab, map_one]
    apply eq_zero_of_hForm hd
    intro z
    set q := z - hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w -
      hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w with hq
    have hqa : hForm (gramAt h v w) (vecAt v x₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, ha, hab]
      ring
    have hqb : hForm (gramAt h v w) (vecAt v w₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, hb, hba]
      ring
    have key : ∀ c : ℂ, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (c • q)).re = 0 := by
      intro c
      have hmem : (Pi.single w (c • q) : InfinitePlace E → ι → ℂ) ∈ heisY h v x₀ w₀ := by
        intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [Pi.single_eq_same, hForm_smul_right, hqa, hqb, mul_zero, and_self]
        · simp only [Pi.single_eq_of_ne hw, hForm_zero_right, and_self]
      have := hy ⟨_, hmem⟩
      rw [heisForm_apply, Finset.sum_eq_single w] at this
      · simpa using this
      · intro w' _ hw
        simp [Pi.single_eq_of_ne hw, hForm_zero_right]
      · simp
    have h1 := key 1
    have h2 := key Complex.I
    rw [hForm_smul_right, one_mul] at h1
    rw [hForm_smul_right, Complex.I_mul_re, neg_eq_zero] at h2
    have hyq : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) q = 0 := Complex.ext h1 h2
    have hya : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v x₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).1, map_zero]
    have hyb : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).2, map_zero]
    have hz : z = q + hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w +
        hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w := by
      rw [hq]
      abel
    rw [hz, hForm_add_right, hForm_add_right, hForm_smul_right, hForm_smul_right, hyq, hya, hyb]
    ring
  exact ⟨left, fun y hy => left y fun z => by rw [heisForm_comm hp]; exact hy z⟩

theorem heisForm_heisConjLin (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heisConjLin_apply, heisConjLin_apply, hForm_mulVec_of_unitary _ (archUnitary_at_place g w)]

end Form

theorem UnipotentModulus.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentModulus.Statement h v := by
  intro x₀ w₀ hp μ _ g hg
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (unipRadical h v x₀ : Set (archUnitary h v))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set G := heisConjLin g hg with hG
  set c : unipRadical h v x₀ → unipRadical h v x₀ := fun n => φ ((G (φ.symm n).1, (φ.symm n).2))
    with hcdef
  have hc : ∀ n, ((c n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_conj hp g hg _).symm
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hcm : Measurable c :=
    (φ.continuous.comp ((hGc.comp (continuous_fst.comp φ.symm.continuous)).prodMk
      (continuous_snd.comp φ.symm.continuous))).measurable
  have hmap : (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) =
      Subtype.val ∘ c := by
    funext n
    exact (hc n).symm
  have hGm : MeasurePreserving G Measure.addHaar Measure.addHaar :=
    measurePreserving_of_preserves_bilin _ (heisForm h v x₀ w₀) (heisForm_nondegenerate hp) G
      (heisForm_heisConjLin g hg)
  have hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam := by
    have e : (fun x => φ.symm (c (φ x))) = Prod.map G id := by
      funext x
      simp only [hcdef, Homeomorph.symm_apply_apply, Prod.map, id]
    rw [e]
    exact hGm.prod (MeasurePreserving.id volume)
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  rw [hmap, ← Measure.map_map continuous_subtype_val.measurable hcm,
    map_eq_of_measurePreserving_coordinates lam φ hL c hC μ]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
