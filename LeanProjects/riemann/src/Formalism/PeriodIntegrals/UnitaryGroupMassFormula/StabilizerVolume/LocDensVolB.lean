import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdDual

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem hform_single {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (Am : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) (x y : A) :
    Formalism.UG.hform s Am (Pi.single i x) (Pi.single j y) = s x * Am i j * y := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · simp
  · intro i' _ hi'
    simp [hi']
  · simp

def gG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) :
    Matrix (Fin a × Fin M × Fin d) (Fin a × Fin M × Fin d) F :=
  fun q q' => if q.1 = q'.1 then Algebra.trace F E (σ (b q.2.2) * J q.2.1 q'.2.1 * b q'.2.2) else 0

def cT {a M : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Fin a × Fin M × Fin d → Fv F v :=
  fun q => crd b (Fv F v) (Y q.1 q.2.1) q.2.2

variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem BR_eT (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q q' : Fin a × Fin M × Fin d) :
    BR (Fv F v) σ J (eT v b q) (eT v b q') = algebraMap F (Fv F v) (gG b σ J a q q') := by
  obtain ⟨p, i, k⟩ := q
  obtain ⟨p', j, l⟩ := q'
  simp only [BR, eT]
  rw [Finset.sum_eq_single p (fun p'' _ h => by simp [Pi.single_apply, h, hR, Formalism.UG.hform])
    (by simp)]
  simp only [Pi.single_eq_same, gG]
  by_cases hp : p = p'
  · subst hp
    simp only [Pi.single_eq_same, if_true, hR, hform_single, JR, Matrix.map_apply]
    have e : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) * inclR (Fv F v) (J i j) *
        ((1 : Fv F v) ⊗ₜ[F] b l) = (1 : Fv F v) ⊗ₜ[F] (σ (b k) * J i j * b l) := by
      simp [sigR, inclR, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, trace_one_tmul]
  · have hp' : p' ≠ p := fun h => hp h.symm
    simp [Pi.single_apply, hp, hR, Formalism.UG.hform]

theorem BR_eT_left (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q : Fin a × Fin M × Fin d) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (eT v b q) Y =
      ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  have h := congrFun (congrArg (phiL (a := a) v b σ J) (sum_eT v b Y)) q
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  change BR (Fv F v) σ J (eT v b q) Y = _
  have h2 : phiL (a := a) v b σ J Y q = BR (Fv F v) σ J (eT v b q) Y := rfl
  rw [← h2, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, cT]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h3 : phiL (a := a) v b σ J (eT v b q') q = BR (Fv F v) σ J (eT v b q) (eT v b q') := rfl
  rw [h3, BR_eT, mul_comm]

theorem BR_eq_sum (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q, cT b v X q * ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  rw [BR_expand v b σ J X Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [BR_eT_left]
  rfl

theorem cT_surj {a M : ℕ} (c : Fin a × Fin M × Fin d → Fv F v) :
    ∃ Y : Fin a → Fin M → Fv F v ⊗[F] E, cT b v Y = c := by
  refine ⟨fun p i => (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm
    (fun k => c (p, i, k)), ?_⟩
  funext q
  obtain ⟨p, i, k⟩ := q
  simp only [cT, crd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem mem_latV_iff {a M : ℕ} (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV (M := M) (n := a) b v ↔ ∀ q, cT b v Y q ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h q
    exact h q.1 q.2.1 q.2.2
  · intro h p i k
    exact h (p, i, k)

theorem mulVec_int {ι : Type} [Fintype ι] (A : Matrix ι ι F)
    (hA : ∀ i j, algebraMap F (Fv F v) (A i j) ∈ v.adicCompletionIntegers F)
    (w : ι → Fv F v) (hw : ∀ i, w i ∈ v.adicCompletionIntegers F) (i : ι) :
    (A.map (algebraMap F (Fv F v))).mulVec w i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hA i j) (hw j)

include v in

theorem det_gG [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) : (gG b σ J a).det ≠ 0 := by
  classical
  intro h0
  set G := (gG b σ J a).map (algebraMap F (Fv F v)) with hG
  have hdet : G.det = 0 := by
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨Y, hY⟩ := cT_surj b v (a := a) (M := M) w
  have hY0 : Y = 0 := by
    apply nondeg_BR v σ hσ J hJ Y
    intro X
    rw [BR_eq_sum, hY, hw]
    simp
  apply hw0
  rw [← hY, hY0]
  funext q
  simp [cT, crd]

theorem ev_dual [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) :
    ∀ᶠ v in cofinite, {Y | ∀ X ∈ latV (M := M) (n := a) b v,
      BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} = latV (M := M) (n := a) b v := by
  classical
  filter_upwards [ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      gG b σ J a q.1 q.2),
    ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      (gG b σ J a)⁻¹ q.1 q.2)] with v h1 h2
  have hdet := det_gG b v σ hσ J hJ (a := a)
  set g := gG b σ J a with hg
  ext Y
  constructor
  · intro hY
    rw [Set.mem_setOf_eq] at hY
    rw [mem_latV_iff]
    have hw : ∀ q, (g.map (algebraMap F (Fv F v))).mulVec (cT b v Y) q ∈
        v.adicCompletionIntegers F := by
      intro q
      rw [← BR_eT_left]
      exact hY _ (eT_mem v b q)
    have hinv : (g⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((g.map (algebraMap F (Fv F v))).mulVec (cT b v Y)) = cT b v Y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _)
        (map_one _), Matrix.one_mulVec]
    intro q
    rw [← hinv]
    exact mulVec_int v g⁻¹ (fun i j => h2 (i, j)) _ hw q
  · intro hY
    rw [Set.mem_setOf_eq]
    intro X hX
    rw [BR_eq_sum]
    rw [mem_latV_iff] at hX hY
    exact sum_mem fun q _ => mul_mem (hX q) (mulVec_int v g (fun i j => h1 (i, j)) _ hY q)

end VolAAW

end PI.VolStabS
