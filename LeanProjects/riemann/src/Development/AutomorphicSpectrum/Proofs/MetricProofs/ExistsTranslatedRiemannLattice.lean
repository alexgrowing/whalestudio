import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.HeightsAndTheta.Theta.CMDatum

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

theorem restr_embOf (s : 𝓞 E →+* ℂ) : (embOf s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (embOf_coe s)

omit [IsCMField E] in
theorem hom_ext {φ ψ : E →+* ℂ} (h : φ.comp (algebraMap (𝓞 E) E) = ψ.comp (algebraMap (𝓞 E) E)) : φ = ψ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h

theorem embOf_restr (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ :=
  hom_ext (restr_embOf _)

theorem sum_embeddings_cm {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (f : (E →+* ℂ) → ℂ) :
    ∑ φ, f φ = ∑ τ, (f (embOf (σ τ)) + f ((starRingEnd ℂ).comp (embOf (σ τ)))) := by
  classical
  let m : Ψ × Bool → (E →+* ℂ) := fun p =>
    if p.2 then (starRingEnd ℂ).comp (embOf (σ p.1)) else embOf (σ p.1)
  have hc : ∀ s t : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp s = (starRingEnd ℂ).comp t → s = t := by
    intro s t h
    ext x
    have := congrArg (fun r : 𝓞 E →+* ℂ => starRingEnd ℂ (r x)) h
    simpa using this
  have hcc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext x
    simp
  have hr : ∀ τ, ((starRingEnd ℂ).comp (embOf (σ τ))).comp (algebraMap (𝓞 E) E) = (starRingEnd ℂ).comp (σ τ) := by
    intro τ
    rw [RingHom.comp_assoc, restr_embOf]
  have hm : Function.Bijective m := by
    constructor
    · rintro ⟨τ, b⟩ ⟨τ', b'⟩ h
      have h' := congrArg (fun r : E →+* ℂ => r.comp (algebraMap (𝓞 E) E)) h
      cases b <;> cases b' <;> simp only [m, Bool.false_eq_true, if_true, if_false, hr, restr_embOf] at h'
      · rw [hσ.1 h']
      · exact absurd ⟨τ, h'⟩ ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩)
      · exact absurd ⟨τ', h'.symm⟩ ((hσ.2 (σ τ)).1 ⟨τ, rfl⟩)
      · rw [hσ.1 (hc _ _ h')]
    · intro φ
      by_cases h : ∃ τ, σ τ = φ.comp (algebraMap (𝓞 E) E)
      · obtain ⟨τ, hτ⟩ := h
        refine ⟨(τ, false), ?_⟩
        simp only [m, Bool.false_eq_true, if_false, hτ, embOf_restr]
      · have h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp (φ.comp (algebraMap (𝓞 E) E)) := by
          by_contra h3
          exact h ((hσ.2 _).2 h3)
        obtain ⟨τ, hτ⟩ := h2
        refine ⟨(τ, true), ?_⟩
        simp only [m, if_true]
        apply hom_ext
        rw [hr, hτ, hcc]
  rw [← (Equiv.ofBijective m hm).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [m, Fintype.sum_bool, add_comm]

theorem trace_eq_sum_re {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ, 2 * (embOf (σ τ) z).re := by
  apply Complex.ofReal_injective
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  rw [eq_ratCast] at h
  have h2 : ∑ φ : E →ₐ[ℚ] ℂ, φ z = ∑ φ : E →+* ℂ, φ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun τ => rfl).symm
  rw [h2, sum_embeddings_cm hσ (fun φ => φ z)] at h
  push_cast
  rw [h]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [RingHom.comp_apply]
  rw [Complex.add_conj]
  push_cast
  ring

section Lat

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem emb_sesq (τ : Ψ) (w v : Fin (j + j') → E) :
    embOf (F.σ τ) (C.h.toSesq w v) =
      star (fun i => embOf (F.σ τ) (w i)) ⬝ᵥ (C.gr τ *ᵥ fun i => embOf (F.σ τ) (v i)) := by
  rw [sesq_eq_sum C.h.toSesq (Pi.basisFun E (Fin (j + j'))) w v]
  simp only [map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, LatEmb.gr, Matrix.map_apply, Pi.star_apply,
    Pi.basisFun_repr, GroundTheory.Heights₂.Theta.embedding_conj (maximalRealSubfield E) E, mul_assoc]
  rfl

theorem Fm_vec (x y : Λ) : C.Fm (C.vec x) (C.vec y) = F.form x y := by
  have h := C.form_eq x y
  have h2 := trace_eq_sum_re F.cm (C.xi * C.h.toSesq (C.e y) (C.e x))
  rw [← h] at h2
  simp only [Rat.cast_intCast] at h2
  rw [h2]
  unfold LatEmb.Fm
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, emb_sesq]
  rfl

end Lat

section Rot

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) where
  toFun := C.vec
  map_zero' := by
    ext τ i
    simp [LatEmb.vec]
  map_add' x y := by
    ext τ i
    simp [LatEmb.vec]

theorem vec_lam (k : Fin (2 * g)) : C.vec (C.lam k) = C.bas k := by
  ext τ i
  exact (C.bas_eq k τ i).symm

theorem perExt_bas (R : RiemLat E g Λ) (k : Fin (2 * g)) : C.perExt R (C.bas k) = R.P (C.lam k) := by
  simp [LatEmb.perExt]

theorem perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  have h : ((C.perExt R).toAddMonoidHom.comp (vecHom C)).toIntLinearMap = R.P.toIntLinearMap := by
    apply C.lam.ext
    intro k
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [vec_lam, perExt_bas]
  exact DFunLike.congr_fun h x

def FmB : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ C.Fm
    (fun y z w => by
      simp only [LatEmb.Fm, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r y w => by
      simp only [LatEmb.Fm, Pi.smul_apply, mulVec_smul, dotProduct_smul, mul_smul_comm, Complex.smul_re,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring)
    (fun y z w => by
      simp only [LatEmb.Fm, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r y w => by
      simp only [LatEmb.Fm, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, mul_smul_comm, Complex.smul_re,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring)

def HrB (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y y' => (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im)
    (fun y z w => by
      simp only [map_add, add_dotProduct, Complex.add_im])
    (fun r y w => by
      simp only [map_smul, smul_dotProduct, Complex.smul_im])
    (fun y z w => by
      simp only [map_add, star_add, mulVec_add, dotProduct_add, Complex.add_im])
    (fun r y w => by
      simp only [map_smul, star_smul, star_trivial, mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem im_eq_Fm (R : RiemLat E g Λ) (hform : R.form = F.form) (y y' : Ψ → Fin (j + j') → ℂ) :
    (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  have h : HrB C R = FmB C := LinearMap.ext_basis C.bas C.bas fun k l => by
    show (C.perExt R (C.bas k) ⬝ᵥ R.Hm *ᵥ star (C.perExt R (C.bas l))).im = C.Fm (C.bas k) (C.bas l)
    rw [perExt_bas, perExt_bas, R.im, hform, ← vec_lam, ← vec_lam, Fm_vec]
  exact DFunLike.congr_fun (DFunLike.congr_fun h y) y'

def rotL (ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) :
    (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y τ := ai τ *ᵥ y τ
  map_add' y z := by
    ext τ i
    simp [mulVec_add]
  map_smul' r y := by
    ext τ i
    simp [mulVec_smul]

theorem Fm_rot (ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (h : ∀ τ, (ai τ)ᴴ * C.gr τ * ai τ = C.gr τ)
    (y y' : Ψ → Fin (j + j') → ℂ) : C.Fm (rotL ai y) (rotL ai y') = C.Fm y y' := by
  unfold LatEmb.Fm
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 : star (ai τ *ᵥ y' τ) ⬝ᵥ (C.gr τ *ᵥ (ai τ *ᵥ y τ)) = star (y' τ) ⬝ᵥ (C.gr τ *ᵥ y τ) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h]
  show 2 * (_ * (star (ai τ *ᵥ y' τ) ⬝ᵥ (C.gr τ *ᵥ (ai τ *ᵥ y τ)))).re = _
  rw [h1]

variable (F) in

def scL (c : 𝓞 E) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y τ := F.σ τ c • y τ
  map_add' y z := by
    ext τ i
    simp [mul_add]
  map_smul' r y := by
    ext τ i
    simp [mul_left_comm]

theorem scL_vec (c : 𝓞 E) (x : Λ) : scL F c (C.vec x) = C.vec (c • x) := by
  ext τ i
  simp [scL, LatEmb.vec, C.e_smul, embOf_coe]

theorem perExt_sc (R : RiemLat E g Λ) (c : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (scL F c y) = R.B c (C.perExt R y) := by
  have h : (C.perExt R).comp (scL F c) = ((R.B c).restrictScalars ℝ).comp (C.perExt R) := C.bas.ext fun k => by
    show C.perExt R (scL F c (C.bas k)) = R.B c (C.perExt R (C.bas k))
    rw [← vec_lam C k, scL_vec, perExt_vec, perExt_vec, R.act]
  exact DFunLike.congr_fun h y

theorem rotL_sc (ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    rotL ai (scL F c y) = scL F c (rotL ai y) := by
  funext τ
  simp [rotL, scL, mulVec_smul]

def rot (R : RiemLat E g Λ) (ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hform : R.form = F.form)
    (h : ∀ τ, (ai τ)ᴴ * C.gr τ * ai τ = C.gr τ) : RiemLat E g Λ :=
  { R with
    P := ((C.perExt R).comp (rotL ai)).toAddMonoidHom.comp (vecHom C)
    im := fun x y => by
      show (C.perExt R (rotL ai (C.vec x)) ⬝ᵥ R.Hm *ᵥ star (C.perExt R (rotL ai (C.vec y)))).im = _
      rw [im_eq_Fm C R hform, Fm_rot C ai h, Fm_vec, hform]
    act := fun c x => by
      show C.perExt R (rotL ai (C.vec (c • x))) = R.B c (C.perExt R (rotL ai (C.vec x)))
      rw [← scL_vec, rotL_sc, perExt_sc] }

theorem perExt_of_P {R R' : RiemLat E g Λ} {ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ}
    (h : ∀ x, R'.P x = C.perExt R (rotL ai (C.vec x))) : C.perExt R' = (C.perExt R).comp (rotL ai) :=
  C.bas.ext fun k => by
    rw [LinearMap.comp_apply, perExt_bas, h, vec_lam]

open Classical in
theorem rotL_single (ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    rotL ai (Pi.single τ y) = Pi.single τ (ai τ *ᵥ y) := by
  funext t
  by_cases ht : t = τ
  · subst ht
    simp [rotL]
  · simp [rotL, Pi.single_eq_of_ne ht]

theorem pPart_rot {R R' : RiemLat E g Λ} {ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ}
    (h : ∀ x, R'.P x = C.perExt R (rotL ai (C.vec x))) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.pPart R' τ y = C.pPart R τ (ai τ *ᵥ y) := by
  unfold LatEmb.pPart
  simp only [perExt_of_P C h, LinearMap.comp_apply, rotL_single, mulVec_smul]

theorem pBar_rot {R R' : RiemLat E g Λ} {ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ}
    (h : ∀ x, R'.P x = C.perExt R (rotL ai (C.vec x))) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.pBar R' τ y = C.pBar R τ (ai τ *ᵥ y) := by
  unfold LatEmb.pBar
  simp only [perExt_of_P C h, LinearMap.comp_apply, rotL_single, mulVec_smul]

theorem inv_preserves {N : Type} [Fintype N] [DecidableEq N] {a ai G : Matrix N N ℂ} (hone : a * ai = 1)
    (h : aᴴ * G * a = G) : aiᴴ * G * ai = G := by
  calc aiᴴ * G * ai = aiᴴ * (aᴴ * G * a) * ai := by rw [h]
    _ = (a * ai)ᴴ * G * (a * ai) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = G := by
      rw [hone]
      simp

theorem isAdapted_rot {R R' : RiemLat E g Λ} {a ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ}
    (hone : ∀ τ, a τ * ai τ = 1) (ha : ∀ τ, (a τ)ᴴ * C.gr τ * a τ = C.gr τ)
    (h : ∀ x, R'.P x = C.perExt R (rotL ai (C.vec x))) {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}
    (hA : C.IsAdapted R A) : C.IsAdapted R' fun τ => a τ * A τ := by
  have hinv : ∀ τ, ai τ * a τ = 1 := fun τ => mul_eq_one_comm.1 (hone τ)
  have hback : ∀ τ (v : Sg j j' → ℂ), ai τ *ᵥ ((a τ * A τ) *ᵥ v) = A τ *ᵥ v := by
    intro τ v
    rw [mulVec_mulVec, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  refine ⟨fun τ => ?_, fun τ v => ?_, fun τ v => ?_⟩
  · rw [← hA.unit τ, conjTranspose_mul]
    unfold LatEmb.sgr
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc (A τ)ᴴ * (a τ)ᴴ * C.gr τ * (a τ * A τ) = (A τ)ᴴ * ((a τ)ᴴ * C.gr τ * a τ) * A τ := by
          simp only [Matrix.mul_assoc]
      _ = (A τ)ᴴ * C.gr τ * A τ := by rw [ha]
  · rw [pPart_rot C h, hback]
    exact hA.ker τ v
  · rw [pBar_rot C h, hback]
    exact hA.kerBar τ v

theorem rotate_exists (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ)
    (a ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hform : R.form = F.form) (hone : ∀ τ, a τ * ai τ = 1)
    (ha : ∀ τ, (a τ)ᴴ * C.gr τ * a τ = C.gr τ) :
    ∃ R' : RiemLat E g Λ, R'.form = R.form ∧ R'.B = R.B ∧ (∀ x, R'.P x = C.perExt R fun τ => ai τ *ᵥ C.vec x τ) ∧
      ∀ A, C.IsAdapted R A → C.IsAdapted R' fun τ => a τ * A τ := by
  have h : ∀ x, (rot C R ai hform fun τ => inv_preserves (hone τ) (ha τ)).P x = C.perExt R (rotL ai (C.vec x)) :=
    fun _ => rfl
  exact ⟨rot C R ai hform fun τ => inv_preserves (hone τ) (ha τ), rfl, rfl, h, fun A hA => isAdapted_rot C hone ha h hA⟩

end Rot

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate
