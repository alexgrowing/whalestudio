import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.PolynomialThetaProduct
import Formalism.SharpRestriction.GrowthBounds.ObjBridge

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Lift

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def kap (h : HidaSetting p n' W Qq O Kf ι σ j w) : KK O ≃ₐ[O] Kf :=
  haveI := h.frac_O
  FractionRing.algEquiv O Kf

def kapR (h : HidaSetting p n' W Qq O Kf ι σ j w) : KK O →+* Kf := ((kap h : KK O ≃ₐ[O] Kf) : KK O →+* Kf)

theorem kapR_alg (h : HidaSetting p n' W Qq O Kf ι σ j w) (x : O) :
    kapR h (algebraMap O (KK O) x) = algebraMap O Kf x := by
  unfold kapR
  exact (kap h).commutes x

theorem kapR_inj (h : HidaSetting p n' W Qq O Kf ι σ j w) : Function.Injective (kapR h) := by
  intro a b hab
  exact (kap h).injective hab

theorem coeffs_iff (h : HidaSetting p n' W Qq O Kf ι σ j w) {τ : Type} (a : O) (P : MvPolynomial τ (KK O)) :
    (∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (a * c)) ↔
      ∃ P0 : MvPolynomial τ O, map (kapR h) P = algebraMap O Kf a • map (algebraMap O Kf) P0 := by
  classical
  constructor
  · intro hc
    choose c hc using hc
    refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
    ext m
    rw [coeff_map, coeff_smul, coeff_map, smul_eq_mul]
    have e : (∑ x ∈ P.support, monomial x (c x)).coeff m = if m ∈ P.support then c m else 0 := by
      rw [coeff_sum]
      simp only [coeff_monomial]
      exact Finset.sum_ite_eq' _ _ _
    rw [e]
    by_cases hm : m ∈ P.support
    · rw [if_pos hm, hc m, kapR_alg, map_mul]
    · rw [if_neg hm, map_zero, mul_zero]
      rw [MvPolynomial.mem_support_iff, not_not] at hm
      rw [hm, map_zero]
  · rintro ⟨P0, hP0⟩ m
    refine ⟨P0.coeff m, kapR_inj h ?_⟩
    have e := congrArg (fun Q => Q.coeff m) hP0
    simp only [coeff_map, coeff_smul, smul_eq_mul] at e
    rw [e, kapR_alg, map_mul]

theorem inA_iff (h : HidaSetting p n' W Qq O Kf ι σ j w) {τ : Type} (P : MvPolynomial τ (KK O)) :
    InA (O := O) P ↔ ∃ P0 : MvPolynomial τ O, map (kapR h) P = map (algebraMap O Kf) P0 := by
  unfold InA
  have e := coeffs_iff h (1 : O) P
  simp only [one_mul, map_one, one_smul] at e
  exact e

theorem inWj_iff (h : HidaSetting p n' W Qq O Kf ι σ j w) {τ : Type} (P : MvPolynomial τ (KK O)) (i : ℕ) :
    InWj w P i ↔
      ∃ P0 : MvPolynomial τ O, map (kapR h) P = algebraMap O Kf w ^ i • map (algebraMap O Kf) P0 := by
  unfold InWj
  have e := coeffs_iff h (w ^ i) P
  rw [map_pow] at e
  exact e

theorem pol_iff (h : HidaSetting p n' W Qq O Kf ι σ j w) {S : Type} (k : ℕ) (d : S → ℕ)
    (P : MvPolynomial (S × Fin k) (KK O)) : P ∈ Formalism.MainNotions.G.Pol (KK O) k d ↔ map (kapR h) P ∈ Formalism.MainNotions.G.Pol Kf k d := by
  simp only [Formalism.MainNotions.G.Pol, MvPolynomial.mem_restrictSupport_iff]
  rw [MvPolynomial.support_map_of_injective _ (kapR_inj h)]

variable [Fact p.Prime]

theorem sig_iter (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (s : ℕ) (x : WF p n') :
    (σ ^ s) (algebraMap W Qq (φ x)) =
      algebraMap W Qq (φ (((WittVector.frobenius : WF p n' →+* WF p n') ^ s) x)) := by
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', pow_succ']
    change σ ((σ ^ s) _) = _
    rw [ih, hφ]
    rfl

theorem sigPow_nat (s : ℕ) (hs : s < n') :
    sigPow p n' (s : ℤ) = (WittVector.frobenius : WF p n' →+* WF p n') ^ s := by
  have h1 : ((s : ℤ) % (n' : ℤ)) = s := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hs)
  unfold sigPow
  rw [h1]
  simp

theorem sig_tw (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℕ) (hs : s < n') (a b : Fin k) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    kapR h (sigMat p n' O g (s : ℤ) a b) = la_tw ι σ s (matQ φ g) a b := by
  simp only [sigMat, Matrix.of_apply, kapR_alg, sigPow_nat s hs, la_tw, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom, matQ]
  rw [sig_iter φ hφ, h.ι_comp]
  rfl

theorem sig_tw_mat (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℕ) (hs : s < n') :
    letI : Algebra (WF p n') O := algOfIdent j φ
    (kapR h).mapMatrix (sigMat p n' O g (s : ℤ)) = la_tw ι σ s (matQ φ g) := by
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact sig_tw h φ hφ g s hs a b

theorem sigMat_det (φ : WF p n' ≃+* W) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) (s : ℤ) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    IsUnit (sigMat p n' O g s).det := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have e : sigMat p n' O g s = ((algebraMap O (KK O)).comp ((algebraMap (WF p n') O).comp (sigPow p n' s))).mapMatrix g := by
    ext a b
    rfl
  rw [e, ← RingHom.map_det]
  exact IsUnit.map _ hg

theorem sig_tw_inv (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) (s : ℕ) (hs : s < n') (a b : Fin k) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    kapR h ((sigMat p n' O g (s : ℤ))⁻¹ a b) = (la_tw ι σ s (matQ φ g))⁻¹ a b := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hdet := sigMat_det (O := O) (j := j) φ g hg (s : ℤ)
  have key : (kapR h).mapMatrix ((sigMat p n' O g (s : ℤ))⁻¹) = (la_tw ι σ s (matQ φ g))⁻¹ := by
    rw [← sig_tw_mat h φ hφ g s hs]
    symm
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  have e := congrFun (congrFun key a) b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  exact e

theorem matQ_tw_det (φ : WF p n' ≃+* W) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g) (s : ℕ) :
    IsUnit (la_tw ι σ s (matQ (Qq := Qq) φ g)).det := by
  have e : la_tw ι σ s (matQ (Qq := Qq) φ g) = ((ι.comp ((σ ^ s : Qq ≃+* Qq) : Qq →+* Qq)).comp ((algebraMap W Qq).comp (φ : WF p n' →+* W))).mapMatrix g := by
    ext a b
    rfl
  rw [e, ← RingHom.map_det]
  exact IsUnit.map _ hg

def Bm {S : Type} (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) (r : ℕ) {k : ℕ} (vec : S → Bool)
    (pos : S → Fin n') (g : Matrix (Fin k) (Fin k) (WF p n')) (x : S) : Matrix (Fin k) (Fin k) Kf :=
  fun c b =>
    if vec x then (if r ≤ b.val then algebraMap O Kf w else 1) * (la_tw ι σ (pos x).val (matQ φ g))⁻¹ b c
    else (if b.val < r then algebraMap O Kf w else 1) * la_tw ι σ (pos x).val (matQ φ g) c b

theorem lift_eq {S : Type} [Fintype S] [DecidableEq S] (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W)
    (hφ : IsWittIdent σ φ) (r : ℕ) {k : ℕ} (LL : LiftLetters S) (pos : S → Fin n')
    (hpos : ∀ x, LL.pos x = ((pos x).val : ℤ)) (g : Matrix (Fin k) (Fin k) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial (S × Fin k) (KK O)) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    map (kapR h) (liftSubst p n' O w r LL g F) = Lin (Bm ι σ w φ r LL.vec pos g) (map (kapR h) F) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hinv : ∀ x b c, kapR h ((sigMat p n' O g (LL.pos x))⁻¹ b c) = (la_tw ι σ (pos x).val (matQ φ g))⁻¹ b c := by
    intro x b c
    rw [hpos x]
    exact sig_tw_inv h φ hφ g hg _ (pos x).isLt b c
  have hmat : ∀ x b c, kapR h (sigMat p n' O g (LL.pos x) b c) = la_tw ι σ (pos x).val (matQ φ g) b c := by
    intro x b c
    rw [hpos x]
    exact sig_tw h φ hφ g _ (pos x).isLt b c
  have e : (MvPolynomial.map (kapR h)).comp (liftSubst p n' O w r LL g).toRingHom =
      (Lin (Bm ι σ w φ r LL.vec pos g)).toRingHom.comp (MvPolynomial.map (kapR h)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Lin, liftSubst]
    · intro v
      obtain ⟨x, c⟩ := v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, liftSubst, aeval_X, map_X, Lin]
      by_cases hv : LL.vec x
      · simp only [hv, if_true, Bm, map_sum, map_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_C, hinv]
        split_ifs <;> simp [map_C, map_X, kapR_alg, C_mul] <;> ring
      · simp only [hv, Bool.false_eq_true, if_false, Bm, map_sum, map_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_C, hmat]
        split_ifs <;> simp [map_C, map_X, kapR_alg, C_mul] <;> ring
  exact RingHom.congr_fun e F

end Lift

end Formalism.L2.G.Model
