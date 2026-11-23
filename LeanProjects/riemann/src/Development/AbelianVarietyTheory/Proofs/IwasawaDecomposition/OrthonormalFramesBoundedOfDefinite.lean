import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralBasisReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianLatticeMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOrthUpdateMulInv
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FrameStepOfRightMulRealUnitaryGroup

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MixedSignature

open GlobalTheory.UnitaryFrames (hermC_eq_dot gram_eq_mul hermC_mulVec col_mul' locallyCompact_GL secondCountable_GL)
open GlobalTheory.FiniteCovolume (inv_keeps_gram embGL embGL_val hermC_eq_dotProduct uStabSubgroup)
open GlobalTheory.UnitaryLift (det_ne_zero_of_diag)
open GlobalTheory.LatFin (exists_common_den exists_int_smul_mem finite_bounded)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Orth {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)

def Uni {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, ∀ u w, hermC τ.1 G (Matrix.mulVec (n τ) u) (Matrix.mulVec (n τ) w) = hermC τ.1 G u w

lemma det_ne_zero_of_isOrth {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn
  split_ifs <;> simp

lemma isClosed_unitary {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by
  simp only [Uni, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun u => isClosed_iInter fun w => ?_
  refine isClosed_eq ?_ continuous_const
  have hc : Continuous fun g : X.Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val.comp (continuous_apply τ)
  simp only [hermC_eq_dot]
  exact (hc.matrix_mulVec continuous_const).dotProduct
    (continuous_const.matrix_mulVec (hc.matrix_mulVec continuous_const).star)

lemma isOrth_lmulC {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hn : Uni X G n) {x : Frame X.Ψ r} (hx : Orth X G p x) : Orth X G p (X.lmulC n x) := by
  intro τ
  rw [← hx τ, show mat (X.lmulC n x) τ = n τ * mat x τ from rfl]
  ext a b
  simp only [gram, Matrix.of_apply, col_mul', hn τ]

noncomputable def toGL {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x τ) (det_ne_zero_of_isOrth X hx τ)

lemma val_toGL {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x : Frame X.Ψ r} (hx : Orth X G p x) (τ : X.Ψ) :
    (toGL X hx τ : Matrix (Fin r) (Fin r) ℂ) = mat x τ := rfl

lemma quotient_unitary {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x y : Frame X.Ψ r} (hx : Orth X G p x)
    (hy : Orth X G p y) :
    Uni X G fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have key : ∀ u w, hermC τ.1 G (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      hermC τ.1 G (mat y τ *ᵥ u) (mat y τ *ᵥ w) := by
    intro u w
    rw [hermC_mulVec, hermC_mulVec, hx τ, hy τ]
  have h := key ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
    ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  rw [← val_toGL X hx, ← val_toGL X hy] at h
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  exact h

lemma continuous_toGL {r : ℕ} (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) :
    Continuous fun x : {x : Frame X.Ψ r | Orth X G p x} => toGL X x.2 := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun x : {x : Frame X.Ψ r | Orth X G p x} => mat x.1 τ :=
    (continuous_apply τ).comp continuous_subtype_val
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have h : (fun x : {x : Frame X.Ψ r | Orth X G p x} =>
      (((toGL X x.2 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
      fun x => ((mat x.1 τ).det)⁻¹ • (mat x.1 τ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_toGL, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hc.matrix_det.inv₀ fun x => det_ne_zero_of_isOrth X x.2 τ).smul hc.matrix_adjugate

theorem unitary_group_frames :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (p : X.Ψ → ℕ) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, Orth X G p x0 → (∀ g : H, Orth X G p (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | Orth X G p x} ∧ (∀ x, Orth X G p x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g) := by
  classical
  intro r X G p H hH
  haveI := locallyCompact_GL r
  haveI := secondCountable_GL r
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert isClosed_unitary X G using 1
    ext g
    exact hH g
  refine ⟨hcl.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, fun x0 hx0 => ?_⟩
  have horth : ∀ g : H, Orth X G p (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  refine ⟨horth, fun x => if hx : Orth X G p x then
    ⟨toGL X hx * (toGL X hx0)⁻¹, (hH _).2 (quotient_unitary X hx hx0)⟩ else 1, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    refine ((continuous_toGL X G p).mul (continuous_const (y := (toGL X hx0)⁻¹))).congr fun x => ?_
    have hx : Orth X G p x.1 := x.2
    simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    funext τ
    change (((toGL X hx τ * (toGL X hx0 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (toGL X hx0 τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Units.val_mul, inv_mul_cancel_right, val_toGL]
  · intro g
    simp only [dif_pos (horth g)]
    apply Subtype.ext
    change toGL X (horth g) * (toGL X hx0)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    funext τ
    exact Units.ext rfl

theorem isOrth_update_mul_inv :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (τ0 : X.Ψ) (x : Frame X.Ψ r) (a : Matrix (Fin r) (Fin r) ℂ), Orth X G p x → (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → Orth X G p (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X G p τ0 x a hx ha τ
  letI : DecidableEq X.Ψ := Classical.decEq _
  by_cases hτ : τ = τ0
  · subst hτ
    have hm : mat (Function.update x τ (mat x τ * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ * a⁻¹ := by
      unfold mat
      exact Function.update_self _ _ _
    have hJ : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ then (1 : ℂ) else -1)
        = gram τ.1 G (mat x τ) := by
      rw [hx τ]
      congr 1
      funext k
      unfold sgn
      split_ifs <;> simp
    have hdet : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ then (1 : ℂ) else -1).det
        ≠ 0 := by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      split_ifs <;> simp
    have h := inv_keeps_gram hdet ha
    rw [hJ] at h
    rw [hm, ← hx τ, ← h, gram_eq_mul, gram_eq_mul,
      Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  · have hm : mat (Function.update x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ := by
      unfold mat
      exact Function.update_of_ne hτ _ _
    rw [hm]
    exact hx τ

lemma conj_unitary {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} {x0 : Frame X.Ψ r} (hx0 : Orth X G p x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1)) :
    Uni X G fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  have hJ : ∀ τ, (Matrix.diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < (p τ) then (1 : ℂ) else -1) := by
    intro τ
    congr 1
    funext k
    unfold sgn
    split_ifs <;> simp
  have hy : Orth X G p
      (fun τ => (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    intro τ
    have h0 := hx0 τ
    rw [gram_eq_mul, hJ] at h0
    change gram τ.1 G (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [gram_eq_mul, hJ, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
          ((mat x0 τ)ᵀ * (G.map τ.1 * (mat x0 τ).map (starRingEnd ℂ))) *
          (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h0, hc τ]
  have he : toGL X hy = toGL X hx0 * c := by
    funext τ
    exact Units.ext rfl
  rw [← he]
  exact quotient_unitary X hy hx0

theorem step_of_right_mul :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X G p H hH x0 hx0 τ0 a s ha hs hsa
  letI : DecidableEq X.Ψ := Classical.decEq _
  have hda := det_ne_zero_of_diag ha
  let A : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a hda
  let S : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero s (det_ne_zero_of_diag hs)
  have hAi : ((A⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = a⁻¹ := by
    rw [Matrix.coe_units_inv]; rfl
  have hSA : S * A = A⁻¹ * S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAi]
    exact hsa
  have hSA' : S * A⁻¹ = A * S := by
    calc S * A⁻¹ = A * (A⁻¹ * S) * A⁻¹ := by group
      _ = A * S := by rw [← hSA]; group
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) →
      toGL X hx0 * Pi.mulSingle τ0 b * (toGL X hx0)⁻¹ ∈ H := by
    intro b hb
    refine (hH _).2 (conj_unitary X hx0 _ fun τ => ?_)
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hb
    · rw [Pi.mulSingle_eq_of_ne h]
      simp
  refine ⟨(⟨_, hmem A ha⟩ : H)⁻¹, ⟨_, hmem S hs⟩, ?_, fun g => ?_⟩
  · apply Subtype.ext
    have h1 : (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹ : X.Ψ → GL (Fin r) ℂ) =
        Pi.mulSingle τ0 A * Pi.mulSingle τ0 S := by
      rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul, hSA']
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = toGL X hx0 * (Pi.mulSingle τ0 S * (Pi.mulSingle τ0 A)⁻¹) * (toGL X hx0)⁻¹ := by group
      _ = _ := by rw [h1]; group
  · have key : ((g * (⟨_, hmem A ha⟩ : H)⁻¹ : H) : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 =
        (g : X.Ψ → GL (Fin r) ℂ) * toGL X hx0 * Pi.mulSingle τ0 A⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mulSingle_inv]
      group
    funext τ
    have k1 := congrArg (fun u : X.Ψ → GL (Fin r) ℂ => (u τ : Matrix (Fin r) (Fin r) ℂ)) key
    refine k1.trans ?_
    beta_reduce
    rw [Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul]
    by_cases h : τ = τ0
    · subst h
      rw [Pi.mulSingle_eq_same, hAi]
      exact Eq.symm (@Function.update_self X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _)
    · rw [Pi.mulSingle_eq_of_ne h, Units.val_one, Matrix.mul_one]
      exact Eq.symm (@Function.update_of_ne X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _)

theorem isUnitaryC_of_isUStab {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E} (hγ : IsUStab G X.Λ γ) :
    Uni X G fun τ => ((embGL X.Ψ γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  have h0 : (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
    ext a b
    have h := hγ.1 (Pi.single a 1) (Pi.single b 1)
    simp only [herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, one_mul] at h
    have h2 : G a b = ∑ x, ∑ x_1, if x = a then G x x_1 * cc (if x_1 = b then 1 else 0) else 0 := by
      simp [apply_ite cc, cc_one, cc_zero]
    rw [h2, ← h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  intro τ u w
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) E => M.map τ.1) h0
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have e3 : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext a b; simp [emb_cc]
  rw [e3] at h
  simp only [embGL_val]
  set M := (γ : Matrix (Fin r) (Fin r) E).map τ.1
  have e4 : starRingEnd ℂ ∘ (M *ᵥ w) = M.map (starRingEnd ℂ) *ᵥ (starRingEnd ℂ ∘ w) := by
    funext a; exact RingHom.map_mulVec (starRingEnd ℂ) M w a
  rw [hermC_eq_dotProduct, hermC_eq_dotProduct, e4, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X G H _
  refine ⟨((uStabSubgroup G X.Λ).map (embGL X.Ψ)).subgroupOf H, fun g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine exists_congr fun γ => and_congr Iff.rfl ⟨fun h τ => ?_, fun h => ?_⟩
  · rw [← h, embGL_val]
  · funext τ
    exact Units.ext ((embGL_val _ _ _).trans (h τ).symm)

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X G p R
  have h1 : IsClosed {x : Frame X.Ψ r | Orth X G p x} := by
    simp only [Orth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

theorem orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) {p : X.Ψ → ℕ}, (∀ τ, p τ = 0 ∨ p τ = r) →
      ∃ R : ℝ, ∀ x, Orth X G p x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X G p hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a, ‖(G.map τ.1)⁻¹ a a‖, fun x hx τ a b => ?_⟩
  obtain ⟨s, hs, hsa⟩ : ∃ s : ℂ, s * s = 1 ∧ ∀ a : Fin r, ((sgn (p τ) (a : ℕ) : ℝ) : ℂ) = s := by
    rcases hp τ with hp | hp
    · exact ⟨-1, by ring, fun a => by simp [sgn, hp]⟩
    · exact ⟨1, by ring, fun a => by simp [sgn, hp]⟩
  have h : (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) =
      s • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    have h0 := hx τ
    simp only [hsa] at h0
    rw [Matrix.smul_one_eq_diagonal, ← h0]
    ext i j
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h1 := norm_entry_le_of_gram_eq_smul_one _ _ s hs h a b
  have h2 : ‖(G.map τ.1)⁻¹ a a‖ ≤ ∑ a, ‖(G.map τ.1)⁻¹ a a‖ :=
    Finset.single_le_sum (f := fun a => ‖(G.map τ.1)⁻¹ a a‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h3 : ∑ a, ‖(G.map τ.1)⁻¹ a a‖ ≤ ∑ τ : X.Ψ, ∑ a, ‖(G.map τ.1)⁻¹ a a‖ :=
    Finset.single_le_sum (f := fun τ : X.Ψ => ∑ a, ‖(G.map τ.1)⁻¹ a a‖)
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  have h4 : mat x τ a b = x τ a b := rfl
  rw [h4] at h1
  linarith

theorem compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (∀ τ, p τ = 0 ∨ p τ = r) → ∀ x0, Orth X G p x0 → CompactSpace H) := by
  intro r X G p H hH hp x0 hx0
  obtain ⟨R, hR⟩ := orthonormal_frames_bounded_of_definite r X G hp
  obtain ⟨-, -, h⟩ := unitary_group_frames r X p H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h x0 hx0
  have hK := (isCompact_orth_bounded r X G p R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab G X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X G H _
  have hS := finite_automorphisms r X G 2
  set S := {γ : GL (Fin r) E | IsUStab G X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.MixedSignature
