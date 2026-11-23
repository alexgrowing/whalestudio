import Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.CasApply
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransport
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecB

open CompanionTheory.Zuck PositivityTheory.UnitaryDecomposition.DecA BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam IsCayleyU)
open Formalism.REAL (Jm UJ)

section Lin

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Jm_sq (ε : Fin m → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem formT_mat (ε : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (hA : A * Jm ε * Aᴴ = Jm ε) (y x : Fin m → H) :
    formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d) = formT ε y x := by
  have key : ∀ d e, ∑ c, (if ε c = true then (1:ℂ) else -1) * (starRingEnd ℂ (A d c) * A e c) = Jm ε e d := by
    intro d e
    rw [← hA, Jm, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, conjTranspose_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  calc formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d)
      = ∑ e, ∑ d, (∑ c, (if ε c = true then (1:ℂ) else -1) * (starRingEnd ℂ (A d c) * A e c)) * ⟪y d, x e⟫_ℂ := by
        unfold formT
        simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = formT ε y x := by
        simp only [key, Jm, diagonal_apply]
        unfold formT
        refine Finset.sum_congr rfl fun d _ => ?_
        simp

theorem formT_le (ε : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (y x : Fin m → H) :
    ‖formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d)‖ ≤
      (∑ c, (∑ d, ‖A d c‖) ^ 2) * ((∑ d, ‖x d‖) * ∑ d, ‖y d‖) := by
  have bound : ∀ (z : Fin m → H) (c : Fin m), ‖∑ d, A d c • z d‖ ≤ (∑ d, ‖A d c‖) * ∑ d, ‖z d‖ := by
    intro z c
    calc ‖∑ d, A d c • z d‖ ≤ ∑ d, ‖A d c‖ * ‖z d‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp [norm_smul]
      _ ≤ ∑ d, ‖A d c‖ * ∑ d, ‖z d‖ := by
          refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact Finset.single_le_sum (f := fun d => ‖z d‖) (fun i _ => norm_nonneg _) (Finset.mem_univ d)
      _ = (∑ d, ‖A d c‖) * ∑ d, ‖z d‖ := by rw [Finset.sum_mul]
  unfold formT
  calc ‖∑ c, (if ε c = true then (1:ℂ) else -1) * ⟪∑ d, A d c • y d, ∑ d, A d c • x d⟫_ℂ‖
      ≤ ∑ c, ‖∑ d, A d c • y d‖ * ‖∑ d, A d c • x d‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        have h1 : ‖(if ε c = true then (1:ℂ) else -1)‖ = 1 := by split_ifs <;> simp
        rw [h1, one_mul]
        exact norm_inner_le_norm _ _
    _ ≤ ∑ c, ((∑ d, ‖A d c‖) * ∑ d, ‖y d‖) * ((∑ d, ‖A d c‖) * ∑ d, ‖x d‖) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul (bound y c) (bound x c) (norm_nonneg _) ?_
        exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = (∑ c, (∑ d, ‖A d c‖) ^ 2) * ((∑ d, ‖x d‖) * ∑ d, ‖y d‖) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring

theorem sum_comp (A B : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → H) (c : Fin m) :
    ∑ d, B d c • ∑ e, A e d • x e = ∑ e, (A * B) e c • x e := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

theorem sum_one (x : Fin m → H) (c : Fin m) : ∑ e, (1 : Matrix (Fin m) (Fin m) ℂ) e c • x e = x c := by
  simp [Matrix.one_apply]

end Lin

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem cay_mem {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r} (hg : gᴴ * Jm ε * g = Jm ε) : P⁻¹ * g * P ∈ GG k r := by
  obtain ⟨⟨hu, hP⟩, _⟩ := hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hu)
  have hPi' : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
  have hP' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP
  show (P⁻¹ * g * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * g * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hP']
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * gᴴ * (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * g * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (gᴴ * Jm ε * g) * P := by
        rw [hPi, hPi']
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [hg]

theorem cay_mem' {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r} (hg : g ∈ GG k r) :
    (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = Jm ε := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one]
  have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
  have hc : Pᴴ * Jm ε * P = PI.UpqRep.Hpk k r := hP.1.2
  calc (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P⁻¹ᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hc, hg', ← hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, Matrix.one_mul]

theorem cay_two {P Q : Mx k r} (hP : IsCayleyU k r ε P) (hQ : IsCayleyU k r ε Q) : Q⁻¹ * P ∈ GG k r := by
  obtain ⟨⟨hu, hP'⟩, _⟩ := hP
  obtain ⟨⟨hv, hQ'⟩, _⟩ := hQ
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hv)
  have hQi' : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQi, conjTranspose_one]
  have e1 : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP'
  have e2 : Qᴴ * Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ'
  show (Q⁻¹ * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * P) = Formalism.QuantumDeterminants.Hpk k r
  calc (Q⁻¹ * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * P)
      = Pᴴ * ((Q⁻¹ᴴ * Qᴴ) * Jm ε * (Q * Q⁻¹)) * P := by
        rw [← e2]
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by
        rw [hQi, hQi', Matrix.one_mul, Matrix.mul_one]
        exact e1

theorem act_coe (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    (CompanionTheory.Zuck.act (vr k r true, U) g x c : U.R.H) = ∑ d, g⁻¹ d c • U.R.σ g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, vr, if_true, ite_true, BranchingSupport.dualM, CompanionTheory.Zuck.URep.sig, dif_pos hg,
    LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.compLeft_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Function.comp_apply, transpose_apply, Submodule.coe_sum,
    Submodule.coe_smul, LinearMap.restrict_coe_apply, ContinuousLinearMap.coe_coe]
  rfl

theorem act_one_coe (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, CompanionTheory.Zuck.one, CompanionTheory.Zuck.triv, CompanionTheory.Zuck.URep.sig, dif_pos hg,
    LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.compLeft_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Function.comp_apply, Submodule.coe_sum,
    Submodule.coe_smul, LinearMap.restrict_coe_apply, ContinuousLinearMap.coe_coe]
  simp only [Fintype.univ_unit, Finset.sum_singleton, Matrix.one_apply_eq, one_smul]
  rfl

def dn (U : URep k r) (P : Mx k r) : M (vr k r true, U) →ₗ[ℂ] (Fin (2 * r + k + 1) → U.R.H) where
  toFun x := fun c => ∑ d, P⁻¹ d c • (x d : U.R.H)
  map_add' x y := by funext c; simp [Finset.sum_add_distrib]
  map_smul' a x := by funext c; simp [Finset.smul_sum, smul_smul, mul_comm]

def ext1 (T : URep k r) (x : T.R.H) : M (one T) := if h : x ∈ T.R.sm then fun _ => ⟨x, h⟩ else 0

theorem extension_one_coe (T : URep k r) (y : M (one T)) : ext1 T (y ()) = y := by
  funext u
  have h : ((y ()) : T.R.H) ∈ T.R.sm := (y ()).2
  simp [ext1, h]

theorem extendHalfPlane_coe_point (T : URep k r) {x : T.R.H} (h : x ∈ T.R.sm) : (ext1 T x () : T.R.H) = x := by
  rw [ext1, dif_pos h]

theorem one_ext (T : URep k r) {y y' : M (one T)} (h : (y () : T.R.H) = y' ()) : y = y' :=
  funext fun _ => Subtype.ext h

private theorem formT_add_right {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (y x x' : Fin m → H) : formT ε y (x + x') = formT ε y x + formT ε y x' := by
  unfold formT
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, inner_add_right, mul_add]

private theorem formT_add_left {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (y y' x : Fin m → H) : formT ε (y + y') x = formT ε y x + formT ε y' x := by
  unfold formT
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, inner_add_left, mul_add]

private theorem formT_smul_right {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (a : ℂ) (y x : Fin m → H) : formT ε y (a • x) = a * formT ε y x := by
  unfold formT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, inner_smul_right]
  ring

private theorem formT_smul_left {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (a : ℂ) (y x : Fin m → H) : formT ε (a • y) x = star a * formT ε y x := by
  unfold formT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, inner_smul_left, Complex.star_def]
  ring

private theorem ext1_add' (T : URep k r) {x x' : T.R.H} (hx : x ∈ T.R.sm) (hx' : x' ∈ T.R.sm) :
    ext1 T (x + x') = ext1 T x + ext1 T x' := by
  have h : x + x' ∈ T.R.sm := T.R.smSub.add_mem hx hx'
  apply one_ext
  rw [extendHalfPlane_coe_point T h, Pi.add_apply, Submodule.coe_add, extendHalfPlane_coe_point T hx, extendHalfPlane_coe_point T hx']

private theorem ext1_smul (T : URep k r) (a : ℂ) {x : T.R.H} (hx : x ∈ T.R.sm) :
    ext1 T (a • x) = a • ext1 T x := by
  have h : a • x ∈ T.R.sm := T.R.smSub.smul_mem a hx
  apply one_ext
  rw [extendHalfPlane_coe_point T h, Pi.smul_apply, Submodule.coe_smul, extendHalfPlane_coe_point T hx]

private theorem sn_one_ext1_eq_norm_dsigW (T : URep k r) {x : T.R.H} (hx : x ∈ T.R.sm) (W : List (Mx k r)) :
    CompanionTheory.Zuck.sn (one T) W (ext1 T x) = ‖PI.UpqRep.dsigW T.R.σ W x‖ := by
  show ∑ c : Unit, ‖PI.UpqRep.dsigW T.R.σ W (ext1 T x c : T.R.H)‖ = _
  rw [Fintype.sum_unique]
  show ‖PI.UpqRep.dsigW T.R.σ W (ext1 T x () : T.R.H)‖ = _
  rw [extendHalfPlane_coe_point T hx]

private theorem sn_nil_eq_sum_norm (U : URep k r) (w : M (vr k r true, U)) :
    CompanionTheory.Zuck.sn (vr k r true, U) [] w = ∑ c, ‖(w c : U.R.H)‖ := rfl

theorem invForm {U T T' : URep k r} {P : Mx k r} (hP : IsCayleyU k r ε P) (i : M (one T) →ₗ[ℂ] M (vr k r true, U))
    (i' : M (one T') →ₗ[ℂ] M (vr k r true, U)) (hi : IsHom (one T) (vr k r true, U) i)
    (hi' : IsHom (one T') (vr k r true, U) i') :
    IsInvForm T.R T'.R fun x y => formT ε (dn U P (i' (ext1 T' y))) (dn U P (i (ext1 T x))) := by
  have hJ : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_sq ε)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  unfold BranchingSupport.IsInvForm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y hy
    simp only [ext1_add' T hx hx', map_add, formT_add_right]
  · intro a x hx y hy
    simp only [ext1_smul T a hx, map_smul, formT_smul_right]
  · intro x hx y hy y' hy'
    simp only [ext1_add' T' hy hy', map_add, formT_add_left]
  · intro a x hx y hy
    simp only [ext1_smul T' a hy, map_smul, formT_smul_left]
  · intro g hg x hx y hy
    have e1 : ∀ (T0 : URep k r) {z : T0.R.H}, z ∈ T0.R.sm →
        ext1 T0 (T0.R.σ g z) = CompanionTheory.Zuck.act (one T0) g (ext1 T0 z) := by
      intro T0 z hz
      have hm : T0.R.σ g z ∈ T0.R.sm := by
        have h0 := (CompanionTheory.Zuck.act (one T0) g (ext1 T0 z) ()).2
        rw [act_one_coe T0 hg, extendHalfPlane_coe_point T0 hz] at h0
        exact h0
      apply one_ext
      rw [extendHalfPlane_coe_point T0 hm, act_one_coe T0 hg, extendHalfPlane_coe_point T0 hz]
    have eB : P⁻¹ * (P * g * P⁻¹)⁻¹ = g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have e2 : ∀ w : M (vr k r true, U), dn U P (CompanionTheory.Zuck.act (vr k r true, U) g w) =
        fun c => ∑ d, (P * g * P⁻¹)⁻¹ d c • U.R.σ g (dn U P w d) := by
      intro w
      funext c
      show ∑ d, P⁻¹ d c • ((CompanionTheory.Zuck.act (vr k r true, U) g w d : U.R.H)) =
        ∑ d, (P * g * P⁻¹)⁻¹ d c • U.R.σ g (∑ e, P⁻¹ e d • (w e : U.R.H))
      simp only [act_coe U hg, map_sum, map_smul]
      rw [sum_comp, sum_comp, eB]
    have hB : (P * g * P⁻¹)⁻¹ * Jm ε * ((P * g * P⁻¹)⁻¹)ᴴ = Jm ε := by
      have hC := cay_mem' hP hg
      have h2 : ((P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹))⁻¹ = (Jm ε)⁻¹ := by rw [hC]
      rw [Matrix.mul_inv_rev ((P * g * P⁻¹)ᴴ * Jm ε) (P * g * P⁻¹), Matrix.mul_inv_rev ((P * g * P⁻¹)ᴴ) (Jm ε),
        hJ] at h2
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      exact h2
    have hiso : ∀ v w : U.R.H, ⟪U.R.σ g v, U.R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := by
      intro v w
      let L : U.R.H →ₗᵢ[ℂ] U.R.H :=
        { toLinearMap := (U.R.σ g : U.R.H →ₗ[ℂ] U.R.H), norm_map' := U.rep.2.1 g hg }
      exact L.inner_map_map v w
    have hi1 := LinearMap.congr_fun (hi.equiv g hg) (ext1 T x)
    have hi2 := LinearMap.congr_fun (hi'.equiv g hg) (ext1 T' y)
    simp only [LinearMap.comp_apply] at hi1 hi2
    simp only []
    rw [e1 T hx, e1 T' hy, hi1, hi2, e2, e2, formT_mat ε _ hB]
    unfold formT
    simp only [hiso]
  · obtain ⟨C1, Ws, hWs, hb1⟩ := hi.cont [] (by intro Y hY; simp at hY)
    obtain ⟨C2, Ws', hWs', hb2⟩ := hi'.cont [] (by intro Y hY; simp at hY)
    refine ⟨(∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) * C1 * C2, Ws, Ws', ?_, ?_⟩
    · intro W hW X hX
      rcases List.mem_append.mp hW with h | h
      · exact hWs W h X hX
      · exact hWs' W h X hX
    · intro x hx y hy
      have s1 := hb1 (ext1 T x)
      have s2 := hb2 (ext1 T' y)
      simp only [sn_one_ext1_eq_norm_dsigW T hx, sn_one_ext1_eq_norm_dsigW T' hy, sn_nil_eq_sum_norm] at s1 s2
      have hK : 0 ≤ ∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have n1 : 0 ≤ ∑ d, ‖(i (ext1 T x) d : U.R.H)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have n2 : 0 ≤ ∑ d, ‖(i' (ext1 T' y) d : U.R.H)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc ‖formT ε (dn U P (i' (ext1 T' y))) (dn U P (i (ext1 T x)))‖
          ≤ (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) *
              ((∑ d, ‖(i (ext1 T x) d : U.R.H)‖) * ∑ d, ‖(i' (ext1 T' y) d : U.R.H)‖) :=
            formT_le ε P⁻¹ (fun d => (i' (ext1 T' y) d : U.R.H)) (fun d => (i (ext1 T x) d : U.R.H))
        _ ≤ (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) *
              ((C1 * (List.map (fun W => ‖PI.UpqRep.dsigW T.R.σ W x‖) Ws).sum) *
                (C2 * (List.map (fun W => ‖PI.UpqRep.dsigW T'.R.σ W y‖) Ws').sum)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul s1 s2 n2 (n1.trans s1)) hK
        _ = (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) * C1 * C2 * (List.map (fun W => ‖PI.UpqRep.dsigW T.R.σ W x‖) Ws).sum *
              (List.map (fun W => ‖PI.UpqRep.dsigW T'.R.σ W y‖) Ws').sum := by ring

end PositivityTheory.UnitaryDecomposition.DecB
