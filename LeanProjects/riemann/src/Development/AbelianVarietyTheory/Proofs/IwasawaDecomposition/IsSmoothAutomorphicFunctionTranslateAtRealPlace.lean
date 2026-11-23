import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.RealTranslate

open GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom

section Lin

variable {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ}

theorem mul_inv_eq (ha : aᴴ * H * a = H) (hab : a * b = 1) : H * b = aᴴ * H := by
  conv_lhs => rw [← ha]
  rw [Matrix.mul_assoc, hab, Matrix.mul_one]

theorem inv_mul_eq (ha : aᴴ * H * a = H) (hab : a * b = 1) : bᴴ * H = H * a := by
  conv_lhs => rw [← ha]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hab, conjTranspose_one, Matrix.one_mul]

theorem skew_conj (ha : aᴴ * H * a = H) (hab : a * b = 1) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) :
    (b * X * a)ᴴ * H + H * (b * X * a) = 0 := by
  have e : (b * X * a)ᴴ * H + H * (b * X * a) = aᴴ * (Xᴴ * (bᴴ * H)) + (H * b) * X * a := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, inv_mul_eq ha hab, mul_inv_eq ha hab]
  calc _ = aᴴ * (Xᴴ * H + H * X) * a := by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

theorem bar_conj (hu : IsUnit H.det) (ha : aᴴ * H * a = H) (hab : a * b = 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    -(H⁻¹ * (b * Z * a)ᴴ * H) = b * (-(H⁻¹ * Zᴴ * H)) * a := by
  have h1 : H⁻¹ * aᴴ = b * H⁻¹ := by
    rw [← nonsing_inv_mul_cancel_left H (b * H⁻¹) hu, ← Matrix.mul_assoc H, mul_inv_eq ha hab,
      mul_nonsing_inv_cancel_right _ _ hu]
  have e : H⁻¹ * (b * Z * a)ᴴ * H = (H⁻¹ * aᴴ) * Zᴴ * (bᴴ * H) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, h1, inv_mul_eq ha hab]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem exp_conj_eq (hab : a * b = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • X) * a = a * NormedSpace.exp (t • (b * X * a)) := by
  have hu : IsUnit a.det := isUnit_det_of_right_inverse hab
  have e : t • (b * X * a) = a⁻¹ * (t • X) * a := by
    rw [inv_eq_right_inv hab, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj' _ _ ((isUnit_iff_isUnit_det a).2 hu), Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]

end Lin

variable {D : D7} {θ : InfF D} {V : HSp D}

variable (θ) in

def adAt (h : GA D V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ * X * infMat D.sp.cm.sig V.gram (θ τ) h

variable (θ) in

def IsRealPt (h : GA D V) : Prop :=
  h ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

theorem isRealPt_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsRealPt θ (atTau θ V τ g) := by
  have h := atTau_spec hθ V τ hg
  refine ⟨h.1, fun τ' => ?_⟩
  by_cases c : τ' = τ
  · subst c; rw [h.2.1]; exact hg
  · rw [h.2.2 τ' c]; exact one_mem_UH _

variable {h : GA D V}

theorem adAt_mem (hh : IsRealPt θ h) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    adAt θ h τ X ∈ lieAt V τ := skew_conj (hh.2 τ) (infMat_mul_inv θ V τ h) hX

theorem oneP_mul (hθ : IsInfFam θ) (hh : IsRealPt θ h) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * h = h * oneP θ V τ (adAt θ h τ X) t := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have h1 := atTau_spec hθ V τ (GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 τ).2 hX t)
  have h2 := atTau_spec hθ V τ (GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 τ).2 (adAt_mem hh hX) t)
  refine R.2.2.1 _ (mul_mem h1.1 hh.1) _ (mul_mem hh.1 h2.1) fun τ' => ?_
  rw [infMat_mul, infMat_mul]
  unfold oneP
  by_cases c : τ' = τ
  · subst c
    rw [h1.2.1, h2.2.1]
    exact exp_conj_eq (infMat_mul_inv θ V τ' h) X t
  · rw [h1.2.2 τ' c, h2.2.2 τ' c, Matrix.one_mul, Matrix.mul_one]

theorem Rder_rTr (hθ : IsInfFam θ) (hh : IsRealPt θ h) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V h φ) = rTr V h (Rder θ V τ (adAt θ h τ X) φ) := by
  funext g
  unfold Rder rTr
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, oneP_mul hθ hh hX]

theorem RderC_rTr (hθ : IsInfFam θ) (hh : IsRealPt θ h) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e : conjAt V τ (adAt θ h τ Z) = adAt θ h τ (conjAt V τ Z) :=
    bar_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (hh.2 τ) (infMat_mul_inv θ V τ h) Z
  unfold RderC
  rw [Rder_rTr hθ hh h1, Rder_rTr hθ hh h2, e]
  simp only [adAt, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  rfl

theorem prod_mul_eq {G : Type} [Group G] (h : G) : ∀ (k : ℕ) (u v : Fin k → G), (∀ i, u i * h = h * v i) →
    (List.ofFn u).prod * h = h * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | k + 1, u, v, e => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]

theorem rTr_mem (hθ : IsInfFam θ) (hh : IsRealPt θ h) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V h φ ∈ SmFun θ V := by
  intro k τs Xs hX g
  have := hφ k τs (fun i => adAt θ h (τs i) (Xs i)) (fun i => adAt_mem hh (hX i)) (g * h)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, prod_mul_eq h k _ _ fun i => oneP_mul hθ hh (hX i) (t i)]

theorem Rder_comb (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) (r s : ℝ) :
    Rder θ V τ (r • X + s • Y) φ = (r : ℂ) • Rder θ V τ X φ + (s : ℂ) • Rder θ V τ Y φ := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  let Y' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, hY⟩
  have k : ∀ W : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ, Rder θ V τ W.1 φ =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ W) ψ).1 := fun W => GlobalTheory.SmoothForms.Rder_eq R τ W φ
  have := k (r • X' + s • Y')
  rw [GlobalTheory.SmoothForms.opAt_add, GlobalTheory.SmoothForms.opAt_smul, GlobalTheory.SmoothForms.opAt_smul] at this
  rw [k X', k Y']
  exact this

theorem RderC_add (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z Z' : Matrix (Fin V.rank) (Fin V.rank) ℂ) : RderC θ V τ (Z + Z') φ = RderC θ V τ Z φ + RderC θ V τ Z' φ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  obtain ⟨h1', h2'⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z'
  have e : conjAt V τ (Z + Z') = conjAt V τ Z + conjAt V τ Z' := by
    simp only [conjAt, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
  have k1 := Rder_comb hθ hφ h1 h1' 1 1
  have k2 := Rder_comb hθ hφ h2 h2' 1 1
  simp only [one_smul, Complex.ofReal_one, ← smul_add] at k1 k2
  unfold RderC
  rw [e, add_add_add_comm Z, k1, add_sub_add_comm, k2, smul_add Complex.I, add_add_add_comm]

theorem RderC_smul (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (τ : D.what₂.Tau) (c : ℂ)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : RderC θ V τ (c • Z) φ = c • RderC θ V τ Z φ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e : conjAt V τ (c • Z) = star c • conjAt V τ Z := by
    simp only [conjAt, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have k1 := Rder_comb hθ hφ h1 h2 c.re (-c.im)
  have k2 := Rder_comb hθ hφ h1 h2 c.im c.re
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hc : c = c.re + c.im * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = c.re - c.im * Complex.I := by
    apply Complex.ext <;> simp
  have e1 : (1 / 2 : ℂ) • (c • Z + star c • conjAt V τ Z) = c.re • ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) +
      (-c.im) • ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) := by
    rw [hs, hI]
    generalize c.re = x at *
    generalize c.im = y at *
    subst hc
    simp only [← Complex.coe_smul]
    push_cast
    match_scalars <;> ring
  have e2 : (1 / (2 * Complex.I) : ℂ) • (c • Z - star c • conjAt V τ Z) = c.im • ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) +
      c.re • ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) := by
    rw [hs, hI]
    generalize c.re = x at *
    generalize c.im = y at *
    subst hc
    simp only [← Complex.coe_smul]
    match_scalars
    · linear_combination (-(y : ℂ) / 2) * Complex.I_mul_I
    · linear_combination (-(y : ℂ) / 2) * Complex.I_mul_I
  unfold RderC
  rw [e, e1, e2, k1, k2]
  generalize c.re = x at *
  generalize c.im = y at *
  subst hc
  push_cast
  match_scalars
  · ring
  · linear_combination (-(y : ℂ)) * Complex.I_mul_I

def derEnd (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ (SmFun θ V) where
  toFun Z :=
    { toFun := fun φ => ⟨RderC θ V τ Z φ.1, (linOnSm_RderC τ Z).mem _ φ.2⟩
      map_add' := fun φ ψ => Subtype.ext ((linOnSm_RderC τ Z).add _ φ.2 _ ψ.2)
      map_smul' := fun c φ => Subtype.ext ((linOnSm_RderC τ Z).smul c _) }
  map_add' Z Z' := LinearMap.ext fun φ => Subtype.ext (RderC_add hθ φ.2 τ Z Z')
  map_smul' c Z := LinearMap.ext fun φ => Subtype.ext (RderC_smul hθ φ.2 τ c Z)

def rTrLin (h : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gelf_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) :
    gelf θ V τ k φ.1 = (GlobalTheory.SmoothForms.gelfA (fun a b => derEnd hθ τ (Matrix.single a b 1)) k φ).1 := by
  rw [gelf, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun idx _ => GlobalTheory.SmoothForms.foldr_ofFn_eq _ _ _ _ (fun _ _ => rfl) φ

theorem gelf_rTr (hθ : IsInfFam θ) (hh : IsRealPt θ h) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ SmFun θ V) : gelf θ V τ k (rTr V h φ) = rTr V h (gelf θ V τ k φ) := by
  let T : Module.End ℂ (SmFun θ V) := (rTrLin h).restrict fun _ hx => rTr_mem hθ hh hx
  have hQP : (infMat D.sp.cm.sig V.gram (θ τ) h)ᵀ * (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹)ᵀ = 1 := by
    rw [← transpose_mul, mul_eq_one_comm.1 (infMat_mul_inv θ V τ h), transpose_one]
  have key := GlobalTheory.Dec.GelfAd.trace_pow_comm (fun a b => derEnd hθ τ (Matrix.single a b 1)) T _ _ hQP
    (fun a b => by
      simp only [← map_smul, ← map_sum]
      have e : ∑ c, ∑ d, ((infMat D.sp.cm.sig V.gram (θ τ) h⁻¹)ᵀ a c * (infMat D.sp.cm.sig V.gram (θ τ) h)ᵀ d b) •
          (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = adAt θ h τ (Matrix.single a b 1) := by
        rw [matrix_eq_sum_single (adAt θ h τ _)]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
        congr 1
        simp [adAt, Matrix.mul_apply, Matrix.single, ite_and]
      rw [e]
      exact LinearMap.ext fun ψ => Subtype.ext (RderC_rTr hθ hh τ _ ψ.1)) (k + 1)
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have := congrArg (fun S : Module.End ℂ (SmFun θ V) => (S ⟨φ, hφ⟩).1) key
  rw [gelf_eq hθ τ k ⟨φ, hφ⟩, gelf_eq hθ τ k ⟨_, rTr_mem hθ hh hφ⟩]
  exact this

theorem foldr_rTr (hθ : IsInfFam θ) (hh : IsRealPt θ h) (φ : GA D V → ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V h φ) =
      rTr V h ((l.map fun p => (p.1, adAt θ h p.1 p.2)).foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      Rder_rTr hθ hh (hl p List.mem_cons_self)]

theorem isAutFunSm_rTr (hθ : IsInfFam θ) (hh : IsRealPt θ h) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (rTr V h φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine { left := fun γ hγ g => ?_, level := ?_, cont := hφ.cont.comp (continuous_mul_right h),
           smooth := rTr_mem hθ hh hφ.smooth, zfin := ?_, growth := ?_ }
  · unfold rTr
    rw [mul_assoc, hφ.left γ hγ]
  · obtain ⟨U, hU, e⟩ := hφ.level
    refine ⟨U, hU, fun u hu hf g => ?_⟩
    unfold rTr
    rw [mul_assoc, ← comm_of_mem V hh.1 hf, ← mul_assoc, e u hu hf]
  · obtain ⟨W, hW, m, s⟩ := hφ.zfin
    refine ⟨(W ⊓ SmFun θ V).map (rTrLin h), inferInstance, ⟨φ, ⟨m, hφ.smooth⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨s τ k f hf.1, (linOnSm_gelf τ k).mem f hf.2⟩, (gelf_rTr hθ hh τ k hf.2).symm⟩
  · obtain ⟨N, hN⟩ := hφ.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun p => (p.1, adAt θ h p.1 p.2)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact adAt_mem hh (hl q hq)) x
    refine ⟨|C| * normInf θ V h ^ N, fun g hg => ?_⟩
    rw [foldr_rTr hθ hh φ l hl]
    unfold rTr
    rw [mul_assoc x, mul_assoc |C|, ← mul_pow, mul_comm (normInf θ V h)]
    exact (hC _ (mul_mem hg hh.1)).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (normInf_nonneg _) ((GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 g h) N) (pow_nonneg (normInf_nonneg _) N)
      (abs_nonneg _))

theorem isAutFunSm_rTr_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ →
    ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) :=
  fun _ _ hθ _ _ hφ τ _ hg => isAutFunSm_rTr hθ (isRealPt_atTau hθ τ hg) hφ

end GlobalTheory.Mem.RealTranslate

end
