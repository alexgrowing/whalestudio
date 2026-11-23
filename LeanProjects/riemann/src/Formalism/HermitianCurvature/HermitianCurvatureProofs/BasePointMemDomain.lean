import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentiableAtOfPuncturedSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.LevelPointCoordinates

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem arel_vlet {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (l : Wd.Letter ℂ S) : ARel T (Wd.vlet σ l) (Wd.vlet σ' l) := by
  unfold Wd.vlet Wd.Ts
  refine arel_ins _ (brel_lift0 ?_)
  split_ifs
  · exact mrel_Tm _ hp hc hci
  · intro a b
    rw [Matrix.map_apply, Matrix.map_apply]
    exact rel_star (mrel_Tm _ hp hc hci a b)

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by unfold Wd.bT; exact arel_mul (arel_vlet hp hc hci l) (arel_bT hp hc hci w)

end bT

section pt

theorem base_point_eq_affine {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) : pt0 hn c = fun σ => Lz (n := n) σ + pt0 hn c 0 := by
  funext σ l
  show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)
  by_cases hl : l.val = 0
  · simp [PBH.consC, Lz, hl]
  · simp [PBH.consC, Lz, hl]

theorem contDiff_base_point {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) : ContDiff ℝ ∞ (pt0 hn c) := by
  rw [base_point_eq_affine hn c]
  exact (Lz (n := n)).contDiff.add contDiff_const

theorem contDiffAt_gauge {τ : ℂ} (hτ : τ ≠ 0) (m : ℕ) :
    ContDiffAt ℝ ∞ (fun σ : ℂ => ((((‖σ‖ ^ m)⁻¹ : ℝ)) : ℂ)) τ := by
  have h1 : ContDiffAt ℝ ∞ (fun σ : ℂ => ‖σ‖) τ := contDiffAt_norm ℝ hτ
  have h2 := (h1.pow m).inv (pow_ne_zero m (norm_ne_zero_iff.2 hτ))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp τ h2

end pt

section read

variable {k n ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem base_point_mem_domain (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    {y : (Fin ρ → ℂ) × Mx k ρ} (hy : y ∈ DomR k ρ zs zs') {τ : ℂ} (hτ : τ ≠ 0) :
    (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z' := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  have e : pt0 rfl y.1 τ = PBH.consC τ y.1 := funext fun l => by simp [pt0]
  rw [e, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact (PBH.domR_iota hτ zs zs' y.1 y.2).2 hy

def rdF (hn : 1 + ρ = n) (y : (Fin ρ → ℂ) × Mx k ρ) (Φ : Fn k n (Wq →L[ℂ] Wp)) : ℂ → (Wq →L[ℂ] Wp) :=
  off0 fun τ => ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) • Φ (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))

variable {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}

theorem rd_smooth (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {y : (Fin ρ → ℂ) × Mx k ρ}
    (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z')
    {Φ : Fn k n (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k n z z' π π') :
    ContDiffOn ℝ ∞ (fun τ => Φ (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))) {τ | τ ≠ 0} := by
  intro τ0 hτ0
  obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 _ (hdom τ0 hτ0)
  let φ : ℂ → (Fin n → ℂ) × Mx k n := fun τ => (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2))
  have hφ : ContDiff ℝ ∞ φ := (contDiff_base_point hn y.1).prodMk contDiff_const
  have hFat : ContDiffAt ℝ ∞ F (φ τ0) := hF.contDiffAt (hU.mem_nhds hxU)
  have hcomp : ContDiffAt ℝ ∞ (F ∘ φ) τ0 := hFat.comp τ0 hφ.contDiffAt
  have heq : (fun τ => Φ (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))) =ᶠ[𝓝 τ0] F ∘ φ := by
    filter_upwards [hφ.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with τ hτ
    exact hΦF (φ τ) hτ (hdom τ0 hτ0).2.1
  exact (hcomp.congr_of_eventuallyEq heq).contDiffWithinAt

theorem rd_raw_smooth (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {y : (Fin ρ → ℂ) × Mx k ρ}
    (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z')
    {Φ : Fn k n (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k n z z' π π') :
    ContDiffOn ℝ ∞ (fun τ => ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) •
      Φ (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))) {τ | τ ≠ 0} := by
  intro τ0 hτ0
  exact ((contDiffAt_gauge hτ0 _).smul ((rd_smooth hn hdom hΦ).contDiffAt
    (isOpen_ne.mem_nhds hτ0))).contDiffWithinAt

theorem rd_mem (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {y : (Fin ρ → ℂ) × Mx k ρ}
    (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z')
    {Φ : Fn k n (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k n z z' π π') : rdF hn y Φ ∈ V1 (Wq →L[ℂ] Wp) :=
  off_zero_mem_punctured_smooth (rd_raw_smooth hn hdom hΦ)

def rdL (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} (y : (Fin ρ → ℂ) × Mx k ρ)
    (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z') :
    RadSp k n z z' π π' →ₗ[ℂ] V1 (Wq →L[ℂ] Wp) where
  toFun Φ := ⟨rdF hn y Φ.1, rd_mem hn hdom Φ.2⟩
  map_add' Φ Ψ := by
    ext τ : 2
    by_cases hτ : τ = 0
    · simp [rdF, off0, hτ]
    · simp [rdF, off0, hτ, smul_add]
  map_smul' s Φ := by
    ext τ : 2
    by_cases hτ : τ = 0
    · simp [rdF, off0, hτ]
    · simp [rdF, off0, hτ, smul_comm s]

section congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dz_congr {f g : ℂ → E} {τ : ℂ} (h : f =ᶠ[𝓝 τ] g) : dz f τ = dz g τ := by
  unfold dz; rw [h.fderiv_eq]

theorem dzb_congr {f g : ℂ → E} {τ : ℂ} (h : f =ᶠ[𝓝 τ] g) : dzb f τ = dzb g τ := by
  unfold dzb; rw [h.fderiv_eq]

end congr

section rel

variable (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} (y : (Fin ρ → ℂ) × Mx k ρ) (hc : y.1 ∈ OmX ρ)
  (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z')

include hc in
theorem rd_apply_ne (Φ : RadSp k n z z' π π') {τ : ℂ} (hτ : τ ≠ 0) :
    (rdL hn y hdom Φ).1 τ = ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) •
      (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2)) := by
  simp [rdL, rdF, off0, hτ]

theorem rd_apply_zero (Φ : RadSp k n z z' π π') : (rdL hn y hdom Φ).1 0 = 0 := by
  simp [rdL, rdF, off0]

theorem raw_ev (Φ : RadSp k n z z' π π') {τ : ℂ} (hτ : τ ≠ 0) :
    (fun σ => (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 σ) (D.castM hn (ιLev k 1 ρ y.2))) =ᶠ[𝓝 τ]
      fun σ => ((‖σ‖ ^ (2 * n + k) : ℝ) : ℂ) • (rdL hn y hdom Φ).1 σ := by
  filter_upwards [isOpen_ne.mem_nhds hτ] with σ hσ
  have hσ' : σ ≠ 0 := hσ
  have hn0 : ‖σ‖ ^ (2 * n + k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hσ')
  simp only [rdL, LinearMap.coe_mk, AddHom.coe_mk, rdF, off0, hσ', if_false, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hn0, Complex.ofReal_one, one_smul]

theorem rd_diff (Φ : RadSp k n z z' π π') {τ : ℂ} (hτ : τ ≠ 0) :
    DifferentiableAt ℝ (rdL hn y hdom Φ).1 τ :=
  differentiableAt_of_punctured_smooth (rdL hn y hdom Φ).2 hτ

variable (X : ActualOps k n z z' π π')

include hc in
theorem rd_op_p (Φ : RadSp k n z z' π π') (τ : ℂ) :
    (rdL hn y hdom (X.op ⟨0, by omega⟩ 0 Φ)).1 τ =
      off0 (fun τ => τ • dz (rdL hn y hdom Φ).1 τ + (((2 * n + k : ℕ) : ℂ) / 2) • (rdL hn y hdom Φ).1 τ) τ := by
  by_cases hτ : τ = 0
  · subst hτ; rw [rd_apply_zero]; simp [off0]
  have hf : DifferentiableAt ℝ (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2)))
      (pt0 hn y.1 τ) := PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ)
  rw [rd_apply_ne hn y hc hdom _ hτ, X.op_apply]
  simp only [off0, hτ, if_false]
  change ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) • opL (⟨0, by omega⟩ : Fin n) 0
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) = _
  rw [(operators_at_base_point hn hc hτ _ hf).1, dz_congr (raw_ev hn y hdom Φ hτ),
    dz_gauge hτ _ (rd_diff hn y hdom Φ hτ), smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hτ)), Complex.ofReal_one, one_smul]

include hc in
theorem rd_op_pb (Φ : RadSp k n z z' π π') (τ : ℂ) :
    (rdL hn y hdom (X.op ⟨0, by omega⟩ 3 Φ)).1 τ =
      off0 (fun τ => conj τ • dzb (rdL hn y hdom Φ).1 τ + (((2 * n + k : ℕ) : ℂ) / 2) • (rdL hn y hdom Φ).1 τ) τ := by
  by_cases hτ : τ = 0
  · subst hτ; rw [rd_apply_zero]; simp [off0]
  have hf : DifferentiableAt ℝ (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2)))
      (pt0 hn y.1 τ) := PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ)
  rw [rd_apply_ne hn y hc hdom _ hτ, X.op_apply]
  simp only [off0, hτ, if_false]
  change ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) • opL (⟨0, by omega⟩ : Fin n) 3
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) = _
  rw [(operators_at_base_point hn hc hτ _ hf).2.2.2.1, dzb_congr (raw_ev hn y hdom Φ hτ),
    dzb_gauge hτ _ (rd_diff hn y hdom Φ hτ), smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hτ)), Complex.ofReal_one, one_smul]

include hc in
theorem rd_op_mul (Φ : RadSp k n z z' π π') (i : Fin 6) (m : ℂ → ℂ)
    (hm : ∀ τ, τ ≠ 0 → opL (⟨0, by omega⟩ : Fin n) i
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) =
        m τ • (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))) (τ : ℂ) :
    (rdL hn y hdom (X.op ⟨0, by omega⟩ i Φ)).1 τ = m τ • (rdL hn y hdom Φ).1 τ := by
  by_cases hτ : τ = 0
  · subst hτ; rw [rd_apply_zero, rd_apply_zero, smul_zero]
  rw [rd_apply_ne hn y hc hdom _ hτ, rd_apply_ne hn y hc hdom _ hτ, X.op_apply]
  change ((((‖τ‖ ^ (2 * n + k))⁻¹ : ℝ)) : ℂ) • opL (⟨0, by omega⟩ : Fin n) i
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) = _
  rw [hm τ hτ, smul_comm]

end rel

section act

variable (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} (y : (Fin ρ → ℂ) × Mx k ρ) (hc : y.1 ∈ OmX ρ)
  (hdom : ∀ τ : ℂ, τ ≠ 0 → (pt0 hn y.1 τ, D.castM hn (ιLev k 1 ρ y.2)) ∈ DomR k n z z')
  (X : ActualOps k n z z' π π')

def kapM (n k : ℕ) : ℂ := ((2 * n + k : ℕ) : ℂ) / 2

include hc in
theorem rel_p : Rel (rdL hn y hdom) (mkP (X.op ⟨0, by omega⟩ 0) (-X.op ⟨0, by omega⟩ 3))
    (site1 (E := Wq →L[ℂ] Wp) (kapM n k)).p := by
  refine rel_mk (fun Φ => ?_) (fun Φ => ?_)
  · exact Subtype.ext (funext fun τ => (rd_op_p hn y hc hdom X Φ τ).symm)
  · rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg]
    exact congrArg Neg.neg (Subtype.ext (funext fun τ => (rd_op_pb hn y hc hdom X Φ τ).symm))

include hc in
theorem rel_mulop (i i' : Fin 6) (m m' : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0})
    (hm' : ContDiffOn ℝ ∞ m' {τ | τ ≠ 0})
    (h1 : ∀ (Φ : RadSp k n z z' π π') τ, τ ≠ 0 → opL (⟨0, by omega⟩ : Fin n) i
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) =
        m τ • (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2)))
    (h2 : ∀ (Φ : RadSp k n z z' π π') τ, τ ≠ 0 → opL (⟨0, by omega⟩ : Fin n) i'
      (fun c' => (Φ : Fn k n (Wq →L[ℂ] Wp)) c' (D.castM hn (ιLev k 1 ρ y.2))) (pt0 hn y.1 τ) =
        m' τ • (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 τ) (D.castM hn (ιLev k 1 ρ y.2))) :
    Rel (rdL hn y hdom) (mkP (X.op ⟨0, by omega⟩ i) (X.op ⟨0, by omega⟩ i'))
      (mkP (opM (E := Wq →L[ℂ] Wp) m hm) (opM m' hm')) := by
  refine rel_mk (fun Φ => ?_) (fun Φ => ?_)
  · exact Subtype.ext (funext fun τ => (rd_op_mul hn y hc hdom X Φ i m (h1 Φ) τ).symm)
  · exact Subtype.ext (funext fun τ => (rd_op_mul hn y hc hdom X Φ i' m' (h2 Φ) τ).symm)

include hc in
theorem rel_c : Rel (rdL hn y hdom) (mkP (X.op ⟨0, by omega⟩ 1) (X.op ⟨0, by omega⟩ 4))
    (site1 (E := Wq →L[ℂ] Wp) (kapM n k)).c :=
  rel_mulop hn y hc hdom X 1 4 _ _ cd_id cd_conj
    (fun Φ τ hτ => (operators_at_base_point hn hc hτ _ (PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ))).2.1)
    (fun Φ τ hτ => (operators_at_base_point hn hc hτ _ (PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ))).2.2.2.2.1)

include hc in
theorem rel_ci : Rel (rdL hn y hdom) (mkP (X.op ⟨0, by omega⟩ 2) (X.op ⟨0, by omega⟩ 5))
    (site1 (E := Wq →L[ℂ] Wp) (kapM n k)).ci :=
  rel_mulop hn y hc hdom X 2 5 _ _ cd_inv cd_conjinv
    (fun Φ τ hτ => (operators_at_base_point hn hc hτ _ (PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ))).2.2.1)
    (fun Φ τ hτ => (operators_at_base_point hn hc hτ _ (PBH.diff_rad Φ.2 _ (pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ))).2.2.2.2.2)

include hc in

theorem rd_act {L : R.LevelData (Pr (RadSp k n z z' π π')) n} (hL : IsActualLevel X L)
    {S : Type} [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k n z z' π π')
    (e : Wd.Ix S) :
    rdL hn y hdom (P5.act (P5.bTl L ⟨0, by omega⟩ w) x e) =
      oneBT (E := Wq →L[ℂ] Wp) (kapM n k) w (fun b => rdL hn y hdom (x b)) e := by
  have hp : Rel (rdL hn y hdom) (P5.site L ⟨0, by omega⟩).p (site1 (kapM n k)).p := by
    show Rel _ (L.p _) _
    rw [hL.1]; exact rel_p hn y hc hdom X
  have hcc : Rel (rdL hn y hdom) (P5.site L ⟨0, by omega⟩).c (site1 (kapM n k)).c := by
    show Rel _ (L.c _) _
    rw [hL.2.2.1]; exact rel_c hn y hc hdom X
  have hci : Rel (rdL hn y hdom) (P5.site L ⟨0, by omega⟩).ci (site1 (kapM n k)).ci := by
    show Rel _ (L.ci _) _
    rw [hL.2.2.2.1]; exact rel_ci hn y hc hdom X
  exact act_tr (arel_bT hp hcc hci w) x e

theorem raw_eq (Φ : RadSp k n z z' π π') {t : ℂ} (ht : t ≠ 0) :
    (Φ : Fn k n (Wq →L[ℂ] Wp)) (pt0 hn y.1 t) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) • (rdL hn y hdom Φ).1 t :=
  (raw_ev hn y hdom Φ ht).self_of_nhds

end act

end read

end Formalism.FourierDecayAlt.P.PBP
