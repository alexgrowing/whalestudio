import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.FlagUnipotentLattices.KappaAssemblyOf

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section SlopeTestRemainingChoices

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_highest_weight_unit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsDS ε lam σ) : ∃ w : H, IsHighestUnit ε lam σ w := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · exact (le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS) :
      S ≤ lowKSub ε lam σ) (S.smul_mem _ hvS)
  · intro θ hθ
    rw [map_smul, hwt θ hθ, smul_comm]

theorem hermitian_of_mem_p (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inP ε X) :
    X.IsHermitian ∧ ∀ a b, ε a = ε b → X a b = 0 := by
  obtain ⟨hG, hA⟩ := hX
  unfold Formalism.REAL.inG at hG
  have hs : ∀ c : Fin n, (if ε c = true then (1:ℂ) else -1) ≠ 0 := by
    intro c
    split_ifs <;> norm_num
  constructor
  · show X.conjTranspose = X
    ext a b
    have h1 := congrFun (congrFun hG a) b
    have h2 := congrFun (congrFun hA a) b
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
      Matrix.neg_apply, Matrix.zero_apply] at h1 h2
    have h3 : (X.conjTranspose a b - X a b) * (if ε b = true then (1:ℂ) else -1) = 0 := by
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right (hs b))
  · intro a b hab
    have h2 := congrFun (congrFun hA a) b
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h2
    rw [hab] at h2
    have h3 : X a b * (2 * (if ε b = true then (1:ℂ) else -1)) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero (hs b))

end SlopeTestRemainingChoices

theorem decay_q_form_of_decay (D : Formalism.BasicNotions.D7) (h0 : DiscreteSeriesDecayBound D) : DiscreteSeriesDecayMinusSigns D := by
  unfold DiscreteSeriesDecayBound at h0
  unfold DiscreteSeriesDecayMinusSigns
  intro n ε lam hlam H _ _ _ σ hσ E hE h hgap hth k X hk hX
  refine le_trans (h0 n ε lam hlam H σ hσ E hE h hgap hth k X hk hX) ?_
  have hh : 0 ≤ h := le_trans (by positivity) hth
  rcases Nat.eq_zero_or_pos (min (pOf ε) (qOf ε)) with hz | hpos
  · have hall : ∀ a b, ε a = ε b := by
      have hpq : pOf ε = 0 ∨ qOf ε = 0 := by omega
      rcases hpq with hp | hq
      · unfold pOf at hp
        have hf := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp)
        intro a b
        have ha := hf (Finset.mem_univ a)
        have hb := hf (Finset.mem_univ b)
        simp only [Bool.not_eq_true] at ha hb
        rw [ha, hb]
      · unfold qOf at hq
        have hf := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hq)
        intro a b
        have ha := hf (Finset.mem_univ a)
        have hb := hf (Finset.mem_univ b)
        simp only [Bool.not_eq_false] at ha hb
        rw [ha, hb]
    have hX0 : ∀ a b, X a b = 0 := fun a b => (hermitian_of_mem_p ε X hX).2 a b (hall a b)
    have hhs : Formalism.REAL.hs X = 0 := by
      unfold Formalism.REAL.hs
      simp [hX0]
    unfold decBound
    rw [hhs]
    simp
  · unfold decBound
    apply Real.exp_le_exp.mpr
    have hq0 : (0 : ℝ) < ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := by exact_mod_cast hpos
    have hm : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ≤ (qOf ε : ℝ) := by exact_mod_cast min_le_right _ _
    apply mul_le_mul_of_nonpos_left _ (by linarith)
    apply min_le_min_left
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    · exact Real.sqrt_pos.mpr (by linarith)
    · exact Real.sqrt_le_sqrt (by linarith)

theorem lowest_K_type_positivity (D : Formalism.BasicNotions.D7) : PositivityFromLowestKType D := by
  intro ha hF
  unfold adm2 at ha
  unfold DiscreteSeriesLowestKTypeFormula at hF
  unfold LowestKTypePositivity
  intro n ε lam hlam H _ _ _ σ hσ h hgap hth X hX x hx
  haveI : FiniteDimensional ℂ (lowKSub ε lam σ) := (ha n ε lam hlam H σ hσ).1.1
  obtain ⟨E, hE⟩ : ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) := by
    refine ⟨(lowKSub ε lam σ).starProjection, ?_⟩
    have hr : LinearMap.range ((lowKSub ε lam σ).starProjection : H →ₗ[ℂ] H) = lowKSub ε lam σ := by
      ext z
      simp
    refine ⟨?_, ?_, hr⟩
    · ext z
      rw [ContinuousLinearMap.comp_apply]
      have hm : (lowKSub ε lam σ).starProjection z ∈
          LinearMap.range ((lowKSub ε lam σ).starProjection : H →ₗ[ℂ] H) :=
        LinearMap.mem_range_self _ z
      rw [hr] at hm
      first
        | exact Submodule.starProjection_eq_self_iff.mpr hm
        | simp only [Submodule.starProjection_apply, Submodule.orthogonalProjection_mem_subspace_eq_self]
    · intro a b
      exact Submodule.inner_starProjection_left_eq_right _ a b
  obtain ⟨w, hw⟩ := exists_highest_weight_unit ε lam σ hσ
  have hpos := (hF n ε lam hlam H σ hσ E hE w hw h hgap hth X hX).2
  have hfix : E x = x := by
    obtain ⟨hidem, -, hr⟩ := hE
    rw [← hr] at hx
    obtain ⟨z, rfl⟩ := hx
    have h := congrArg (fun F : H →L[ℂ] H => F z) hidem
    simpa using h
  have key : ⟪x, σ (NormedSpace.exp X) x⟫_ℂ = ⟪x, (E ∘L σ (NormedSpace.exp X) ∘L E) x⟫_ℂ := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hE.2.1 x, hfix]
  rw [key]
  have hsym : ∀ a b, ⟪(E ∘L σ (NormedSpace.exp X) ∘L E) a, b⟫_ℂ =
      ⟪a, (E ∘L σ (NormedSpace.exp X) ∘L E) b⟫_ℂ := by
    first
      | exact fun a b => hpos.1.isSymmetric a b
      | exact fun a b => hpos.1 a b
      | exact fun a b => hpos.isSelfAdjoint.isSymmetric a b
      | exact fun a b => hpos.isSymmetric a b
  have hre : 0 ≤ (⟪(E ∘L σ (NormedSpace.exp X) ∘L E) x, x⟫_ℂ).re := by
    first
      | exact hpos.re_inner_nonneg_left x
      | exact hpos.2 x
      | exact (Complex.nonneg_iff.mp (hpos.2 x)).1
      | exact (Complex.nonneg_iff.mp (hpos.inner_nonneg_left x)).1
  have hc : ⟪x, (E ∘L σ (NormedSpace.exp X) ∘L E) x⟫_ℂ =
      ⟪(E ∘L σ (NormedSpace.exp X) ∘L E) x, x⟫_ℂ := (hsym x x).symm
  constructor
  · have hconj : (starRingEnd ℂ) ⟪(E ∘L σ (NormedSpace.exp X) ∘L E) x, x⟫_ℂ =
        ⟪x, (E ∘L σ (NormedSpace.exp X) ∘L E) x⟫_ℂ := inner_conj_symm _ _
    rw [← hc] at hconj
    have him := congrArg Complex.im hconj
    rw [Complex.conj_im] at him
    linarith
  · rw [hc]
    exact hre

section Dec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem lowest_K_type_stable (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv
  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    unfold lowKSub
    refine sSup_le fun S hS => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact le_sSup hS (hS.2.1 g hg x hx)
  exact hle hv

theorem orth_proj_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (y : H) : E y ∈ S := by
  obtain ⟨-, -, hr⟩ := hE
  rw [← hr]
  exact LinearMap.mem_range_self (E : H →ₗ[ℂ] H) y

theorem orth_proj_fix {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) {x : H} (hx : x ∈ S) :
    E x = x := by
  obtain ⟨hidem, -, hr⟩ := hE
  rw [← hr] at hx
  obtain ⟨z, rfl⟩ := hx
  have h := congrArg (fun F : H →L[ℂ] H => F z) hidem
  simpa using h

theorem orth_proj_norm_le {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (y : H) : ‖E y‖ ≤ ‖y‖ := by
  obtain ⟨hidem, hsa, -⟩ := hE
  have hEE : E (E y) = E y := by
    have h := congrArg (fun F : H →L[ℂ] H => F y) hidem
    simpa using h
  have h1 : ⟪E y, E y⟫_ℂ = ⟪y, E y⟫_ℂ := by
    rw [hsa y (E y), hEE]
  have h2 : ‖E y‖ ^ 2 ≤ ‖y‖ * ‖E y‖ := by
    have h3 : ‖⟪E y, E y⟫_ℂ‖ = ‖E y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [← h3, h1]
    exact norm_inner_le_norm y (E y)
  nlinarith [norm_nonneg y, norm_nonneg (E y)]

theorem orth_proj_commute_compact (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hrep : IsURepOn (UJset ε) σ)
    {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (hst : IsKStableOn ε σ S)
    (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Formalism.REAL.Kset ε) : E ∘L σ k = σ k ∘L E := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hrep
  have hE' := hE
  obtain ⟨hidem, hsa, hr⟩ := hE'
  have memS : ∀ y, E y ∈ S := fun y => orth_proj_mem hE y
  have fixS : ∀ x ∈ S, E x = x := fun x hx => orth_proj_fix hE hx
  have kill : ∀ u : H, (∀ s ∈ S, ⟪s, u⟫_ℂ = 0) → E u = 0 := by
    intro u hu
    have h2 : ⟪E u, E u⟫_ℂ = 0 := by
      rw [← hsa (E u) u, fixS _ (memS u)]
      exact hu _ (memS u)
    exact inner_self_eq_zero.mp h2
  have KinU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    have hu1 : g.conjTranspose * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show Formalism.REAL.inUJ ε g
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have Kstar : ∀ g ∈ Formalism.REAL.Kset ε, g.conjTranspose ∈ Formalism.REAL.Kset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    have hu1 : g.conjTranspose * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have hu2 : g * g.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
    refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hu1), ?_⟩
    calc g.conjTranspose * Formalism.REAL.Jm ε
        = g.conjTranspose * Formalism.REAL.Jm ε * (g * g.conjTranspose) := by rw [hu2, Matrix.mul_one]
      _ = g.conjTranspose * (Formalism.REAL.Jm ε * g) * g.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = g.conjTranspose * (g * Formalism.REAL.Jm ε) * g.conjTranspose := by rw [← hc]
      _ = g.conjTranspose * g * Formalism.REAL.Jm ε * g.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * g.conjTranspose := by rw [hu1, Matrix.one_mul]
  have hkU : k ∈ UJset ε := KinU k hk
  have hksU : k.conjTranspose ∈ UJset ε := KinU _ (Kstar k hk)
  have hinv : ∀ v, σ k (σ k.conjTranspose v) = v := by
    intro v
    have e1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
    have h3 := hmul k hkU k.conjTranspose hksU
    rw [e1, h1] at h3
    have h4 := congrArg (fun F : H →L[ℂ] H => F v) h3
    simpa using h4.symm
  have hip : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
    LinearIsometry.inner_map_map (⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩ : H →ₗᵢ[ℂ] H) x y
  have horth : ∀ x, ∀ s ∈ S, ⟪s, σ k (x - E x)⟫_ℂ = 0 := by
    intro x s hs
    have hs2 : σ k.conjTranspose s ∈ S := hst _ (Kstar k hk) s hs
    rw [← hinv s, hip, inner_sub_right, ← hsa, fixS _ hs2, sub_self]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have hsplit : σ k x = σ k (E x) + σ k (x - E x) := by
    rw [map_sub]
    abel
  rw [hsplit, map_add, fixS _ (hst k hk _ (memS x)), kill _ (horth x), add_zero]

def oneBasedParam (lam : Fin n → ℝ) (i : ℕ) : ℝ := if h : i - 1 < n then lam ⟨i - 1, h⟩ else 0

theorem weight_one_based_eq (lam : Fin n → ℝ) (X km : Matrix (Fin n) (Fin n) ℂ) (hkm : km ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∏ i ∈ Ico 1 n, (Formalism.NuclearRankWeightBounds.D.lead (km.conjTranspose * NormedSpace.exp X * km) i).re
      ^ (-(oneBasedParam lam i - oneBasedParam lam (i + 1) + 1)) = wtF lam X km := by
  have hinv : km⁻¹ = km.conjTranspose := by
    apply Matrix.inv_eq_left_inv
    exact Matrix.mem_unitaryGroup_iff'.1 hkm
  unfold wtF
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_range, hinv]
  apply Finset.prod_congr rfl
  intro i _
  have hi : i.val < n - 1 := i.2
  have h1 : 1 + i.val ≤ n := by omega
  have e1 : Formalism.NuclearRankWeightBounds.D.lead (km.conjTranspose * NormedSpace.exp X * km) (1 + i.val) =
      leadMinor (km.conjTranspose * NormedSpace.exp X * km) (i.val + 1) (by omega) := by
    unfold Formalism.NuclearRankWeightBounds.D.lead leadMinor
    rw [dif_pos h1]
    have gen : ∀ (a b : ℕ) (hab : a = b) (ha : a ≤ n) (hb : b ≤ n) (M : Matrix (Fin n) (Fin n) ℂ),
        (M.submatrix (Fin.castLE ha) (Fin.castLE ha)).det = (M.submatrix (Fin.castLE hb) (Fin.castLE hb)).det := by
      intro a b hab ha hb M
      subst hab
      rfl
    exact gen _ _ (by omega) _ _ _
  have e2 : oneBasedParam lam (1 + i.val) = lam ⟨i.val, by omega⟩ := by
    unfold oneBasedParam
    rw [dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp)
  have e3 : oneBasedParam lam (1 + i.val + 1) = lam ⟨i.val + 1, by omega⟩ := by
    unfold oneBasedParam
    rw [dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp; omega)
  rw [e1, e2, e3]

end Dec

section Core

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def d30f (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) (kk : Formalism.REAL.KG ε) : H →L[ℂ] H :=
  ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (Formalism.REAL.toMK kk) w)

theorem inner_integral_pull (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) (hint : Integrable (d30f ε lam σ w X) (Formalism.REAL.muK ε)) (x y : H) :
    ⟪x, (∫ kk, d30f ε lam σ w X kk ∂(Formalism.REAL.muK ε)) y⟫_ℂ =
      ∫ kk, ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) *
        (⟪x, σ (Formalism.REAL.toMK kk) w⟫_ℂ * ⟪σ (Formalism.REAL.toMK kk) w, y⟫_ℂ) ∂(Formalism.REAL.muK ε) := by
  rw [ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap y)]
  congr 1
  funext kk
  have hin : ∀ a b : H, (innerSL ℂ a) b = ⟪a, b⟫_ℂ := fun a b => by simp
  simp only [d30f, rank1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, hin,
    inner_smul_right]
  ring

theorem weight_at_zero_eq_one (lam : Fin n → ℝ) (km : Matrix (Fin n) (Fin n) ℂ) (hkm : km ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    wtF lam 0 km = 1 := by
  have hinv : km⁻¹ = star km := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hkm)
  unfold wtF
  refine Finset.prod_eq_one fun i _ => ?_
  rw [NormedSpace.exp_zero, Matrix.mul_one, hinv, Matrix.mem_unitaryGroup_iff'.mp hkm]
  unfold leadMinor
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  simp

end Core

section Core2

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem one_based_param_succ (lam : Fin n → ℝ) (a : Fin n) : oneBasedParam lam (a.val + 1) = lam a := by
  unfold oneBasedParam
  have h : a.val + 1 - 1 < n := by simpa using a.isLt
  rw [dif_pos h]
  exact congrArg lam (Fin.ext (by simp))

theorem compact_block_diagonal (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.REAL.Kset ε) (a b : Fin n)
    (hab : ε a ≠ ε b) : g a b = 0 := by
  obtain ⟨-, hc⟩ := hg
  have h := congrFun (congrFun hc a) b
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have key : ((if ε b = true then (1:ℂ) else -1) - (if ε a = true then 1 else -1)) ≠ 0 := by
    cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
  have h2 : g a b * ((if ε b = true then (1:ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_right key

theorem projected_exp_estimate (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hrep : IsURepOn (UJset ε) σ) (E : H →L[ℂ] H)
    (S : Submodule ℂ H) (hE : IsOrthProjOnto E S) (w : H) (dn : ℕ) (h : ℝ) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inP ε X)
    (hFX : E ∘L σ (NormedSpace.exp X) ∘L E = (dn : ℂ) • ∫ kk, d30f ε lam σ w X kk ∂(Formalism.REAL.muK ε))
    (hF0 : E ∘L σ (NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ)) ∘L E =
      (dn : ℂ) • ∫ kk, d30f ε lam σ w 0 kk ∂(Formalism.REAL.muK ε)) :
    ‖E ∘L σ (NormedSpace.exp X) ∘L E‖ ≤ decBound (min (pOf ε) (qOf ε)) h X := by
  have hbpos : 0 ≤ decBound (min (pOf ε) (qOf ε)) h X := (Real.exp_pos _).le
  have hE0 : E ∘L σ (NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ)) ∘L E = E := by
    rw [NormedSpace.exp_zero, hrep.1.1]
    exact hE.1
  by_cases hi0 : Integrable (d30f ε lam σ w 0) (Formalism.REAL.muK ε)
  swap
  · have hz : E = 0 := by rw [← hE0, hF0, integral_undef hi0, smul_zero]
    rw [hz]
    simpa using hbpos
  by_cases hiX : Integrable (d30f ε lam σ w X) (Formalism.REAL.muK ε)
  swap
  · rw [hFX, integral_undef hiX, smul_zero, norm_zero]; exact hbpos
  have hBmem : ∀ y, (E ∘L σ (NormedSpace.exp X) ∘L E) y ∈ S := fun y => orth_proj_mem hE _
  let A : S →L[ℂ] S := ((E ∘L σ (NormedSpace.exp X) ∘L E).codRestrict S hBmem) ∘L S.subtypeL
  let sd : ℂ := ((Real.sqrt dn : ℝ) : ℂ)
  let v : Formalism.REAL.KG ε → S := fun kk => ⟨E (sd • σ (Formalism.REAL.toMK kk) w), orth_proj_mem hE _⟩
  have hsd : sd * sd = (dn : ℂ) := by
    show ((Real.sqrt dn : ℝ) : ℂ) * ((Real.sqrt dn : ℝ) : ℂ) = (dn : ℂ)
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hv1 : ∀ (x : S) kk, inner ℂ x (v kk) = sd * ⟪(x : H), σ (Formalism.REAL.toMK kk) w⟫_ℂ := by
    intro x kk
    rw [Submodule.coe_inner]
    show ⟪(x : H), E (sd • σ (Formalism.REAL.toMK kk) w)⟫_ℂ = _
    rw [← hE.2.1, orth_proj_fix hE x.2, inner_smul_right]
  have hv2 : ∀ (y : S) kk, inner ℂ (v kk) y = sd * ⟪σ (Formalism.REAL.toMK kk) w, (y : H)⟫_ℂ := by
    intro y kk
    rw [Submodule.coe_inner]
    show ⟪E (sd • σ (Formalism.REAL.toMK kk) w), (y : H)⟫_ℂ = _
    rw [hE.2.1, orth_proj_fix hE y.2, inner_smul_left]
    show (starRingEnd ℂ) ((Real.sqrt dn : ℝ) : ℂ) * _ = _
    rw [Complex.conj_ofReal]
  have gen : ∀ X' : Matrix (Fin n) (Fin n) ℂ, Integrable (d30f ε lam σ w X') (Formalism.REAL.muK ε) → ∀ x y : S,
      ⟪(x : H), ((dn : ℂ) • ∫ kk, d30f ε lam σ w X' kk ∂(Formalism.REAL.muK ε)) (y : H)⟫_ℂ =
        ∫ kk, ((wtF lam X' (Formalism.REAL.toMK kk) : ℝ) : ℂ) * (inner ℂ x (v kk) * inner ℂ (v kk) y)
          ∂(Formalism.REAL.muK ε) := by
    intro X' hi x y
    rw [_root_.smul_apply, inner_smul_right, inner_integral_pull ε lam σ w X' hi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with kk
    rw [hv1, hv2, ← hsd]
    ring
  have key := Formalism.HermitianLatticeCounting.Final.S7.decay_right_side n ε (oneBasedParam lam) h (Formalism.REAL.KG ε) S (Formalism.REAL.muK ε)
    (fun kk => Formalism.REAL.toMK kk) v X A
    (by
      intro i h1 h2
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [one_based_param_succ lam ⟨j + 1, h2⟩, one_based_param_succ lam ⟨j, by omega⟩]
      exact hlam.1 (Fin.lt_def.2 (by simp)))
    (by
      intro a b hba hne
      rw [one_based_param_succ, one_based_param_succ]
      have h1 := hgap a b hne
      have h2 : lam a < lam b := hlam.1 hba
      rw [abs_of_neg (by linarith)] at h1
      linarith)
    (fun kk => ⟨kk.2.1, fun a b hab => compact_block_diagonal ε _ kk.2 a b hab⟩)
    (hermitian_of_mem_p ε X hX).1 (hermitian_of_mem_p ε X hX).2
    (by
      intro x y
      have h1 := gen 0 hi0 x y
      rw [← hF0, hE0, orth_proj_fix hE y.2] at h1
      rw [Submodule.coe_inner, h1]
      apply integral_congr_ae
      filter_upwards with kk
      rw [weight_at_zero_eq_one lam _ kk.2.1]
      simp)
    (by
      intro x y
      have h1 := gen X hiX x y
      rw [← hFX] at h1
      rw [Submodule.coe_inner]
      show ⟪(x : H), (E ∘L σ (NormedSpace.exp X) ∘L E) (y : H)⟫_ℂ = _
      rw [h1]
      apply integral_congr_ae
      filter_upwards with kk
      show _ = ((∏ i ∈ Ico 1 n, (Formalism.NuclearRankWeightBounds.D.lead ((Formalism.REAL.toMK kk).conjTranspose * NormedSpace.exp X *
        Formalism.REAL.toMK kk) i).re ^ (-(oneBasedParam lam i - oneBasedParam lam (i + 1) + 1)) : ℝ) : ℂ) * _
      rw [weight_one_based_eq lam X _ kk.2.1])
  have hAB : ‖E ∘L σ (NormedSpace.exp X) ∘L E‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro y
    have e1 : (E ∘L σ (NormedSpace.exp X) ∘L E) y = ((A ⟨E y, orth_proj_mem hE y⟩ : S) : H) := by
      show E (σ (NormedSpace.exp X) (E y)) = E (σ (NormedSpace.exp X) (E (E y)))
      rw [orth_proj_fix hE (orth_proj_mem hE y)]
    rw [e1]
    refine le_trans (A.le_opNorm ⟨E y, orth_proj_mem hE y⟩) ?_
    exact mul_le_mul_of_nonneg_left (orth_proj_norm_le hE y) (norm_nonneg A)
  refine le_trans hAB (le_of_le_of_eq key ?_)
  unfold Formalism.HermitianLatticeCounting.S7.decExp decBound Formalism.NuclearRankWeightBounds.D.hs Formalism.NuclearRankWeightBounds.D.q0 pOf qOf Formalism.REAL.hs
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  ring

end Core2

theorem decay_of_formula (D : Formalism.BasicNotions.D7) : IntegralityFromMetric D := by
  intro hF
  unfold DiscreteSeriesLowestKTypeFormula at hF
  unfold DiscreteSeriesDecayBound
  intro n ε lam hlam H _ _ _ σ hσ E hE h hgap hth k X hk hX
  obtain ⟨w, hw⟩ := exists_highest_weight_unit ε lam σ hσ
  have hrep : IsURepOn (UJset ε) σ := hσ.2.2.1
  have h0P : Formalism.REAL.inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨by simp [Formalism.REAL.inG], by simp⟩
  have hcore := projected_exp_estimate ε lam hlam σ hrep E _ hE w _ h hgap X hX
    (hF n ε lam hlam H σ hσ E hE w hw h hgap hth X hX).1
    (hF n ε lam hlam H σ hσ E hE w hw h hgap hth 0 h0P).1
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hXh : X.conjTranspose = X := (hermitian_of_mem_p ε X hX).1
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hJJ
  have hconjX : Formalism.REAL.Jm ε * X * (Formalism.REAL.Jm ε)⁻¹ = -X := by
    rw [hJinv, Matrix.mul_assoc, hX.2, Matrix.mul_neg, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJexp : Formalism.REAL.Jm ε * NormedSpace.exp X = NormedSpace.exp (-X) * Formalism.REAL.Jm ε := by
    have hU : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
    rw [← hconjX, Matrix.exp_conj _ _ hU, hJinv]
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hinvexp : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hexpU : NormedSpace.exp X ∈ UJset ε := by
    show Formalism.REAL.inUJ ε (NormedSpace.exp X)
    unfold Formalism.REAL.inUJ
    rw [← Matrix.exp_conjTranspose, hXh, Matrix.mul_assoc, hJexp, ← Matrix.mul_assoc, hinvexp,
      Matrix.one_mul]
  have hkU : k ∈ UJset ε := by
    obtain ⟨hu, hc⟩ := hk
    have hu1 : k.conjTranspose * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show Formalism.REAL.inUJ ε k
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hsplit : σ (k * NormedSpace.exp X) = (σ k).comp (σ (NormedSpace.exp X)) :=
    hrep.1.2 k hkU _ hexpU
  have hcomm := orth_proj_commute_compact ε σ hrep hE (lowest_K_type_stable ε lam σ) k hk
  have hnk : ‖σ k‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp [hrep.2.1 k hkU v])
  have heq : E.comp ((σ (k * NormedSpace.exp X)).comp E) =
      (σ k).comp (E ∘L σ (NormedSpace.exp X) ∘L E) := by
    rw [hsplit]
    ext v
    have hc := congrArg (fun F : H →L[ℂ] H => F (σ (NormedSpace.exp X) (E v))) hcomm
    simpa using hc
  rw [heq]
  calc ‖(σ k).comp (E ∘L σ (NormedSpace.exp X) ∘L E)‖
      ≤ ‖σ k‖ * ‖E ∘L σ (NormedSpace.exp X) ∘L E‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖E ∘L σ (NormedSpace.exp X) ∘L E‖ := by gcongr
    _ = ‖E ∘L σ (NormedSpace.exp X) ∘L E‖ := one_mul _
    _ ≤ _ := hcore

theorem family_lowest_K_type_positivity {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyPositivityOfLowestKTypeFormula Fm := by
  intro ha h0 x i
  exact lowest_K_type_positivity (Fm.D x i) (ha x i) (h0 x i)

theorem family_decay_of_formula {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : PeriodFamilyStatement Fm := by
  intro h0 x i
  exact decay_of_formula (Fm.D x i) (h0 x i)

theorem family_decay_q_form_of_decay {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilyDiscreteSeriesDecay Fm) : FamilyDecayMinusSigns Fm := by
  intro x i
  exact decay_q_form_of_decay (Fm.D x i) (h x i)

section Poly

variable {n : ℕ}

theorem hilbert_schmidt_polar_bound (k X : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hX : X.IsHermitian) :
    Formalism.REAL.hs (k * NormedSpace.exp X) ≤ (n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 := by
  have h1 := (Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.polarInv n k X hk hX).2.2.2
  have h2 := h1.trace_nonneg
  have h3 : ∀ g : Matrix (Fin n) (Fin n) ℂ, (g.conjTranspose * g).trace = ((Formalism.REAL.hs g : ℝ) : ℂ) := by
    intro g
    unfold Formalism.REAL.hs Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    push_cast
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact Complex.conj_mul' _
  rw [Matrix.trace_sub, h3, Matrix.trace_smul, Matrix.trace_one] at h2
  have e : Formalism.NuclearRankWeightBounds.D.hs X = Real.sqrt (Formalism.REAL.hs X) := rfl
  rw [e] at h2
  have h5 : (Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 : ℝ) • ((Fintype.card (Fin n) : ℕ) : ℂ) -
      ((Formalism.REAL.hs (k * NormedSpace.exp X) : ℝ) : ℂ) =
      (((n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 - Formalism.REAL.hs (k * NormedSpace.exp X) : ℝ) : ℂ) := by
    rw [Complex.real_smul, Fintype.card_fin]
    push_cast
    ring
  rw [h5] at h2
  have h6 := Complex.zero_le_real.1 h2
  linarith

end Poly

theorem poly_decay_of_decay_statement (D : Formalism.BasicNotions.D7) (h1 : DiscreteSeriesDecayBound D) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → 1 ≤ min (pOf ε) (qOf ε) →
      ∀ w : H, IsLowUnit ε lam σ w → ∀ g ∈ UJset ε,
        ‖⟪w, σ g w⟫_ℂ‖ ≤
          Real.sqrt n ^ (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)))) *
            Real.exp (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) /
              Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) *
            Real.sqrt (Formalism.REAL.hs g) ^ (-(h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))))) := by
  intro n ε lam hlam H _ _ _ σ hσ E hE h hgap hth hq w hw g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
  have hh : 0 ≤ h := le_trans (by positivity) hth
  set q0 : ℝ := ((min (pOf ε) (qOf ε) : ℕ) : ℝ) with hq0
  have hq0' : (1 : ℝ) ≤ q0 := by rw [hq0]; exact_mod_cast hq
  set s : ℝ := Real.sqrt (2 * q0) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  set a : ℝ := h / (8 * s) with ha
  have ha0 : 0 ≤ a := by positivity
  set t : ℝ := Real.sqrt (Formalism.REAL.hs X) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hsX : Formalism.REAL.hs X = t ^ 2 := by
    rw [ht, Real.sq_sqrt]; unfold Formalism.REAL.hs; positivity

  have c1 := Formalism.HermitianLatticeCounting.Final.S7.coeffLeOp H E (σ (k * NormedSpace.exp X)) w hE.2.1 (orth_proj_fix hE hw.2) hw.1
  have c2 := h1 n ε lam hlam H σ hσ E hE h hgap hth k X hk hX
  have c3 : ‖⟪w, σ (k * NormedSpace.exp X) w⟫_ℂ‖ ≤ decBound (min (pOf ε) (qOf ε)) h X := le_trans c1 c2
  refine le_trans c3 ?_

  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have : pOf ε = 0 := by unfold pOf; simp
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have g1 := hilbert_schmidt_polar_bound k X hk.1 (hermitian_of_mem_p ε X hX).1
  have g2 : Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) ≤ Real.sqrt n * Real.exp t := by
    rw [← Real.sqrt_sq (Real.exp_pos t).le, ← Real.sqrt_mul hnR.le]
    exact Real.sqrt_le_sqrt g1
  have g3 : 0 < Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) := by
    apply Real.sqrt_pos.2
    have hnn : 0 ≤ Formalism.REAL.hs (k * NormedSpace.exp X) := by unfold Formalism.REAL.hs; positivity
    rcases hnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hz : k * NormedSpace.exp X = 0 := by
        ext i j
        unfold Formalism.REAL.hs at heq
        have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))).1
          heq.symm i (Finset.mem_univ _)
        have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 e1 j (Finset.mem_univ _)
        simpa using e2
      have hJ : Formalism.REAL.Jm ε = 0 := by
        have : Formalism.REAL.inUJ ε (k * NormedSpace.exp X) := hg
        unfold Formalism.REAL.inUJ at this
        rw [hz] at this
        simpa using this.symm
      have h11 := Formalism.REAL.Jm_mul_self ε
      rw [hJ, Matrix.mul_zero] at h11
      have := congrFun (congrFun h11 ⟨0, hn⟩) ⟨0, hn⟩
      simp at this
  have g4 : (Real.sqrt n * Real.exp t) ^ (-a) ≤ Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos g3 g2 (by linarith)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have g5 : Real.sqrt n ^ a * Real.exp (a / s) * (Real.sqrt n * Real.exp t) ^ (-a) = Real.exp (a / s - a * t) := by
    rw [Real.mul_rpow hsn.le (Real.exp_pos t).le, Real.rpow_neg hsn.le, ← Real.exp_mul, Real.exp_sub,
      show t * -a = -(a * t) by ring, Real.exp_neg]
    have : Real.sqrt n ^ a ≠ 0 := (Real.rpow_pos_of_pos hsn a).ne'
    field_simp
  refine le_trans ?_ (mul_le_mul_of_nonneg_left g4 (by positivity))
  rw [g5]
  unfold decBound
  apply Real.exp_le_exp.2
  rw [hsX, Real.sqrt_sq ht0, ← hq0, ← hs]
  have hc : 0 ≤ h / 8 := by positivity
  have ea : a = h / 8 / s := by rw [ha]; field_simp
  have m1 : a * t - a / s ≤ h / 8 * (t / s) := by
    have : h / 8 * (t / s) = a * t := by rw [ea]; field_simp
    rw [this]
    have : 0 ≤ a / s := by positivity
    linarith
  have m2 : a * t - a / s ≤ h / 8 * t ^ 2 := by
    have e1 : a * t - a / s = h / 8 * (t / s - 1 / s ^ 2) := by rw [ea]; field_simp
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hc
    have : 0 ≤ (t - 1 / (2 * s)) ^ 2 + 3 / (4 * s ^ 2) := by positivity
    have e2 : (t - 1 / (2 * s)) ^ 2 + 3 / (4 * s ^ 2) = t ^ 2 - t / s + 1 / s ^ 2 := by field_simp; ring
    linarith
  have m3 : a * t - a / s ≤ h / 8 * min (t ^ 2) (t / s) := by
    rcases min_cases (t ^ 2) (t / s) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
    · exact m2
    · exact m1
  linarith

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem K_type_map_of_intertwiner (ε : Fin n → Bool) (σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (U V : H →L[ℂ] H)
    (hUV : ∀ v, U (V v) = v) (hVU : ∀ v, V (U v) = v)
    (hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v, σ₁ g (U v) = U (σ₂ g v)) (Λ : Fin n → ℝ) (S : Submodule ℂ H)
    (hS : IsKTypeOf ε σ₂ Λ S) : IsKTypeOf ε σ₁ Λ (S.map (U : H →ₗ[ℂ] H)) := by
  obtain ⟨hfd, hst, hirr, ⟨u0, hu0S, hu0, hw0⟩, hdom⟩ := hS
  have hUVid : (U : H →ₗ[ℂ] H).comp (V : H →ₗ[ℂ] H) = LinearMap.id := LinearMap.ext fun v => hUV v
  have hback : ∀ g ∈ Formalism.REAL.Kset ε, ∀ s, σ₂ g (V s) = V (σ₁ g s) := by
    intro g hg s
    have h := hint g hg (V s)
    rw [hUV] at h
    rw [h, hVU]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    infer_instance
  · intro g hg v hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [ContinuousLinearMap.coe_coe, hint g hg u]
    exact Submodule.mem_map_of_mem (hst g hg u hu)
  · intro S' hle hS'
    have hT : S'.map (V : H →ₗ[ℂ] H) ≤ S := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := ht
      obtain ⟨u, hu, rfl⟩ := hle hs
      simpa [hVU] using hu
    have hTst : IsKStableOn ε σ₂ (S'.map (V : H →ₗ[ℂ] H)) := by
      intro g hg t ht
      obtain ⟨s, hs, rfl⟩ := ht
      rw [ContinuousLinearMap.coe_coe, hback g hg s]
      exact Submodule.mem_map_of_mem (hS' g hg s hs)
    have hround : (S'.map (V : H →ₗ[ℂ] H)).map (U : H →ₗ[ℂ] H) = S' := by
      rw [← Submodule.map_comp, hUVid, Submodule.map_id]
    rcases hirr _ hT hTst with h | h
    · left
      rw [← hround, h, Submodule.map_bot]
    · right
      rw [← hround, h]
  · refine ⟨U u0, Submodule.mem_map_of_mem hu0S, ?_, ?_⟩
    · intro h
      apply hu0
      rw [← hVU u0, h, map_zero]
    · intro θ hθ
      rw [hint _ hθ u0, hw0 θ hθ, map_smul]
  · intro μ v hv hv0 hw
    obtain ⟨u, hu, rfl⟩ := hv
    refine hdom μ u hu ?_ ?_
    · intro h
      apply hv0
      rw [h, map_zero]
    · intro θ hθ
      have h := hw θ hθ
      rw [ContinuousLinearMap.coe_coe, hint _ hθ u] at h
      have h2 := congrArg (fun z => V z) h
      simp only [hVU, map_smul] at h2
      exact h2

theorem lowest_K_type_map_of_intertwiner (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (U V : H →L[ℂ] H) (hUV : ∀ v, U (V v) = v) (hVU : ∀ v, V (U v) = v)
    (hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v, σ₁ g (U v) = U (σ₂ g v)) (w : H) (hw : w ∈ lowKSub ε lam σ₂) :
    U w ∈ lowKSub ε lam σ₁ := by
  have hle : lowKSub ε lam σ₂ ≤ (lowKSub ε lam σ₁).comap (U : H →ₗ[ℂ] H) := by
    unfold lowKSub
    refine sSup_le fun S hS => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact (le_sSup (show S.map (U : H →ₗ[ℂ] H) ∈ {S | IsKTypeOf ε σ₁ (Formalism.QuantumDeterminants.lowK ε lam) S} from
      K_type_map_of_intertwiner ε σ₁ σ₂ U V hUV hVU hint (Formalism.QuantumDeterminants.lowK ε lam) S hS) :
        S.map (U : H →ₗ[ℂ] H) ≤ lowKSub ε lam σ₁) (Submodule.mem_map_of_mem hx)
  exact hle hw

theorem trace_conj_mul_eq_hilbert_schmidt (g : Matrix (Fin n) (Fin n) ℂ) : (g.conjTranspose * g).trace = ((Formalism.REAL.hs g : ℝ) : ℂ) := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem hs_unitary_conj (P x : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.hs (P * x * P.conjTranspose) = Formalism.REAL.hs x := by
  have hPP : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hP
  have key : ((P * x * P.conjTranspose).conjTranspose * (P * x * P.conjTranspose)).trace
      = (x.conjTranspose * x).trace := by
    have e : (P * x * P.conjTranspose).conjTranspose * (P * x * P.conjTranspose)
        = P * (x.conjTranspose * x * P.conjTranspose) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc P * (x.conjTranspose * P.conjTranspose) * (P * x * P.conjTranspose)
          = P * x.conjTranspose * (P.conjTranspose * P) * x * P.conjTranspose := by
            simp only [Matrix.mul_assoc]
        _ = P * (x.conjTranspose * x * P.conjTranspose) := by
            rw [hPP, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc (x.conjTranspose * x), hPP, Matrix.mul_one]
  rw [trace_conj_mul_eq_hilbert_schmidt, trace_conj_mul_eq_hilbert_schmidt] at key
  exact_mod_cast key

end Conj

section Bessel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem star_projection_is_orth_proj [CompleteSpace H] (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    IsOrthProjOnto S.starProjection S := by
  have hr : LinearMap.range (S.starProjection : H →ₗ[ℂ] H) = S := by
    ext x
    simp
  refine ⟨?_, ?_, hr⟩
  · ext x
    rw [ContinuousLinearMap.comp_apply]
    have hm : S.starProjection x ∈ LinearMap.range (S.starProjection : H →ₗ[ℂ] H) :=
      LinearMap.mem_range_self _ x
    rw [hr] at hm
    first
      | exact Submodule.starProjection_eq_self_iff.mpr hm
      | simp only [Submodule.starProjection_apply, Submodule.orthogonalProjection_mem_subspace_eq_self]
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right S x y

theorem lowest_unit_cayley_indep (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P')
    (hrep : IsURepOn (UJset ε) (fun g => σ (P⁻¹ * g * P))) (w : H)
    (hw : IsLowUnit ε lam (fun g => σ (P'⁻¹ * g * P')) w) : IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w := by
  obtain ⟨⟨-, hPJ⟩, hPu⟩ := hP
  obtain ⟨⟨-, hPJ'⟩, hPu'⟩ := hP'
  have hP1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hP2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hP1' : P'.conjTranspose * P' = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu'
  have hP2' : P' * P'.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hPu'
  have hPi : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv hP1
  have hPi' : P'⁻¹ = P'.conjTranspose := Matrix.inv_eq_left_inv hP1'
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = P' * P.conjTranspose := ⟨_, rfl⟩
  have hQh : Q.conjTranspose = P * P'.conjTranspose := by
    rw [hQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hQ1 : Q.conjTranspose * Q = 1 := by
    rw [hQh, hQ]
    calc P * P'.conjTranspose * (P' * P.conjTranspose)
        = P * (P'.conjTranspose * P') * P.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP1', Matrix.mul_one, hP2]
  have hQ2 : Q * Q.conjTranspose = 1 := by
    rw [hQh, hQ]
    calc P' * P.conjTranspose * (P * P'.conjTranspose)
        = P' * (P.conjTranspose * P) * P'.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP1, Matrix.mul_one, hP2']
  have hEq : P.conjTranspose * Formalism.REAL.Jm ε * P = P'.conjTranspose * Formalism.REAL.Jm ε * P' := by
    rw [hPJ, hPJ']
  have hQJ : Q * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q := by
    rw [hQ]
    calc P' * P.conjTranspose * Formalism.REAL.Jm ε
        = P' * (P.conjTranspose * Formalism.REAL.Jm ε * P) * P.conjTranspose := by
          simp only [Matrix.mul_assoc, hP2, Matrix.mul_one]
      _ = P' * (P'.conjTranspose * Formalism.REAL.Jm ε * P') * P.conjTranspose := by rw [hEq]
      _ = Formalism.REAL.Jm ε * (P' * P.conjTranspose) := by
          simp only [← Matrix.mul_assoc, hP2', Matrix.one_mul]
  have KinU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    have hu1 : g.conjTranspose * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show Formalism.REAL.inUJ ε g
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have Kstar : ∀ g ∈ Formalism.REAL.Kset ε, g.conjTranspose ∈ Formalism.REAL.Kset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    have hu1 : g.conjTranspose * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have hu2 : g * g.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
    refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hu1), ?_⟩
    calc g.conjTranspose * Formalism.REAL.Jm ε
        = g.conjTranspose * Formalism.REAL.Jm ε * (g * g.conjTranspose) := by rw [hu2, Matrix.mul_one]
      _ = g.conjTranspose * (Formalism.REAL.Jm ε * g) * g.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = g.conjTranspose * (g * Formalism.REAL.Jm ε) * g.conjTranspose := by rw [← hc]
      _ = g.conjTranspose * g * Formalism.REAL.Jm ε * g.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * g.conjTranspose := by rw [hu1, Matrix.one_mul]
  have UJmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := by
    intro a ha b hb
    have ha' : Formalism.REAL.inUJ ε a := ha
    have hb' : Formalism.REAL.inUJ ε b := hb
    show Formalism.REAL.inUJ ε (a * b)
    unfold Formalism.REAL.inUJ at ha' hb' ⊢
    rw [Matrix.conjTranspose_mul]
    calc b.conjTranspose * a.conjTranspose * Formalism.REAL.Jm ε * (a * b)
        = b.conjTranspose * (a.conjTranspose * Formalism.REAL.Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hQK : Q ∈ Formalism.REAL.Kset ε := ⟨Matrix.mem_unitaryGroup_iff.mpr (by
      rw [Matrix.star_eq_conjTranspose]
      exact hQ2), hQJ⟩
  have hQhK : Q.conjTranspose ∈ Formalism.REAL.Kset ε := Kstar Q hQK
  have hQU : Q ∈ UJset ε := KinU Q hQK
  have hQhU : Q.conjTranspose ∈ UJset ε := KinU _ hQhK
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P)) :=
    fun a ha b hb => hrep.1.2 a ha b hb
  have hone : σ (P⁻¹ * 1 * P) = 1 := hrep.1.1
  have hUV : ∀ v, σ (P⁻¹ * Q * P) (σ (P⁻¹ * Q.conjTranspose * P) v) = v := by
    intro v
    have h := hmul Q hQU _ hQhU
    rw [hQ2, hone] at h
    have h' := congrArg (fun F : H →L[ℂ] H => F v) h
    simpa using h'.symm
  have hVU : ∀ v, σ (P⁻¹ * Q.conjTranspose * P) (σ (P⁻¹ * Q * P) v) = v := by
    intro v
    have h := hmul _ hQhU Q hQU
    rw [hQ1, hone] at h
    have h' := congrArg (fun F : H →L[ℂ] H => F v) h
    simpa using h'.symm
  have hconj : ∀ g, P'⁻¹ * g * P' = P⁻¹ * (Q.conjTranspose * g * Q) * P := by
    intro g
    rw [hPi, hPi', hQh, hQ]
    calc P'.conjTranspose * g * P'
        = (P.conjTranspose * P) * P'.conjTranspose * g * P' * (P.conjTranspose * P) := by
          rw [hP1, Matrix.one_mul, Matrix.mul_one]
      _ = P.conjTranspose * (P * P'.conjTranspose * g * (P' * P.conjTranspose)) * P := by
          simp only [Matrix.mul_assoc]
  have hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v,
      σ (P⁻¹ * g * P) (σ (P⁻¹ * Q * P) v) = σ (P⁻¹ * Q * P) (σ (P'⁻¹ * g * P') v) := by
    intro g hg v
    have hgU := KinU g hg
    have h1 := hmul Q hQU _ (UJmul _ (UJmul _ hQhU _ hgU) _ hQU)
    have h2 := hmul g hgU Q hQU
    have e : Q * (Q.conjTranspose * g * Q) = g * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ2, Matrix.one_mul]
    rw [e] at h1
    rw [hconj g]
    have h1' := congrArg (fun F : H →L[ℂ] H => F v) h1
    have h2' := congrArg (fun F : H →L[ℂ] H => F v) h2
    simp only [ContinuousLinearMap.comp_apply] at h1' h2'
    rw [← h1', h2']
  obtain ⟨hn, hwm⟩ := hw
  refine ⟨hn, ?_⟩
  have hUw := lowest_K_type_map_of_intertwiner ε lam (fun g => σ (P⁻¹ * g * P)) (fun g => σ (P'⁻¹ * g * P'))
    (σ (P⁻¹ * Q * P)) (σ (P⁻¹ * Q.conjTranspose * P)) hUV hVU hint w hwm
  have hback := lowest_K_type_stable ε lam (fun g => σ (P⁻¹ * g * P)) _ hQhK _ hUw
  simpa only [hVU] using hback

theorem poly_decay_indefinite_unitary (D : Formalism.BasicNotions.D7) (ha2 : adm2 D) (h1 : DiscreteSeriesDecayBound D) (k r : ℕ)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (hσ : IsDSHpk k r ε lam σ)
    (h : ℝ) (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hth : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hq : 1 ≤ min (pOf ε) (qOf ε)) (w : H) (hw : IsLowUnitH k r ε lam σ w)
    (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖⟪w, σ x w⟫_ℂ‖ ≤
      Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)))) *
        Real.exp (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) /
          Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) *
        Real.sqrt (Formalism.REAL.hs x) ^ (-(h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))))) := by
  obtain ⟨P, hPC, hDS⟩ := hσ
  obtain ⟨P', hP'C, hLU'⟩ := hw
  have hPu := hPC.2
  have hPJ : P.conjTranspose * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hPC.1.2
  have hP1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hP2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hPi : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv hP1
  haveI : CompleteSpace H := hDS.1
  have hLU := lowest_unit_cayley_indep k r ε lam σ P P' hPC hP'C hDS.2.2.1 w hLU'
  unfold adm2 at ha2
  haveI : FiniteDimensional ℂ (lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :=
    (ha2 (2 * r + k + 1) ε lam hlam H (fun g => σ (P⁻¹ * g * P)) hDS).1.1
  obtain ⟨E, hE⟩ : ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :=
    ⟨_, star_projection_is_orth_proj _⟩
  have hmem : P * x * P.conjTranspose ∈ UJset ε := by
    show Formalism.REAL.inUJ ε (P * x * P.conjTranspose)
    unfold Formalism.REAL.inUJ
    have hx' : x.conjTranspose * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P * (x.conjTranspose * P.conjTranspose) * Formalism.REAL.Jm ε * (P * x * P.conjTranspose)
        = P * (x.conjTranspose * (P.conjTranspose * Formalism.REAL.Jm ε * P) * x) * P.conjTranspose := by
          simp only [Matrix.mul_assoc]
      _ = P * (P.conjTranspose * Formalism.REAL.Jm ε * P) * P.conjTranspose := by rw [hPJ, hx']
      _ = Formalism.REAL.Jm ε := by
          simp only [← Matrix.mul_assoc, hP2, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hP2, Matrix.mul_one]
  have e1 : P⁻¹ * (P * x * P.conjTranspose) * P = x := by
    rw [hPi]
    simp only [← Matrix.mul_assoc, hP1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hP1, Matrix.mul_one]
  have e2 : Formalism.REAL.hs (P * x * P.conjTranspose) = Formalism.REAL.hs x := hs_unitary_conj P x hPu
  have hb := poly_decay_of_decay_statement D h1 (2 * r + k + 1) ε lam hlam H (fun g => σ (P⁻¹ * g * P)) hDS
    E hE h hgap hth hq w hLU (P * x * P.conjTranspose) hmem
  rw [e1, e2] at hb
  exact hb

end Bessel

end Formalism.MainNotions.BridgeLemma

end
