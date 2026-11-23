import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace MainStatements.Flath2

def clampFn (ε t : ℝ) : ℝ := max (-ε) (min t ε)

def cutFn (ε t : ℝ) : ℝ := t - clampFn ε t

def invFn (ε t : ℝ) : ℝ := t / max (t ^ 2) (ε ^ 2)

theorem continuous_clampFn (ε : ℝ) : Continuous (clampFn ε) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuous_cutFn (ε : ℝ) : Continuous (cutFn ε) :=
  continuous_id.sub (continuous_clampFn ε)

theorem continuous_invFn {ε : ℝ} (hε : 0 < ε) : Continuous (invFn ε) := by
  have h : ∀ t : ℝ, max (t ^ 2) (ε ^ 2) ≠ 0 := fun t =>
    (lt_of_lt_of_le (by positivity : (0 : ℝ) < ε ^ 2) (le_max_right _ _)).ne'
  exact Continuous.div continuous_id ((continuous_pow 2).max continuous_const) h

theorem abs_clampFn_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : |clampFn ε t| ≤ ε :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem mul_invFn_mul_cutFn {ε : ℝ} (hε : 0 < ε) (t : ℝ) : t * invFn ε t * cutFn ε t = cutFn ε t := by
  unfold invFn cutFn clampFn
  rcases le_or_gt t ε with h1 | h1
  · rcases le_or_gt (-ε) t with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2, sub_self, mul_zero]
    · have ht : ε ^ 2 < t ^ 2 := by nlinarith
      have t0 : t ≠ 0 := by linarith
      rw [max_eq_left ht.le, ← mul_div_assoc, ← pow_two, div_self (pow_ne_zero 2 t0), one_mul]
  · have ht : ε ^ 2 < t ^ 2 := by nlinarith
    have t0 : t ≠ 0 := by linarith
    rw [max_eq_left ht.le, ← mul_div_assoc, ← pow_two, div_self (pow_ne_zero 2 t0), one_mul]

section

variable {G : Type} [Group G] [TopologicalSpace G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ρ : G →* (H →L[ℂ] H)}

theorem exists_irred_of_finiteDimensional (hρ : IsUnitaryRep ρ) {W E : Submodule ℂ H} (hW : IsSubrep ρ W)
    (hE : FiniteDimensional ℂ E)
    (hS : ∀ (Y : Submodule ℂ H) [Y.HasOrthogonalProjection], IsSubrep ρ Y → Y ≤ W →
      ∀ x ∈ E, Y.starProjection x ∈ E)
    (hWE : W ⊓ E ≠ ⊥) : ∃ X ≤ W, IsIrredSubrep ρ X := by
  obtain ⟨U, ⟨hU, hUW, hUE⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun U => IsSubrep ρ U ∧ U ≤ W ∧ U ⊓ E ≠ ⊥) (fun U => Module.finrank ℂ ↥(U ⊓ E)) ⟨W, hW, le_rfl, hWE⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUE
  let X := sInf {Y | IsSubrep ρ Y ∧ x ∈ Y}
  have hX : IsSubrep ρ X := ⟨by
    rw [Submodule.coe_sInf]
    exact isClosed_biInter fun Y hY => hY.1.1,
    fun g v hv => Submodule.mem_sInf.2 fun Y hY => hY.1.2 g v (Submodule.mem_sInf.1 hv Y hY)⟩
  have hxX : x ∈ X := Submodule.mem_sInf.2 fun Y hY => hY.2
  have hXU : X ≤ U := sInf_le ⟨hU, hx.1⟩
  refine ⟨X, hXU.trans hUW, hX, (Submodule.ne_bot_iff _).2 ⟨x, hxX, hx0⟩, fun Y hYX hY => ?_⟩
  have := hY.completeSpace
  by_cases hy : Y.starProjection x = 0
  · have : X ≤ Yᗮ := sInf_le ⟨hY.orthogonal hρ, (Submodule.starProjection_apply_eq_zero_iff _).1 hy⟩
    exact .inl (le_bot_iff.1 ((le_inf le_rfl (hYX.trans this)).trans (Submodule.inf_orthogonal_eq_bot _).le))
  · have h1 : Y ⊓ E ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨_, ⟨Y.starProjection_apply_mem x,
      hS Y hY (hYX.trans (hXU.trans hUW)) x hx.2⟩, hy⟩
    have h2 : Y ⊓ E ≤ U ⊓ E := inf_le_inf_right _ (hYX.trans hXU)
    have : FiniteDimensional ℂ ↥(U ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right
    have h3 := Submodule.eq_of_le_of_finrank_le h2
      (hmin ⟨hY, hYX.trans (hXU.trans hUW), h1⟩ (Submodule.finrank_mono h2))
    exact .inr (le_antisymm hYX (sInf_le ⟨hY, (h3 ▸ hx : x ∈ Y ⊓ E).1⟩))

theorem exists_irred_of_compact (hρ : IsUnitaryRep ρ) {W : Submodule ℂ H} (hW : IsSubrep ρ W)
    [W.HasOrthogonalProjection] (A : H →L[ℂ] H) (hA : IsCompactOperator A) (hA0 : A ≠ 0)
    (hAW : ∀ x, A (W.starProjection x) = A x)
    (hAY : ∀ (Y : Submodule ℂ H) [Y.HasOrthogonalProjection], IsSubrep ρ Y → Y ≤ W →
      ∀ x, A (Y.starProjection x) = Y.starProjection (A x)) :
    ∃ X ≤ W, IsIrredSubrep ρ X := by
  let T := ContinuousLinearMap.adjoint A ∘L A
  have hTc : IsCompactOperator T := hA.clm_comp (ContinuousLinearMap.adjoint A)
  have hTs : (T : H →ₗ[ℂ] H).IsSymmetric := fun x y => by
    simp [T, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  have hTA : ∀ x, T x = 0 → A x = 0 := fun x e => by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_right,
      show ContinuousLinearMap.adjoint A (A x) = 0 from e, inner_zero_right]
  have hT0 : T ≠ 0 := fun e => hA0 (ContinuousLinearMap.ext fun x => hTA x (by rw [e]; rfl))
  obtain ⟨c, hc1, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra! hn
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).1 hn)
  have hTY : ∀ (Y : Submodule ℂ H) [Y.HasOrthogonalProjection], IsSubrep ρ Y → Y ≤ W →
      ∀ x, T (Y.starProjection x) = Y.starProjection (T x) := by
    intro Y _ hY hYW x
    have h1 : ∀ z, ContinuousLinearMap.adjoint A (Y.starProjection z) =
        Y.starProjection (ContinuousLinearMap.adjoint A z) := fun z =>
      ext_inner_left ℂ fun y => by
        calc ⟪y, ContinuousLinearMap.adjoint A (Y.starProjection z)⟫_ℂ = ⟪A y, Y.starProjection z⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪Y.starProjection (A y), z⟫_ℂ := (Submodule.inner_starProjection_left_eq_right _ _ _).symm
          _ = ⟪A (Y.starProjection y), z⟫_ℂ := by rw [hAY Y hY hYW]
          _ = ⟪Y.starProjection y, ContinuousLinearMap.adjoint A z⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪y, Y.starProjection (ContinuousLinearMap.adjoint A z)⟫_ℂ :=
              Submodule.inner_starProjection_left_eq_right _ _ _
    show ContinuousLinearMap.adjoint A (A (Y.starProjection x)) =
      Y.starProjection (ContinuousLinearMap.adjoint A (A x))
    rw [hAY Y hY hYW, h1]
  obtain ⟨x, hx, hx0⟩ := hc1.exists_hasEigenvector
  have hTx : T x = c • x := Module.End.mem_eigenspace_iff.1 hx
  refine exists_irred_of_finiteDimensional hρ hW (ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0)
    ?_ ?_
  · intro Y _ hY hYW y hy
    have hy' : T y = c • y := Module.End.mem_eigenspace_iff.1 hy
    refine Module.End.mem_eigenspace_iff.2 ?_
    change T (Y.starProjection y) = c • Y.starProjection y
    rw [hTY Y hY hYW, hy', map_smul]
  · refine (Submodule.ne_bot_iff _).2 ⟨W.starProjection x, ⟨W.starProjection_apply_mem x, ?_⟩, fun e => hx0 ?_⟩
    · refine Module.End.mem_eigenspace_iff.2 ?_
      change T (W.starProjection x) = c • W.starProjection x
      rw [hTY W hW le_rfl, hTx, map_smul]
    · have h1 : A x = 0 := by rw [← hAW, e, map_zero]
      have h2 : c • x = 0 := by
        rw [← hTx]
        show ContinuousLinearMap.adjoint A (A x) = 0
        rw [h1, map_zero]
      exact (smul_eq_zero.1 h2).resolve_left hc0

theorem exists_irreducible_subrepresentation_bis (hρ : IsUnitaryRep ρ) {a Q : H →L[ℂ] H}
    (ha : ∀ S : H →L[ℂ] H, (∀ g, S * ρ g = ρ g * S) → S * a = a * S) (hQ : ∀ g, Q * ρ g = ρ g * Q)
    (hc : IsCompactOperator (a * Q)) (h0 : a * Q ≠ 0) : ∃ W, IsIrredSubrep ρ W := by

  have hQs : ∀ g, star Q * ρ g = ρ g * star Q := fun g => ContinuousLinearMap.ext fun x =>
    ext_inner_left ℂ fun y => by
      have e1 := hρ.inner_apply_left g⁻¹ y (star Q x)
      have e2 := hρ.inner_apply_left g⁻¹ (Q y) x
      rw [inv_inv] at e1 e2
      show ⟪y, star Q (ρ g x)⟫_ℂ = ⟪y, ρ g (star Q x)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint] at e1 ⊢
      rw [ContinuousLinearMap.adjoint_inner_right, ← e1, ← e2, ContinuousLinearMap.adjoint_inner_right]
      exact congrArg (fun z => ⟪z, x⟫_ℂ) (DFunLike.congr_fun (hQ g⁻¹) y).symm
  set b := Q * star Q with hbdef
  have hb : IsSelfAdjoint b := IsSelfAdjoint.mul_star_self Q
  have hbρ : ∀ g, Commute b (ρ g) := fun g => by
    show Q * star Q * ρ g = ρ g * (Q * star Q)
    rw [mul_assoc, hQs, ← mul_assoc, hQ, mul_assoc]
  have hab : IsCompactOperator (a * b) := by
    have := hc.comp_clm (star Q)
    rw [hbdef, ← mul_assoc]
    exact this
  have hsub : ∀ ε, cfc (cutFn ε) b = b - cfc (clampFn ε) b := fun ε => by
    have := cfc_sub (fun t : ℝ => t) (clampFn ε) b continuous_id.continuousOn (continuous_clampFn ε).continuousOn
    rw [cfc_id' ℝ b hb] at this
    exact this
  obtain ⟨ε, hε, hne⟩ : ∃ ε > 0, a * cfc (cutFn ε) b ≠ 0 := by
    by_contra! hn
    have key : ∀ ε > 0, ‖a * b‖ ≤ ‖a‖ * ε := fun ε hε => by
      have e1 : a * b = a * cfc (clampFn ε) b := by
        have := hn ε hε
        rw [hsub, mul_sub, sub_eq_zero] at this
        exact this
      rw [e1]
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg a))
      exact norm_cfc_le hε.le fun t _ => by rw [Real.norm_eq_abs]; exact abs_clampFn_le hε.le t
    have hab0 : a * b = 0 := by
      by_contra hne
      have hpos : 0 < ‖a * b‖ := norm_pos_iff.2 hne
      have hε : 0 < ‖a * b‖ / (2 * (‖a‖ + 1)) := by positivity
      have h1 := key _ hε
      have h2 : ‖a‖ * (‖a * b‖ / (2 * (‖a‖ + 1))) < ‖a * b‖ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg a]
      linarith
    refine h0 ((CStarRing.mul_star_self_eq_zero_iff _).1 ?_)
    have e : a * Q * star (a * Q) = a * b * star a := by
      rw [star_mul, hbdef]; simp only [mul_assoc]
    rw [e, hab0, zero_mul]
  set Gε := cfc (cutFn ε) b with hGdef
  set Hε := cfc (invFn ε) b with hHdef
  have hGρ : ∀ g, Commute Gε (ρ g) := fun g => (hbρ g).cfc_real (cutFn ε)
  have hbHG : Gε = b * Hε * Gε := by
    calc Gε = cfc (fun t => t * invFn ε t * cutFn ε t) b :=
          congrArg (fun f => cfc f b) (funext fun t => (mul_invFn_mul_cutFn hε t).symm)
      _ = cfc (fun t => t * invFn ε t) b * Gε :=
          cfc_mul (fun t => t * invFn ε t) (cutFn ε) b
            (continuous_id.mul (continuous_invFn hε)).continuousOn (continuous_cutFn ε).continuousOn
      _ = cfc (fun t : ℝ => t) b * Hε * Gε := by
          rw [cfc_mul (fun t : ℝ => t) (invFn ε) b continuous_id.continuousOn (continuous_invFn hε).continuousOn]
      _ = b * Hε * Gε := by rw [cfc_id' ℝ b hb]
  let W := (LinearMap.range (Gε : H →ₗ[ℂ] H)).topologicalClosure
  have hW : IsSubrep ρ W := isSubrep_topologicalClosure fun g v hv => by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨ρ g w, DFunLike.congr_fun (hGρ g).eq w⟩
  have := hW.completeSpace
  have hGW : ∀ v, Gε v ∈ W := fun v => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ v)
  have hle : W ≤ LinearMap.ker ((a - a * b * Hε : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ (by
      rintro _ ⟨w, rfl⟩
      refine LinearMap.mem_ker.2 ?_
      have h1 := DFunLike.congr_fun (congrArg (a * ·) hbHG) w
      change a (Gε w) - a (b (Hε (Gε w))) = 0
      rw [sub_eq_zero]
      exact h1) (ContinuousLinearMap.isClosed_ker _)
  have hAW : ∀ w ∈ W, a w = (a * b * Hε) w := fun w hw => by
    have h := LinearMap.mem_ker.1 (hle hw)
    change a w - (a * b * Hε) w = 0 at h
    exact sub_eq_zero.1 h
  set P := W.starProjection with hPdef
  have eA : a * P = a * b * Hε * P := ContinuousLinearMap.ext fun x => hAW _ (W.starProjection_apply_mem x)
  have hA : IsCompactOperator (a * P) := by
    rw [eA]
    exact (hab.comp_clm Hε).comp_clm P
  have hA0 : a * P ≠ 0 := by
    obtain ⟨v, hv⟩ : ∃ v, a (Gε v) ≠ 0 := by
      by_contra! h
      exact hne (ContinuousLinearMap.ext h)
    intro e
    apply hv
    have h1 : P (Gε v) = Gε v := Submodule.starProjection_eq_self_iff.2 (hGW v)
    have h2 := DFunLike.congr_fun e (Gε v)
    change a (P (Gε v)) = 0 at h2
    rwa [h1] at h2
  obtain ⟨X, -, hX⟩ := exists_irred_of_compact hρ hW (a * P) hA hA0
    (fun x => by
      show a (P (P x)) = a (P x)
      rw [Submodule.starProjection_eq_self_iff.2 (W.starProjection_apply_mem x)])
    (fun Y _ hY hYW x => by
      show a (P (Y.starProjection x)) = Y.starProjection (a (P x))
      rw [Submodule.starProjection_eq_self_iff.2 (hYW (Y.starProjection_apply_mem x))]
      have h1 : Y.starProjection * a = a * Y.starProjection :=
        ha _ fun g => ContinuousLinearMap.ext fun v => hY.starProjection_apply hρ g v
      have h2 : Y.starProjection (a (P x)) = a (Y.starProjection (P x)) := DFunLike.congr_fun h1 (P x)
      have h3 : Y.starProjection (P x) = Y.starProjection x :=
        DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hYW) x
      rw [h2, h3])
  exact ⟨X, hX⟩

end

theorem irredSt : IrredSt := fun _ _ _ _ _ _ _ _ hρ _ _ ha hQ hc h0 => exists_irreducible_subrepresentation_bis hρ ha hQ hc h0

end MainStatements.Flath2
