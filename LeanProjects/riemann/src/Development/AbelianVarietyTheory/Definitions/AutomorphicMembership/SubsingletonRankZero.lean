import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr.CharModel

namespace GlobalTheory.CuspRep.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E) in
omit [IsTotallyComplex E] in

def absC (s : ℂ) : HChar E := ⟨absHom E s, (absChar E s).2⟩

theorem logNorm_infId (u : (Cinf E)ˣ) : logNorm E (infId E u) = ∑ w, 2 * Real.log ‖(u : Cinf E) w‖ := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.finPart E (infId E u) = 1 := Units.ext (by
    change (1 : Af E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, logFin_one, sub_zero, logInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : ((infPart E (infId E u) : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) = infEq E u := by
    change (1 : InfiniteAdeleRing E) - infEq E 1 + infEq E u = _
    simp
  rw [h2, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]
  have h3 : ‖infEq E u w‖ = ‖(u : Cinf E) w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm) _
  rw [h3]; norm_num

theorem expo_absC (s : ℂ) (τ : E →+* ℂ) : expo (absC E s) τ = s := by
  classical
  refine expo_eq_of_exp _ τ s s fun z => ?_
  change Complex.exp (s * logNorm E (infId E (expU (atEmb τ z)))) = _
  rw [logNorm_infId, Finset.sum_eq_single (InfinitePlace.mk τ)]
  · change Complex.exp (s * ((2 * Real.log ‖Complex.exp (atEmb τ z _)‖ : ℝ) : ℂ)) = _
    rw [Complex.norm_exp, Real.log_exp, ← mul_add, Complex.add_conj]
    congr 3
    unfold atEmb
    split_ifs <;> simp
  · intro w _ hw
    change 2 * Real.log ‖Complex.exp (atEmb τ z w)‖ = 0
    simp [atEmb, hw]
  · simp

theorem infChar_absC (s : ℂ) (τ : E →+* ℂ) : (CG.ofChar (absC E s)).infChar τ = {s} := by
  rw [CG.infChar_ofChar, expo_absC]

theorem isRegAlg_absC (s : ℂ) : (CG.ofChar (absC E s)).IsRegAlg ↔ ∃ n : ℤ, s = n := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  simp only [CG.isRegAlg_ofChar, expo_absC]
  exact ⟨fun h => h τ, fun h _ => h⟩

theorem not_isRegAlg_half : ¬ (CG.ofChar (absC E (1 / 2))).IsRegAlg := by
  rw [isRegAlg_absC]
  rintro ⟨n, hn⟩
  have h : (1 : ℂ) = 2 * n := by rw [← hn]; norm_num
  have h' : (1 : ℤ) = 2 * n := by exact_mod_cast h
  omega

theorem absC_class_injective : Function.Injective fun s : ℂ => CG.ofChar (absC E s) := fun s t h => by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := congrArg (fun π : CG E 1 => π.infChar τ) h
  simpa [infChar_absC] using this

theorem infinite_rank_one : Infinite (CG E 1) := Infinite.of_injective _ absC_class_injective

theorem twist_absC_ne {π : CG E a} (ha : 0 < a) {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {s : ℂ}
    (hs : s ≠ 0) : π.twist (absC E s) ≠ π := fun e => by
  have h1 := (h.twist (absC E s)).infChar_eq
  rw [e, h.infChar_eq, expo_absC] at h1
  have h2 := congrArg Multiset.sum h1
  have h3 : Multiset.card m = a := h.infChar_eq ▸ CG.card_infChar π τ
  rw [Multiset.sum_map_add] at h2
  simp [h3, hs, ha.ne'] at h2

theorem subsingleton_rank_zero : Subsingleton (CG E 0) := by
  have key : ∀ π : CuspSub E 0, π = CuspSub.triv E zero_le_one := fun π => by
    have hle : π.V ≤ (CuspSub.triv E (a := 0) zero_le_one).V := fun φ _ =>
      Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => by
        rw [Subsingleton.elim g 1]; exact mul_one _)⟩
    exact CuspSub.ext (((CuspSub.triv E zero_le_one).irred _ hle π.stable).resolve_left π.ne_bot)
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  rename_i p q
  rw [key p, key q]

theorem chiDet_notMem (ha : 2 ≤ a) (π : CuspSub E a) (χ : HChar E) : mulChi a χ (oneFn E a) ∉ π.V := fun h => by
  have h1 := ((π.cusp _ h).mulChi χ⁻¹).2
  rw [← mulChi_mul, mul_inv_cancel, mulChi_one] at h1
  exact GlobalTheory.ConstNotCusp.not_isCuspidal_oneFn E a ha h1

section CM

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem isCsd_absC (s : ℂ) : (CG.ofChar (absC L s)).IsCsd ↔ s = 0 := by
  constructor
  · intro h
    obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := inferInstance
    have h1 := CG.expo_conj_of_isCsd h τ
    rw [expo_absC, expo_absC] at h1
    linear_combination h1 / 2
  · rintro rfl
    have e : absC L 0 = 1 := Subtype.ext (MonoidHom.ext fun x => Units.ext (by
      change Complex.exp (0 * _) = 1
      simp))
    rw [e, CG.isCsd_ofChar]
    refine CG.thetaInv_of (fun _ => rfl) fun z => ?_
    have h0 : dchi (1 : HChar L) = 0 := fderiv_extZero (continuous_chiInf 1) fun z => by simp [chiInf]
    simp [h0]

end CM

end GlobalTheory.CuspRep.Model
