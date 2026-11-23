import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

noncomputable section

open NumberField GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.Published.AutFinGL.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem forms_anti {L L' : Subgroup (GL (Fin a) (Af E))} (h : L ≤ L') {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (c : (E →+* ℂ) → ℂ → ℂ) : forms L' ρ c ⊆ forms L ρ c :=
  fun _ hφ => ⟨hφ.1, fun k hk => hφ.2.1 k (h hk), hφ.2.2⟩

theorem finite_rank_zero (L : Subgroup (GL (Fin 0) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E 0) W) (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (forms L ρ c)) := by
  have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  have : Finite (GA E 0) := Finite.of_subsingleton
  infer_instance

theorem cap_rank_one (τ : E →+* ℂ) (u : ℂ) (φ : Sm E 1) : cap τ u φ = u • φ + Eop τ 0 0 φ := by
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

def kerL (a : ℕ) (χ : HChar E) : Subgroup (GL (Fin a) (Af E)) := ((chiDet a χ).comp (finGL E a)).ker

theorem isOpen_kerL (χ : HChar E) : IsOpen (kerL a χ : Set (GL (Fin a) (Af E))) := isOpen_ker_chiDet χ

def kRep (a : ℕ) (χ : HChar E) : Representation ℂ (Kinf E a) ℂ :=
  twRep (Representation.trivial ℂ (Kinf E a) ℂ) ((chiDet a χ).comp ((infGL E a).comp Unitary.toUnits))

theorem isContRep_kRep (χ : HChar E) : AutFin.IsContRep (kRep a χ) := by
  intro ℓ w
  have h1 : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have h2 : Continuous fun k : Kinf E a =>
      ((chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf E))) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((continuous_chiInf χ).comp (Matrix.GeneralLinearGroup.continuous_det.comp h1))
  have e : (fun k : Kinf E a => ℓ (kRep a χ k w)) = fun k =>
      ((chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf E))) : ℂˣ) : ℂ) * ℓ w := by
    funext k
    rw [← show chiDet a χ (infGL E a (Unitary.toUnits k)) =
      chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k)) from congrArg χ.1 (det_infGL _), ← smul_eq_mul,
      ← map_smul]
    rfl
  rw [e]
  exact h2.mul continuous_const

theorem chi_mem_forms (χ : HChar E) :
    mulChi a χ (oneFn E a) ∈ forms (kerL a χ) (kRep a χ)
      (fun τ u => ∏ k : Fin a, (u + expo χ τ + (((a : ℂ) - 1) / 2 - (k : ℕ)))) := by
  refine ⟨(isAutForm_const (Submodule.mem_span_singleton_self _)).mulChi χ, fun k hk => ?_, fun g => ?_,
    fun τ u => ?_⟩
  · have h2 : chiDet a χ (finGL E a k) = 1 := hk
    change rt E a (finGL E a k) _ = _
    rw [rt_mulChi, h2, Units.val_one, one_smul]
    rfl
  · refine Submodule.subset_span ⟨LinearMap.id, ((chiDet a χ g : ℂˣ) : ℂ), funext fun k => ?_⟩
    change (1 : ℂ) * ((chiDet a χ (g * infGL E a (Unitary.toUnits k)) : ℂˣ) : ℂ) =
      ((chiDet a χ (infGL E a (Unitary.toUnits k)) : ℂˣ) : ℂ) * ((chiDet a χ g : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul]; ring
  · rw [cap_mulChi, cap_oneFn, map_smul]

theorem chi_ne_zero (χ : HChar E) : mulChi a χ (oneFn E a) ≠ 0 :=
  (map_ne_zero_iff _ (mulChi a χ).injective).2 oneFn_ne_zero

theorem forms_zero_type {L : Subgroup (GL (Fin a) (Af E))} {W : Type} [AddCommGroup W] [Module ℂ W] [Subsingleton W]
    {ρ : Representation ℂ (Kinf E a) W} {c : (E →+* ℂ) → ℂ → ℂ} {φ : Sm E a} (h : φ ∈ forms L ρ c) : φ = 0 := by
  have hb : AutFin.coeffSpan ρ = ⊥ := Submodule.span_eq_bot.2 (by
    rintro _ ⟨ℓ, w, rfl⟩
    funext k
    rw [Subsingleton.elim (ρ k w) 0, map_zero]; rfl)
  refine Subtype.ext (funext fun g => ?_)
  have h1 := h.2.2.1 g
  rw [hb, Submodule.mem_bot] at h1
  have := congrFun h1 1
  simpa using this

end GlobalTheory.Published.AutFinGL.Model

end
