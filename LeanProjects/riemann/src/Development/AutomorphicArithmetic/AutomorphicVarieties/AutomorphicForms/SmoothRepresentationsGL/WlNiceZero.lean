import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem wl_nice_zero : Nice (0 : GA E n → ℂ) where
  cont := continuous_zero
  bdd := ⟨0, fun g => by simp⟩
  left := fun _ _ => rfl
  cusp := fun _ _ _ g => constantTerm_zero g
  level := ⟨⊤, fun _ _ _ => rfl⟩

private theorem wl_nice_add {f f' : GA E n → ℂ} (h : Nice f) (h' : Nice f') : Nice (f + f') where
  cont := h.cont.add h'.cont
  bdd := by
    obtain ⟨C, hC⟩ := h.bdd
    obtain ⟨C', hC'⟩ := h'.bdd
    exact ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩
  left := IsLeftInvariant.add h.left h'.left
  cusp := fun r a b g => by
    have e := constantTerm_add (r := r) h.cont h'.cont g
    rw [h.cusp r a b g, h'.cusp r a b g, add_zero] at e
    exact e
  level := by
    obtain ⟨V, hV⟩ := h.level
    obtain ⟨V', hV'⟩ := h'.level
    refine ⟨V ⊓ V', fun g v hv => ?_⟩
    rw [OpenSubgroup.mem_inf] at hv
    rw [Pi.add_apply, Pi.add_apply, hV g v hv.1, hV' g v hv.2]

private theorem wl_nice_smul {f : GA E n → ℂ} (h : Nice f) (z : ℂ) : Nice (z • f) where
  cont := h.cont.const_smul z
  bdd := by
    obtain ⟨C, hC⟩ := h.bdd
    refine ⟨‖z‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)
  left := IsLeftInvariant.smul z h.left
  cusp := fun r a b g => by
    have e := constantTerm_smul (r := r) z f g
    rw [h.cusp r a b g, smul_zero] at e
    exact e
  level := by
    obtain ⟨V, hV⟩ := h.level
    exact ⟨V, fun g v hv => by rw [Pi.smul_apply, Pi.smul_apply, hV g v hv]⟩

private theorem wl_nice_tr {f : GA E n → ℂ} (h : Nice f) (x : GL (Fin n) (Af E)) :
    Nice (fun g => f (g * finGL E n x)) where
  cont := h.cont.comp (continuous_id.mul continuous_const)
  bdd := h.bdd.imp fun _ hC _ => hC _
  left := fun γ g => by
    have e := h.left γ (g * finGL E n x)
    rw [← mul_assoc] at e
    exact e
  cusp := fun r a b g =>
    (constantTerm_rightTranslate (r := r) f (finGL E n x) g).trans (h.cusp r a b _)
  level := by
    obtain ⟨V, hV⟩ := h.level
    refine ⟨V.comap (MulAut.conj x⁻¹).toMonoidHom ?_, fun g v hv => ?_⟩
    · show Continuous fun v => x⁻¹ * v * x⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ V := hv
      have e := hV (g * finGL E n x) _ hv'
      rw [inv_inv, mul_assoc g, ← map_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, map_mul,
        ← mul_assoc] at e
      exact e

private theorem wl_add {f f' : GA E n → ℂ} (h : Continuous f) (h' : Continuous f') :
    whittaker (f + f') = whittaker f + whittaker f' := by
  funext g
  obtain ⟨C, hC, hD⟩ := FourierWhittaker.exists_isCompact_superset_vecDomain (K := E)
    (ι := FourierWhittaker.Pos n)
  have i : ∀ {φ : GA E n → ℂ}, Continuous φ → IntegrableOn (FourierWhittaker.wInt 0 φ g)
      (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))
      (FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)) := fun hφ =>
    ((FourierWhittaker.continuous_wInt 0 hφ g).continuousOn.integrableOn_compact hC).mono_set hD
  have e := integral_add (i h) (i h')
  simp only [FourierWhittaker.wInt] at e
  simp only [whittaker, Pi.add_apply, add_mul]
  exact e

private theorem wl_smul (f : GA E n → ℂ) (z : ℂ) : whittaker (z • f) = z • whittaker f := by
  funext g
  simp only [whittaker, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

private theorem wl_tr (f : GA E n → ℂ) (y : GA E n) :
    whittaker (fun g => f (g * y)) = fun g => whittaker f (g * y) := by
  funext g
  simp only [whittaker, mul_assoc]

private theorem wl_sum {f : GA E n → ℂ} (h : Nice f) (c : GL (Fin n) (Af E) → ℂ) (s : Finset (GL (Fin n) (Af E))) :
    Nice (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) ∧
      whittaker (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) =
        ∑ x ∈ s, c x • fun g => whittaker f (g * finGL E n x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨wl_nice_zero, ?_⟩
    funext g
    simp [whittaker]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have k := wl_nice_smul (wl_nice_tr h a) (c a)
    exact ⟨wl_nice_add k ih.1, by rw [wl_add k.cont ih.1.cont, ih.2, wl_smul, wl_tr]⟩

private theorem wl_fop (c : GL (Fin n) (Af E) →₀ ℂ) (f : GA E n → ℂ) :
    fop c f = ∑ x ∈ c.support, c x • fun g => f (g * finGL E n x) := by
  funext g
  simp [fop, Finsupp.sum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Smo.whLin :
    UpperTheory.V.Af.Smo.WhLin := by
  intro E _ _ n f hf
  refine ⟨fun c => ?_, fun f' hf' => ?_⟩
  · rw [wl_fop, wl_fop]
    exact wl_sum hf c c.support
  · have e : f - f' = f + (-1 : ℂ) • f' := by rw [neg_one_smul, sub_eq_add_neg]
    have k := wl_nice_smul hf' (-1)
    rw [e]
    exact ⟨wl_nice_add hf k, by rw [wl_add hf.cont k.cont, wl_smul, neg_one_smul, sub_eq_add_neg]⟩
