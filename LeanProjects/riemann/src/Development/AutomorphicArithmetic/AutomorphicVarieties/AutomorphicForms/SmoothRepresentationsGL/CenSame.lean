import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.OneScalar

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem infGL_scalar {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (u : (Rinf E)ˣ) :
    infGL E n (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) (TR.infId E u) := by
  have h1 : pInf E (TR.infId E u).val = u.val := by
    change pInf E (1 - sInf E 1 + sInf E _) = _
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (TR.infEq E).symm_apply_apply x
    simp [h]
  have h2 : pFin E (TR.infId E u).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem deriv_centre {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (φ : TR.Sm E n)
    (g : GA E n) :
    HasDerivAt (fun t : ℝ => φ.1 (g * GeneralLinearGroup.scalar (Fin n) (TR.infId E (TR.expU (t • (1 : Rinf E))))))
      ((TR.lie E n (oneL E n) φ).1 g) 0 := by
  have h := TR.hasDerivAt_curve φ g (fun t : ℝ => GeneralLinearGroup.scalar (Fin n) (TR.expU (t • (1 : Rinf E))))
    (oneL E n) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        simpa using Real.hasDerivAt_exp 0
      · simpa [Matrix.diagonal_apply, Matrix.one_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simp only [infGL_scalar] at h
  exact h

theorem UpperTheory.V.Af.Smo.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.CenSame := by
  intro hC hS hE E _ _ _ n π π' hs hc φ' hφ'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n π π' hs φ hφ φ' hφ'
  have key : ∀ ψ : TR.Sm E n, TR.IsCuspForm ψ → Continuous ψ.1 ∧ IsLeftInvariant ψ.1 := fun ψ hψ => by
    obtain ⟨x, rfl⟩ := Fb.mem_range_ofCusp.2 hψ
    exact ⟨x.2.1.continuous, x.2.1.isLeftInvariant⟩
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w n, InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 (key _ (π.cusp _ hφ)).1 (key _ (π'.cusp _ hφ')).1 (key _ (π.cusp _ hφ)).2
    (key _ (π'.cusp _ hφ')).2 (fun w hw => ⟨hE E n π w _ (hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      hE E n π' w _ (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  refine Subtype.ext (funext fun g' => ?_)
  have d1 := (deriv_centre φ g).mul_const (φ'.1 g')
  have d2 := (deriv_centre φ' g').const_mul (φ.1 g)
  simp only [e _ g g'] at d1
  have d := d1.unique d2
  rw [hc φ hφ] at d
  exact (mul_eq_zero.1 (d.symm.trans (zero_mul _))).resolve_left hg
