import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3 Ad3.R
open scoped Classical

namespace GlobalTheory.CompanionTheory.RankinWhittaker

theorem prodEquiv_realEmb (x : GL (Fin 2) ℝ) :
    AdelicGLn.prodEquiv ℚ 2 (realEmb x) = (GL2Classical.realInf x, 1) :=
  (AdelicGLn.prodEquiv ℚ 2).apply_symm_apply _

theorem realPart_congr {g g' : G2} (h : ∀ w, infAt w g = infAt w g') : realPart g = realPart g' := by
  have e : (AdelicGLn.prodEquiv ℚ 2 g).1 = (AdelicGLn.prodEquiv ℚ 2 g').1 := by
    ext a b
    change (g a b).1 = (g' a b).1
    funext w
    have := congrArg (fun x : GL (Fin 2) w.Completion => x a b) (h w)
    simpa using this
  simp only [GL2Classical.realPart, e]

theorem infAt_realEmb_realPart (g : G2) (w : InfinitePlace ℚ) : infAt w (realEmb (realPart g)) = infAt w g := by
  have e : (AdelicGLn.prodEquiv ℚ 2 (realEmb (realPart g))).1 = (AdelicGLn.prodEquiv ℚ 2 g).1 := by
    rw [prodEquiv_realEmb]
    ext a b
    simp [GL2Classical.realPart, GL2Classical.realInf]
  change (AdelicGLn.infiniteEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (realEmb (realPart g))).1) w =
    (AdelicGLn.infiniteEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 g).1) w
  rw [e]

theorem finAt_realEmb (x : GL (Fin 2) ℝ) (v : Pl) : finAt v (realEmb x) = 1 := by
  have e : (AdelicGLn.prodEquiv ℚ 2 (realEmb x)).2 = 1 := by
    rw [prodEquiv_realEmb]
  change (AdelicGLn.finiteRestrictedEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (realEmb x)).2) v = 1
  rw [e, map_one]
  rfl

theorem Wh_mul_right {φ : G2 → ℂ} {κ : G2} (h : ∀ g, φ (g * κ) = φ g) (g : G2) : Wh φ (g * κ) = Wh φ g := by
  unfold Wh
  simp only [← mul_assoc, h]

theorem Wh_eq_prod {N : ℕ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    {μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ} {φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ}
    (hglob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g)
    (hmod : Mod N ω (Wh φ) μ₁ μ₂ φ₀) (hloc : ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h, IsLoc2 v x h)
    (T : Finset Pl) : ∀ g : G2, (∀ v ∉ T, finAt v g ∈ integralGL (Qv v) 2 ∧ (pOf v ∣ N → finAt v g = 1)) →
      Wh φ g = Wh φ (realEmb (realPart g)) *
        ∏ v ∈ T, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g) := by
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hinf : ∀ w, infAt w ((realEmb (realPart g))⁻¹ * g) = 1 := fun w => by
      rw [Reduction.infAt_mul, Reduction.infAt_inv, infAt_realEmb_realPart, inv_mul_cancel]
    have hfin : ∀ v, finAt v ((realEmb (realPart g))⁻¹ * g) = finAt v g := fun v => by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, finAt_realEmb, inv_one, one_mul]
    have hκ : (realEmb (realPart g))⁻¹ * g ∈ (maxCompact : Subgroup G2) :=
      ⟨fun w => by rw [hinf w]; exact one_mem _, fun v => by
        rw [hfin v]; exact (hg v (by simp)).1⟩
    have h := Wh_mul_right (hglob ⟨_, hκ⟩ hinf (fun v hv => by
      change finAt v ((realEmb (realPart g))⁻¹ * g) = 1
      rw [hfin v]; exact (hg v (by simp)).2 hv)) (realEmb (realPart g))
    simp only [mul_inv_cancel_left] at h
    simpa using h
  | insert v T hv ih =>
    intro g hg
    obtain ⟨h, hh⟩ := hloc v (finAt v g)
    have hv1 : finAt v (g * h⁻¹) = 1 := by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, hh.1, mul_inv_cancel]
    have hoth : ∀ v', v' ≠ v → finAt v' (g * h⁻¹) = finAt v' g := fun v' hne => by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, hh.2.1 v' hne, inv_one, mul_one]
    have hinf : ∀ w, infAt w (g * h⁻¹) = infAt w g := fun w => by
      rw [Reduction.infAt_mul, Reduction.infAt_inv, hh.2.2 w, inv_one, mul_one]
    have hfac := hmod.fac v (g * h⁻¹) hv1 (finAt v g) h hh
    rw [inv_mul_cancel_right] at hfac
    have hoff : ∀ v' ∉ T, finAt v' (g * h⁻¹) ∈ integralGL (Qv v') 2 ∧ (pOf v' ∣ N → finAt v' (g * h⁻¹) = 1) := by
      intro v' hv'
      by_cases e : v' = v
      · subst e
        exact ⟨by rw [hv1]; exact one_mem _, fun _ => hv1⟩
      · rw [hoth v' e]
        exact hg v' (by simp [e, hv'])
    rw [hfac, ih _ hoff, realPart_congr hinf, Finset.prod_insert hv,
      Finset.prod_congr rfl (fun v' hv' => by
        rw [hoth v' (fun e => hv (e ▸ hv'))])]
    ring

theorem whittaker_factorisation : B0 → M0 → F3 → E0 := by
  intro hB hM hF k N _ h3 χ hχ f a hform heig ω φ hom hlift μ₁ μ₂ φ₀ hmod g
  obtain ⟨h1, hinj, -, -, -, -, hfin, -⟩ := hB
  have hH : Hk k N a ω φ := hF k N h3 χ hχ f a hform heig ω φ hom hlift
  have hbad : {v : Pl | pOf v ∣ N}.Finite :=
    ((Finset.finite_toSet (Nat.divisors N)).preimage hinj.injOn).subset fun v hv => by
      simpa [Nat.mem_divisors, NeZero.ne N] using hv
  have hT : ∀ v, v ∉ (hfin g).toFinset ∪ hbad.toFinset → finAt v g ∈ integralGL (Qv v) 2 ∧ ¬ pOf v ∣ N := by
    intro v hv
    simpa using hv
  rw [Wh_eq_prod hH.glob hmod (fun v => (h1 v).2.2.2.2.2.1) ((hfin g).toFinset ∪ hbad.toFinset) g
    (fun v hv => ⟨(hT v hv).1, fun hd => absurd hd (hT v hv).2⟩)]
  congr 1
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hvT
  apply hv
  obtain ⟨hint, hnb⟩ := hT v hvT
  obtain ⟨hu1, hu2, hφ⟩ := hmod.good v hnb
  beta_reduce
  rw [hφ]
  obtain ⟨-, hone, htype⟩ := hM (Qv v) (localAdelicChar ℚ v) (h1 v).1 (μ₁ v) (μ₂ v) (hmod.u₁ v) (hmod.u₂ v) hu1 hu2
  have h := htype.1 (finAt v g) hint 1
  rw [one_mul] at h
  rw [h, hone]

end GlobalTheory.CompanionTheory.RankinWhittaker

end
