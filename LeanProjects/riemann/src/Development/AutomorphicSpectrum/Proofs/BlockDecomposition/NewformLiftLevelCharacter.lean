import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]

omit [MeasurableSpace F] [BorelSpace F] in

theorem inv_mul_mem_of_ord_le {m y : F} (hm : m ≠ 0) (hy : y ≠ 0 → ord m ≤ ord y) :
    m⁻¹ * y ∈ 𝒪[F] := by
  rcases eq_or_ne y 0 with rfl | h0
  · simp
  · have := hy h0
    rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hm) h0), ord_mul (inv_ne_zero hm) h0,
      ord_inv hm]
    omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem le_ord_of_mem {n : ℕ} {y : F} (h0 : y ≠ 0)
    (hc : (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * y ∈ 𝒪[F]) : (n : ℤ) ≤ ord y := by
  have e : ((unifUnit F)⁻¹ ^ n : Fˣ) = unifUnit F ^ (-(n : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_natCast]
  have h := (mem_integer_iff_ord (mul_ne_zero (Units.ne_zero _) h0)).1 hc
  rw [ord_mul (Units.ne_zero _) h0, e, ord_unifUnit_zpow] at h
  omega

omit [MeasurableSpace F] [BorelSpace F] in

theorem ord_lower_right {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) :
    ord (d : F) = 0 := by
  obtain ⟨hx, hc, hd⟩ := h
  have hxi := ((GLnLocal.mem_integralGL_iff F 2).1 hx).1
  have hπ : ((unifUnit F : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h0 : 0 ≤ ord (d : F) := (mem_integer_iff_ord d.ne_zero).1 (hd ▸ hxi 1 1)
  by_contra hne
  have h1 : ord ((unifUnit F : Fˣ) : F) ≤ ord (x 1 1) := by
    rw [ord_unifUnit, ← hd]; omega
  have hd' := inv_mul_mem_of_ord_le hπ (y := x 1 1) fun _ => h1
  have hc' := inv_mul_mem_of_ord_le hπ (y := x 1 0) fun h0 => by
    have := le_ord_of_mem h0 hc
    rw [ord_unifUnit]; omega
  have hdet : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) ∈ 𝒪[F] := by
    have : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) =
        x 0 0 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 1) -
          x 0 1 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 0) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      ring
    rw [this]
    exact sub_mem (mul_mem (hxi 0 0) hd') (mul_mem (hxi 0 1) hc')
  have hz : ord (Matrix.GeneralLinearGroup.det x : F) = 0 := GodementSectionLocal.ord_det_eq_zero hx
  have hdn : (Matrix.GeneralLinearGroup.det x : F) ≠ 0 := Units.ne_zero _
  have := (mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hπ) hdn)).1 hdet
  rw [ord_mul (inv_ne_zero hπ) hdn, ord_inv hπ, ord_unifUnit, hz] at this
  omega

end Local

theorem mem_Gamma0Level_of_places (N : ℕ) [NeZero N] (u : AdelicGLn.FiniteAdelicGL ℚ 2)
    (hint : ∀ v : Pl, glAt v u ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * glAt v u 1 0 ∈ 𝒪[Qv v]) : u ∈ Gamma0Level N := by
  refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => ?_, ?_⟩
  · have e : (AdelicGLn.finiteRestrictedEquiv ℚ 2 u v : GL (Fin 2) (Qv v)) = glAt v u :=
      Units.ext (Matrix.ext fun a b => rfl)
    rw [e]
    exact hint v
  · rw [GL2Classical.mem_levelIdeal_iff, mem_integralFiniteAdeles]
    intro v
    have hw : adeleAt v ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) = ((N : Qv v))⁻¹ := by
      have h1 : ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) * (N : Af) = 1 := by
        rw [← GL2Classical.coe_levelUnit N, Units.inv_mul]
      have h2 := congrArg (adeleAt v) h1
      rw [map_mul, map_natCast, map_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have e : (((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) *
        (u : Matrix (Fin 2) (Fin 2) Af) 1 0) v = ((N : Qv v))⁻¹ * glAt v u 1 0 := by
      rw [← hw]
      exact map_mul (adeleAt v) _ _
    rw [e]
    exact (mem_valuationInteger_iff v _).1 (hlev v)

theorem exists_finEmb (h : G2) (hinf : ∀ w, infAt w h = 1) :
    ∃ u : AdelicGLn.FiniteAdelicGL ℚ 2, h = finEmb ℚ 2 u ∧ ∀ v : Pl, glAt v u = finAt v h := by
  refine ⟨(AdelicGLn.prodEquiv ℚ 2 h).2, ?_, fun v => Units.ext (Matrix.ext fun a b => rfl)⟩
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ rfl
  apply (AdelicGLn.infiniteEquiv ℚ 2).injective
  funext w
  rw [map_one]
  exact hinf w

theorem lift_right {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * finAt v h 1 0 ∈ 𝒪[Qv v])
    (D : Afˣ) (hD : ∀ v, ord (lf v D : Qv v) = 0)
    (hD' : ∀ v, pOf v ∣ N → (lf v D : Qv v) = finAt v h 1 1) (g : G2) :
    φ (g * h) = (ω.toIdele (IdeleGroup.ofFinite D) : ℂ) * φ g := by
  obtain ⟨u, rfl, hu⟩ := exists_finEmb h hinf
  refine hL.level u (mem_Gamma0Level_of_places N u (fun v => ?_) fun v => ?_) D hD (fun v hv => ?_) g
  · rw [hu v]; exact hint v
  · rw [hu v]; exact hlev v
  · rw [hu v]; exact hD' v hv

theorem natCast_ne_zero_at (N : ℕ) [NeZero N] (v : Pl) : (N : Qv v) ≠ 0 := by
  have h : (algebraMap ℚ (Qv v)) (N : ℚ) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 (NeZero.ne N))
  rwa [map_natCast] at h

theorem lf_one (v : Pl) : (lf v (1 : Afˣ) : Qv v) = 1 := by
  simp [lf]

theorem lift_right_good {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ}
    {φ : G2 → ℂ} (hord : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0)
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hbad : ∀ v : Pl, pOf v ∣ N → finAt v h = 1) (g : G2) : φ (g * h) = φ g := by
  have key := lift_right hL hinf hint (fun v => ?_) 1 (fun v => ?_) (fun v hv => ?_) g
  · simpa using key
  · by_cases hv : pOf v ∣ N
    · rw [hbad v hv]; simp
    · refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v) fun h0 => ?_
      rw [hord v hv]
      exact (mem_integer_iff_ord h0).1 (((GLnLocal.mem_integralGL_iff _ 2).1 (hint v)).1 1 0)
  · rw [lf_one]; exact ord_one
  · rw [lf_one, hbad v hv]; simp

theorem ofFinite_toFinite_of_inf {a' d' : Jd} (h3 : ∀ w, infAt w (dg2 a' d' : G2) = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ d') = d' := by
  apply (IdeleGroup.prodEquiv ℚ).injective
  refine Prod.ext ?_ ?_
  · have e : (IdeleGroup.prodEquiv ℚ d').1 = 1 := by
      apply Units.ext
      funext w
      have h := congrArg (fun M : GL (Fin 2) _ => M 1 1) (h3 w)
      show (d' : 𝔸[ℚ]).1 w = 1
      simpa [dg2] using h
    rw [e]
    exact IdeleGroup.toInfinite_ofFinite _
  · exact IdeleGroup.toFinite_ofFinite _

theorem lift_local_invariance : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  intro hB k N _ hk χ hχ f a hf he ω φ hω hL
  obtain ⟨hloc, -, -, -, -, -, -, hid⟩ := hB
  have hordN : ∀ v : Pl, ord (N : Qv v) = N.factorization (pOf v) :=
    fun v => (hloc v).2.2.2.2.1 N (NeZero.ne N)
  have hgood : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0 := fun v hv => by
    rw [hordN v, Nat.factorization_eq_zero_of_not_dvd hv]; rfl
  refine ⟨fun v hv x hx h hh g => ?_, fun v hv x d hxd h hh g => ?_, fun κ hκ hκ' g => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hh
    refine lift_right_good hgood hL h3 (fun v' => ?_) (fun v' hv' => ?_) g
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hx
      · rw [h2 v' e]; exact one_mem _
    · refine h2 v' fun e => hv (e ▸ hv')
  · obtain ⟨h1, h2, h3⟩ := hh
    have hn : 1 ≤ N.factorization (pOf v) :=
      (hloc v).2.2.1.factorization_pos_of_dvd (NeZero.ne N) hv
    have hu : ord (d : Qv v) = 0 := ord_lower_right hn hxd
    obtain ⟨x', a', d', -, ⟨e1, e2, e3⟩, -, -, hc⟩ := hid v 0 1 d
    have hcomp : ∀ v' : Pl, (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') =
        finAt v' (dg2 a' d' : G2) 1 1 := fun v' => rfl
    have hdv : (lf v (IdeleGroup.toFinite ℚ d') : Qv v) = d := by
      rw [hcomp v, e1]; simp [dg2]
    have hov : ∀ v' : Pl, v' ≠ v → (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') = 1 := fun v' hv' => by
      rw [hcomp v', e2 v' hv']; simp
    have key := lift_right hL h3 (fun v' => ?_) (fun v' => ?_) (IdeleGroup.toFinite ℚ d')
      (fun v' => ?_) (fun v' hv' => ?_) g
    · rw [ofFinite_toFinite_of_inf e3, (hc ω).2] at key
      exact key
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hxd.1
      · rw [h2 v' e]; exact one_mem _
    · by_cases e : v' = v
      · subst e
        rw [h1]
        refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v') fun h0 => ?_
        rw [hordN v']
        exact le_ord_of_mem h0 hxd.2.1
      · rw [h2 v' e]; simp
    · by_cases e : v' = v
      · subst e; rw [hdv]; exact hu
      · rw [hov v' e]; exact ord_one
    · by_cases e : v' = v
      · subst e; rw [hdv, h1]; exact hxd.2.2
      · rw [hov v' e, h2 v' e]; simp
  · exact lift_right_good hgood hL hκ (fun v' => κ.2.2 v') hκ' g

end GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel
