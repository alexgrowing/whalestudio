import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSum

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift toReal)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSq

theorem inv_uni_dg {R : Type*} [CommRing R] (b : R) (P : Rˣ) :
    (uni2 b * dg2 P 1 : GL (Fin 2) R)⁻¹ = dg2 P⁻¹ 1 * uni2 (-b) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_dg {R : Type*} [CommRing R] (P : Rˣ) :
    (dg2 1 P : GL (Fin 2) R)⁻¹ = dg2 1 P⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_uni {R : Type*} [CommRing R] (b : R) : (uni2 b : GL (Fin 2) R)⁻¹ = uni2 (-b) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem invariant_under_antidiagonal_idele {R : Type*} [CommRing R] (a d : Rˣ) : (dg2 a d : GL (Fin 2) R)⁻¹ = dg2 a⁻¹ d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem map_uni {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) (b : R) :
    Matrix.GeneralLinearGroup.map e (uni2 b) = uni2 (e b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2]

theorem map_dg {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) (a d : Rˣ) :
    Matrix.GeneralLinearGroup.map e (dg2 a d) = dg2 (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem mem_O_of_ord {v : Pl} {x : Qv v} (hx : x ≠ 0) (h : ord x = 0) : x ∈ 𝒪[Qv v] := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, h]
  simp

theorem ord_inv_of_ord_zero {v : Pl} {x : Qv v} (hx : x ≠ 0) (h : ord x = 0) : ord x⁻¹ = 0 := by
  have := ord_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, h] at this
  simpa [ord] using this.symm

theorem natCast_ne (v : Pl) {n : ℕ} (hn : n ≠ 0) : ((n : ℕ) : Qv v) ≠ 0 := by
  have : algebraMap ℚ (Qv v) n ≠ 0 := by
    simpa using (map_ne_zero (algebraMap ℚ (Qv v))).2 (Nat.cast_ne_zero.2 hn)
  simpa using this

theorem ord_p (h0 : B0) {v v' : Pl} (hv : v' ≠ v) : ord ((pOf v : ℕ) : Qv v') = 0 := by
  obtain ⟨h1, hinj, -⟩ := h0
  obtain ⟨-, -, hpr, -, hfac, -⟩ := h1 v
  obtain ⟨-, -, hpr', -, hfac', -⟩ := h1 v'
  rw [hfac' _ hpr.ne_zero]
  have hne : pOf v ≠ pOf v' := fun h => hv (hinj h).symm
  simp [Nat.Prime.factorization hpr, hne]

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical

theorem prod_fst_one (h : G2) (hinf : ∀ w, infAt w h = 1) : (prodEquiv ℚ 2 h).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have := congrArg (fun g : GL (Fin 2) w.Completion => g a b) (hinf w)
  simp only [GroundTheory.Automorphic.Reduction.infAt_apply] at this
  change (h a b).1 w = _
  rw [this]
  by_cases hab : a = b
  · subst hab; simp; rfl
  · simp [Matrix.one_apply_ne hab]; rfl

theorem split_eq (h : G2) (hinf : ∀ w, infAt w h = 1) (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) ℝ) :
    realEmb x * h = dia2 γ * (realEmb ((toReal γ)⁻¹ * x) *
      finEmb ℚ 2 ((finiteDiagonal ℚ 2 γ)⁻¹ * (prodEquiv ℚ 2 h).2)) := by
  have h1 : h = finEmb ℚ 2 (prodEquiv ℚ 2 h).2 := by
    apply (prodEquiv ℚ 2).injective
    rw [prodEquiv_finEmb]
    exact Prod.ext (prod_fst_one h hinf) rfl
  have := diagonal_mul_realEmb_mul_finEmb 1 γ x (prodEquiv ℚ 2 h).2
  rw [map_one, one_mul, one_mul, ← h1] at this
  rw [this, mul_assoc]

theorem glAt_snd (v : Pl) (h : G2) : glAt v (prodEquiv ℚ 2 h).2 = finAt v h := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

theorem glAt_diag (v : Pl) (γ : GL (Fin 2) ℚ) :
    glAt v (finiteDiagonal ℚ 2 γ) = Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) γ := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  exact RingHom.congr_fun (RingHom.ext_rat ((adeleAt v).comp (algebraMap ℚ Af)) (algebraMap ℚ (Qv v))) _

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical

abbrev uOf (γ : GL (Fin 2) ℚ) (h : G2) : FiniteAdelicGL ℚ 2 := (finiteDiagonal ℚ 2 γ)⁻¹ * (prodEquiv ℚ 2 h).2

theorem glAt_u_self {v : Pl} {γ : GL (Fin 2) ℚ} {h : G2}
    (hh : IsLoc2 v (Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) γ) h) : glAt v (uOf γ h) = 1 := by
  rw [uOf, map_mul, map_inv, glAt_snd, glAt_diag, hh.1, inv_mul_cancel]

theorem glAt_u_ne {v v' : Pl} {γ : GL (Fin 2) ℚ} {h : G2} {x : GL (Fin 2) (Qv v)}
    (hh : IsLoc2 v x h) (hv : v' ≠ v) :
    glAt v' (uOf γ h) = Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v')) γ⁻¹ := by
  rw [uOf, map_mul, map_inv, glAt_snd, glAt_diag, hh.2.1 v' hv, mul_one, map_inv]

theorem mem_level {N : ℕ} [NeZero N] {v : Pl} {γ : GL (Fin 2) ℚ} {h : G2}
    (hh : IsLoc2 v (Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) γ) h)
    (hint : ∀ v' ≠ v, Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v')) γ⁻¹ ∈ integralGL (Qv v') 2)
    (h10 : (γ⁻¹ : GL (Fin 2) ℚ) 1 0 = 0) : uOf γ h ∈ Gamma0Level N := by
  have hg : ∀ v', glAt v' (uOf γ h) ∈ integralGL (Qv v') 2 := fun v' => by
    by_cases hv : v' = v
    · subst hv; rw [glAt_u_self hh]; exact one_mem _
    · rw [glAt_u_ne hh hv]; exact hint v' hv
  refine (mem_Gamma0Level N).2 ⟨(mem_integralFiniteGL_iff_forall ℚ 2).2 fun v' => ?_, ?_⟩
  · have : finiteRestrictedEquiv ℚ 2 (uOf γ h) v' = glAt v' (uOf γ h) :=
      Units.ext (Matrix.ext fun a b => rfl)
    rw [this]
    exact hg v'
  · have : (uOf γ h : Matrix (Fin 2) (Fin 2) Af) 1 0 = 0 := by
      refine Subtype.ext (funext fun v' => ?_)
      change (glAt v' (uOf γ h)) 1 0 = 0
      by_cases hv : v' = v
      · subst hv; rw [glAt_u_self hh]; simp
      · rw [glAt_u_ne hh hv]
        change algebraMap ℚ (Qv v') ((γ⁻¹ : GL (Fin 2) ℚ) 1 0) = 0
        rw [h10, map_zero]
    rw [this]
    exact zero_mem_levelIdeal N

theorem uni_mem {v : Pl} (b : Qv v) (hb : b ∈ 𝒪[Qv v]) : uni2 b ∈ integralGL (Qv v) 2 := by
  have hb' : -b ∈ 𝒪[Qv v] := neg_mem hb
  refine (GLnLocal.mem_integralGL_iff _ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [uni2, hb, zero_mem, one_mem]
  · rw [inv_uni]
    fin_cases i <;> fin_cases j <;> simp [uni2, hb', hb, zero_mem, one_mem]

theorem dg_mem {v : Pl} (a d : (Qv v)ˣ) (ha : ord (a : Qv v) = 0) (hd : ord (d : Qv v) = 0) :
    dg2 a d ∈ integralGL (Qv v) 2 := by
  have h1 := mem_O_of_ord a.ne_zero ha
  have h2 := mem_O_of_ord d.ne_zero hd
  have h3 : (a : Qv v)⁻¹ ∈ 𝒪[Qv v] :=
    mem_O_of_ord (inv_ne_zero a.ne_zero) (ord_inv_of_ord_zero a.ne_zero ha)
  have h4 : (d : Qv v)⁻¹ ∈ 𝒪[Qv v] :=
    mem_O_of_ord (inv_ne_zero d.ne_zero) (ord_inv_of_ord_zero d.ne_zero hd)
  refine (GLnLocal.mem_integralGL_iff _ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [dg2, h1, h2, zero_mem]
  · rw [invariant_under_antidiagonal_idele]
    fin_cases i <;> fin_cases j <;> simp [dg2, h3, h4, zero_mem]

abbrev pu (v' : Pl) (P : ℚˣ) : (Qv v')ˣ := Units.map (algebraMap ℚ (Qv v')).toMonoidHom P

theorem coe_pu {v' : Pl} {P : ℚˣ} {p : ℕ} (hP : (P : ℚ) = p) : ((pu v' P : (Qv v')ˣ) : Qv v') = (p : Qv v') := by
  simp [pu, hP]

theorem ord_pu (h0 : B0) {v v' : Pl} (hv : v' ≠ v) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) :
    ord ((pu v' P : (Qv v')ˣ) : Qv v') = 0 := by
  rw [coe_pu hP]; exact ord_p h0 hv

theorem ord_pu_inv (h0 : B0) {v v' : Pl} (hv : v' ≠ v) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) :
    ord (((pu v' P)⁻¹ : (Qv v')ˣ) : Qv v') = 0 := by
  rw [Units.val_inv_eq_inv_val]
  exact ord_inv_of_ord_zero (pu v' P).ne_zero (ord_pu h0 hv hP)

theorem map_inv_up_mem (h0 : B0) {v v' : Pl} (hv : v' ≠ v) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) (b : ℕ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v')) (uni2 (b : ℚ) * dg2 P 1)⁻¹ ∈ integralGL (Qv v') 2 := by
  rw [inv_uni_dg, map_mul, map_dg, map_uni]
  refine mul_mem (dg_mem _ _ ?_ (by simp [ord])) (uni_mem _ ?_)
  · have := ord_pu_inv h0 hv hP
    simpa [pu] using this
  · have : ((b : ℕ) : Qv v') ∈ 𝒪[Qv v'] := natCast_mem _ b
    simpa using neg_mem this

theorem map_inv_dg_mem (h0 : B0) {v v' : Pl} (hv : v' ≠ v) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v')) (dg2 1 P : GL (Fin 2) ℚ)⁻¹ ∈ integralGL (Qv v') 2 := by
  rw [inv_dg, map_dg]
  refine dg_mem _ _ (by simp [ord]) ?_
  have := ord_pu_inv h0 hv hP
  simpa [pu] using this

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical UpperHalfPlane

theorem up_map {v : Pl} {ϖ : (Qv v)ˣ} (hϖ : (ϖ : Qv v) = (pOf v : ℕ)) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) (b : ℕ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) (uni2 (b : ℚ) * dg2 P 1) = upm ϖ (b : Qv v) := by
  have : Units.map (algebraMap ℚ (Qv v)).toMonoidHom P = ϖ := Units.ext ((coe_pu hP).trans hϖ.symm)
  rw [map_mul, map_uni, map_dg, upm, map_one, this]
  simp

theorem dg_map {v : Pl} {ϖ : (Qv v)ˣ} (hϖ : (ϖ : Qv v) = (pOf v : ℕ)) {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) (dg2 1 P) = dg2 1 ϖ := by
  have : Units.map (algebraMap ℚ (Qv v)).toMonoidHom P = ϖ := Units.ext ((coe_pu hP).trans hϖ.symm)
  rw [map_dg, map_one, this]

theorem phi_up (h0 : B0) {k N : ℕ} [NeZero N] {f : ℍ → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {v : Pl} {ϖ : (Qv v)ˣ} (hϖ : (ϖ : Qv v) = (pOf v : ℕ)) {P : ℚˣ}
    (hP : (P : ℚ) = (pOf v : ℕ)) (b : ℕ) {t : G2} (ht : IsLoc2 v (upm ϖ (b : Qv v)) t) (x : GL (Fin 2) ℝ) :
    φ (realEmb x * t) = φ (realEmb ((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ * x)) := by
  have hh : IsLoc2 v (Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) (uni2 (b : ℚ) * dg2 P 1)) t := by
    rw [up_map hϖ hP]; exact ht
  have h10 : ((uni2 (b : ℚ) * dg2 P 1 : GL (Fin 2) ℚ)⁻¹ : GL (Fin 2) ℚ) 1 0 = 0 := by
    rw [inv_uni_dg]; simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((uni2 (b : ℚ) * dg2 P 1 : GL (Fin 2) ℚ)⁻¹ : GL (Fin 2) ℚ) 1 1 = 1 := by
    rw [inv_uni_dg]; simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hu := mem_level (N := N) hh (fun v' hv => map_inv_up_mem h0 hv hP b) h10
  rw [split_eq t ht.2.2 _ x, hL.left]
  have := hL.level _ hu 1 (fun v' => by simp [lf, ord]) (fun v' _ => by
    by_cases hv : v' = v
    · subst hv
      have h1 := glAt_u_self hh
      change _ = (glAt v' (uOf _ t)) 1 1
      rw [h1]; simp [lf]
    · have h1 := glAt_u_ne (γ := uni2 (b : ℚ) * dg2 P 1) ht hv
      change _ = (glAt v' (uOf _ t)) 1 1
      rw [h1]
      change _ = algebraMap ℚ (Qv v') (((uni2 (b : ℚ) * dg2 P 1 : GL (Fin 2) ℚ)⁻¹ : GL (Fin 2) ℚ) 1 1)
      rw [h11]; simp [lf]) (realEmb ((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ * x))
  rw [this]
  simp

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical UpperHalfPlane

theorem lf_det (v : Pl) (u : FiniteAdelicGL ℚ 2) :
    (lf v (GeneralLinearGroup.det u) : Qv v) = ((GeneralLinearGroup.det (glAt v u)) : (Qv v)ˣ) := by
  simp only [lf, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]
  change adeleAt v _ = _
  rw [RingHom.map_det]
  rfl

theorem phi_dg (h0 : B0) {k N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ} {ω : HeckeCharacter ℚ}
    {φ : G2 → ℂ} (hω : Om N χ ω) (hL : Lift k N f ω φ) {v : Pl} {ϖ : (Qv v)ˣ} (hϖ : (ϖ : Qv v) = (pOf v : ℕ))
    {P : ℚˣ} (hP : (P : ℚ) = (pOf v : ℕ)) (hN : ¬ pOf v ∣ N) {t : G2} (ht : IsLoc2 v (dg2 1 ϖ) t)
    (x : GL (Fin 2) ℝ) :
    φ (realEmb x * t) = χ ((pOf v : ℕ) : ZMod N) * φ (realEmb ((toReal (dg2 1 P))⁻¹ * x)) := by
  have hpr : (pOf v).Prime := (h0.1 v).2.2.1
  have hh : IsLoc2 v (Matrix.GeneralLinearGroup.map (algebraMap ℚ (Qv v)) (dg2 1 P)) t := by
    rw [dg_map hϖ hP]; exact ht
  have h10 : ((dg2 1 P : GL (Fin 2) ℚ)⁻¹ : GL (Fin 2) ℚ) 1 0 = 0 := by
    rw [inv_dg]; simp [dg2]
  have hu := mem_level (N := N) hh (fun v' hv => map_inv_dg_mem h0 hv hP) h10
  have hself : ∀ {v'}, v' = v → glAt v' (uOf (dg2 1 P) t) = 1 := by
    rintro v' rfl; exact glAt_u_self hh
  have hne : ∀ {v'}, v' ≠ v → glAt v' (uOf (dg2 1 P) t) = dg2 1 (pu v' P)⁻¹ := by
    intro v' hv
    rw [glAt_u_ne ht hv, inv_dg, map_dg]
    simp [pu]
  have hp0 : ∀ v' : Pl, ((pOf v : ℕ) : Qv v') ≠ 0 := fun v' => natCast_ne v' hpr.ne_zero
  set d : Afˣ := GeneralLinearGroup.det (uOf (dg2 1 P) t) with hd
  have hd_self : (lf v d : Qv v) = 1 := by
    rw [hd, lf_det, hself rfl]; simp
  have hd_ne : ∀ {v'}, v' ≠ v → (lf v' d : Qv v') = ((pOf v : ℕ) : Qv v')⁻¹ := by
    intro v' hv
    rw [hd, lf_det, hne hv, Matrix.GeneralLinearGroup.val_det_apply]
    simp [dg2, Matrix.det_fin_two, coe_pu hP]
  have hord : ∀ v', ord (lf v' d : Qv v') = 0 := by
    intro v'
    by_cases hv : v' = v
    · subst hv; rw [hd_self]; simp [ord]
    · rw [hd_ne hv]; exact ord_inv_of_ord_zero (hp0 v') (ord_p h0 hv)
  have h11 : ∀ v', pOf v' ∣ N → (lf v' d : Qv v') = glAt v' (uOf (dg2 1 P) t) 1 1 := by
    intro v' hdv
    have hv : v' ≠ v := by rintro rfl; exact hN hdv
    rw [hd_ne hv, hne hv]
    simp [dg2, coe_pu hP]
  have hlev := hL.level _ hu d hord h11 (realEmb ((toReal (dg2 1 P))⁻¹ * x))
  rw [split_eq t ht.2.2 _ x, hL.left, hlev]
  congr 1

  have hcop : Nat.Coprime (pOf v) N := (Nat.Prime.coprime_iff_not_dvd hpr).2 hN
  obtain ⟨n, m, hnm⟩ : ∃ n m : ℤ, ((pOf v : ℕ) : ℤ) * n + (N : ℤ) * m = 1 := by
    refine ⟨Nat.gcdA (pOf v) N, Nat.gcdB (pOf v) N, ?_⟩
    have := Nat.gcd_eq_gcd_ab (pOf v) N
    rw [hcop] at this
    simpa using this.symm
  have hval := hω.val d n hord (fun v' hdv => by
    have hv : v' ≠ v := by rintro rfl; exact hN hdv
    have hN0 : (N : Qv v') ≠ 0 := natCast_ne v' (NeZero.ne N)
    have hc : ((pOf v : ℕ) : Qv v') * n + (N : Qv v') * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Qv v') hnm
    have : (N : Qv v')⁻¹ * ((lf v' d : Qv v') - n) = m * ((pOf v : ℕ) : Qv v')⁻¹ := by
      rw [hd_ne hv]
      field_simp [hp0 v', hN0]
      linear_combination -hc
    rw [this]
    exact mul_mem (intCast_mem _ m) (mem_O_of_ord (inv_ne_zero (hp0 v')) (ord_inv_of_ord_zero (hp0 v') (ord_p h0 hv))))
  have hχ : χ ((pOf v : ℕ) : ZMod N) * χ ((n : ℤ) : ZMod N) = 1 := by
    rw [← map_mul]
    have : (((pOf v : ℕ) : ZMod N)) * ((n : ℤ) : ZMod N) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hnm
      push_cast at this
      simpa using this
    rw [this, map_one]
  have hne0 : χ ((n : ℤ) : ZMod N) ≠ 0 := fun h => by rw [h, mul_zero] at hχ; exact zero_ne_one hχ
  exact mul_right_cancel₀ hne0 (hval.trans hχ.symm)

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical UpperHalfPlane

theorem archLift_tri (k : ℕ) (f : ℍ → ℂ) {g x : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (hx : 0 < x.det.val)
    (h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0) :
    archLift (k : ℤ) f (g * x) = (Real.sqrt g.det.val : ℂ) ^ (k : ℤ) * (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ) ^ (-(k : ℤ)) *
      ((Real.sqrt x.det.val : ℂ) ^ (k : ℤ) * denom x (UpperHalfPlane.I : ℂ) ^ (-(k : ℤ))) * f (g • x • UpperHalfPlane.I) := by
  have hd : denom g ((x • UpperHalfPlane.I : ℍ) : ℂ) = (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ) := by
    simp [denom, h10]
  rw [archLift, map_mul, Units.val_mul, Real.sqrt_mul hg.le, Complex.ofReal_mul, mul_zpow, mul_smul,
    GroundTheory.Automorphic.GL2Classical.denom_mul_of_det_pos _ hx, mul_zpow, hd]
  ring

theorem up_facts {p : ℕ} {P : ℚˣ} (hP : (P : ℚ) = p) (b : ℕ) :
    ((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ : GL (Fin 2) ℝ).det.val = (p : ℝ)⁻¹ ∧
    (((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧
    (((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 ∧
    (((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (p : ℝ)⁻¹ ∧
    (((toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(b : ℝ) * (p : ℝ)⁻¹ := by
  rw [← map_inv, inv_uni_dg, det_toReal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [uni2, dg2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hP]
  all_goals
    rw [toReal_apply]
    simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, hP]
    try ring

theorem dg_facts {p : ℕ} {P : ℚˣ} (hP : (P : ℚ) = p) :
    ((toReal (dg2 1 P))⁻¹ : GL (Fin 2) ℝ).det.val = (p : ℝ)⁻¹ ∧
    (((toReal (dg2 1 P))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧
    (((toReal (dg2 1 P))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (p : ℝ)⁻¹ ∧
    (((toReal (dg2 1 P))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 ∧
    (((toReal (dg2 1 P))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
  rw [← map_inv, inv_dg, det_toReal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [dg2, Matrix.det_fin_two, hP]
  all_goals
    rw [toReal_apply]
    simp [dg2, hP]

theorem coe_smul_tri {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z + (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
      ((((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z + (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos hg]
  simp [num, denom]

theorem lam_eq {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (p : ℝ) ^ (1 - (k : ℝ) / 2) = (Real.sqrt (p : ℝ)⁻¹) ^ k * p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : (Real.sqrt (p : ℝ)⁻¹) ^ k = (p : ℝ) ^ (-((k : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow hp'.le,
      ← Real.rpow_neg hp'.le]
    congr 1
    ring
  rw [h1, sub_eq_add_neg, Real.rpow_add hp', Real.rpow_one]
  ring

end GlobalTheory.CompanionTheory.RSq

namespace GlobalTheory.CompanionTheory.RSq

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GL2Classical UpperHalfPlane

theorem f3a : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates := by
  intro h0 k N _ hk χ hχ f a hf ha ω φ hω hL v ϖ hϖ t t' ht ht' x hx
  have hpr : (pOf v).Prime := (h0.1 v).2.2.1
  have hp0 : (pOf v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpr.ne_zero
  have hpC : (pOf v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpr.ne_zero
  have hpos : (0 : ℝ) < (pOf v : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hpr.pos)
  let P : ℚˣ := Units.mk0 (pOf v : ℚ) (Nat.cast_ne_zero.2 hpr.ne_zero)
  have hP : (P : ℚ) = (pOf v : ℕ) := rfl
  let δ : ℕ → GL (Fin 2) ℝ := fun b => (toReal (uni2 (b : ℚ) * dg2 P 1))⁻¹
  let δ' : GL (Fin 2) ℝ := (toReal (dg2 1 P))⁻¹
  have hδ := fun b => up_facts hP b
  have hδ' := dg_facts hP
  let z : ℍ := x • UpperHalfPlane.I
  let A : ℂ := (Real.sqrt x.det.val : ℂ) ^ (k : ℤ) * denom x (UpperHalfPlane.I : ℂ) ^ (-(k : ℤ))
  let S : ℂ := ((Real.sqrt (pOf v : ℝ)⁻¹ : ℝ) : ℂ) ^ k
  have hd1 : ∀ b, 0 < (δ b).det.val := fun b => by rw [(hδ b).1]; exact hpos
  have hd2 : 0 < δ'.det.val := by rw [hδ'.1]; exact hpos
  have hw : ∀ b : ℕ, ((δ b • z : ℍ) : ℂ) = ((z : ℂ) - b) / (pOf v : ℕ) := fun b => by
    rw [coe_smul_tri (hd1 b)]
    obtain ⟨-, h10, h11, h00, h01⟩ := hδ b
    simp only [δ] at *
    rw [h10, h11, h00, h01]
    push_cast
    field_simp
    ring
  have hw' : ((δ' • z : ℍ) : ℂ) = (pOf v : ℕ) * z := by
    rw [coe_smul_tri hd2]
    obtain ⟨-, h10, h11, h00, h01⟩ := hδ'
    simp only [δ'] at *
    rw [h10, h11, h00, h01]
    push_cast
    field_simp
    ring
  have hsum := GlobalTheory.CompanionTheory.HeckeSum.hecke_sum k N χ f a hf ha (pOf v) hpr z (fun b => δ b • z) hw (δ' • z) hw'
  have hb : ∀ b, φ (realEmb x * t b) = S * A * f (δ b • z) := fun b => by
    rw [phi_up h0 hL hϖ hP b (ht b) x]
    have hdet : 0 < (δ b * x).det.val := by
      rw [map_mul, Units.val_mul]; exact mul_pos (hd1 b) hx
    rw [hL.real _ hdet, archLift_tri k f (hd1 b) hx (hδ b).2.1, (hδ b).2.2.1, (hδ b).1]
    simp [S, A, z]
  have hz : φ (realEmb x) = A * f z := by
    rw [hL.real _ hx, archLift]
    simp only [A, z]
    ring
  have hlam : lamOf k a v = a (pOf v) * (S * (pOf v : ℂ)) := by
    rw [lamOf, lam_eq hpr.pos k]
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum, hsum, hz, hlam]
  by_cases hN : pOf v ∣ N
  · have hχ0 : χ ((pOf v : ℕ) : ZMod N) = 0 := by
      apply χ.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      intro hc
      exact hpr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hN)
    rw [if_pos hN, hχ0]
    ring
  · rw [if_neg hN, phi_dg h0 hω hL hϖ hP hN ht' x]
    have hdet : 0 < (δ' * x).det.val := by
      rw [map_mul, Units.val_mul]; exact mul_pos hd2 hx
    rw [hL.real _ hdet, archLift_tri k f hd2 hx hδ'.2.1, hδ'.2.2.1, hδ'.1]
    have hk1 : (pOf v : ℂ) * (pOf v : ℂ) ^ (k - 1) = (pOf v : ℂ) ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    have hpk : (((pOf v : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(k : ℤ)) = (pOf v : ℂ) ^ k := by
      push_cast
      rw [_root_.zpow_neg, _root_.inv_zpow, inv_inv, zpow_natCast]
    rw [hpk]
    simp only [S, A, z, zpow_natCast]
    linear_combination (-(Complex.ofReal (Real.sqrt (pOf v : ℝ)⁻¹) ^ k * ((Real.sqrt x.det.val : ℂ) ^ k * denom x (UpperHalfPlane.I : ℂ) ^ (-(k : ℤ))) * χ ((pOf v : ℕ) : ZMod N) * f (δ' • x • UpperHalfPlane.I))) * hk1

end GlobalTheory.CompanionTheory.RSq
