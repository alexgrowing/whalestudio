import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeMemDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.auPsiCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → Continuous ((X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le)) → ∀ (v : W.Vl l T.L) (i : Fin 4), Continuous (x.psi v i) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx hcont v i
  have hxe : x = Link.pt φ y := AlgHom.ext fun b => hx b
  subst hxe
  have hκc := auCont c' K.κ K.κ_cont
  have hβc := auCont c' K.β K.β_cont
  have htw : Continuous fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    have he : (fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) = fun g =>
        ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) *
          ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.β g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n := by
      funext g
      rw [K.twc_val]
      simp [W.pushCh]
    rw [he]
    exact (Units.continuous_val.comp hκc).mul ((Units.continuous_val.comp hβc).pow n)
  have hval : Continuous fun g : ↥(Dec (K.s.A ↑v)) =>
      (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    have heq : (fun g : ↥(Dec (K.s.A ↑v)) => (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
        fun g : ↥(Dec (K.s.A ↑v)) => ((K.twc n (g : G (↥T.L) Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) *
          (X.P.map ↑y).ψ (K.e v) i (resLe T.F_le (g : G (↥T.L) Ω)) := by
      funext g
      apply hφ.psi_val y v i g
      rw [resLe_mem_Dec, ← K.hA v]
      exact g.2
    rw [heq]
    refine (htw.comp continuous_subtype_val).mul ?_
    unfold PD.ψ
    exact ((continuous_const.matrix_mul (hcont.comp continuous_subtype_val)).matrix_mul
      continuous_const).matrix_elem i i
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have hinv : (fun g : ↥(Dec (K.s.A ↑v)) => ((((Link.pt φ y).psi v i g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
      fun g => (((Link.pt φ y).psi v i g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    funext g
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv
