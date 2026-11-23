import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v : W.Vl l T.L, W.HasFlag ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) fun i => W.pushCh (algebraMap X.B X.A) (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v
  have hlow := X.pair.low (K.e v)
  have h1 : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := by
    have h0 := hlow.1
    simpa [UpperTheory.V.GradeZeroInterpolatingElement.IsGSp] using h0
  have h2 : X.P.n (K.e v) * adj (X.P.n (K.e v)) = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩, fun s => ?_⟩
  obtain ⟨s, hs⟩ := s
  have hs' : resLe T.F_le s ∈ (T.fr ∅).Gv (K.e v) := by
    show resLe T.F_le s ∈ Dec (F := T.F) (T.pl (K.e v))
    rw [← K.hA v]
    exact hs
  have hval : (((⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A) *
      ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) ⟨s, hs⟩ *
      (⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A)⁻¹ : GL (Fin 4) X.A) :
        Matrix (Fin 4) (Fin 4) X.A) =
      (algebraMap c'.O X.A (K.sc n s)) • (adj (X.P.n (K.e v)) * X.P.r (resLe T.F_le s) * X.P.n (K.e v)) := by
    simp [UpperTheory.V.Ws.Link.rho_apply, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, X.pair.flag (K.e v) _ hs' i j hij, smul_zero]
  · rw [hval, Matrix.smul_apply]
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i ⟨s, hs⟩, map_mul, ← IsScalarTower.algebraMap_apply, X.ψ_map _ _ _ hs', smul_eq_mul]
    rfl
