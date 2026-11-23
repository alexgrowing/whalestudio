import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem psi_map' {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R')
    (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  have hadj : adj ((P.n v).map f) = (adj (P.n v)).map f := by
    ext a b
    simp [adj_apply, Matrix.map_apply, map_zsmul]
  have hr : (mapRep f P.r) s = (P.r s).map f := by
    ext a b
    simp [mapRep_apply]
  change (adj ((P.n v).map f) * (mapRep f P.r) s * (P.n v).map f) i i = f ((adj (P.n v) * P.r s * P.n v) i i)
  rw [hadj, hr, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

theorem UpperTheory.V.Ws.auPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) ∧ ((g : G T.L Ω) ∈ Ine (F := T.L) (K.s.A v) → resLe T.F_le g ∈ Ine (F := T.F) (T.pl (K.e v))) ∧ ((x.psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (K.κ g * K.β g ^ n) * (X.P.map (y : X.A →+* PadicAlgCl l)).ψ (K.e v) i (resLe T.F_le g) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx v i g
  have hd : resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) := by
    rw [← K.hA v]; exact g.2
  refine ⟨hd, fun hg => by rw [← K.hA v]; exact hg, ?_⟩
  have h1 : ((x.psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = x (B.u.ψ v i g : B.B) := rfl
  rw [h1, hx, hφ.2 v i g, map_mul, map_mul, X.ψ_map _ _ _ hd, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  exact congrArg _ (psi_map' X.P (y : X.A →+* PadicAlgCl l) (K.e v) i _).symm
