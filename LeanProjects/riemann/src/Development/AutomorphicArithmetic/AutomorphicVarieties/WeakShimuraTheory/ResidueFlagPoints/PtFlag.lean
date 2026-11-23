import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem ptFlag_adj_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : M4 R) :
    adj (u.map f) = (adj u).map f := by
  ext i j
  simp only [Matrix.map_apply, adj_apply]
  rw [map_zsmul]

theorem UpperTheory.V.Ws.Pt.ptFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp (Dec (F := T.L) (K.s.A v)).subtype) ((Link.pt φ y).psi v) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y v
  have hpair := X.pair
  have hlow := hpair.low (K.e v)
  have hadj : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := Pp.adj_mul_self hlow.1
  have hr : ∀ t, (X.P.map (y : X.A →+* PadicAlgCl l)).r t = (X.P.r t).map (y : X.A →+* PadicAlgCl l) :=
    fun t => rfl
  have hu : adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) = 1 := by
    rw [ptFlag_adj_map, ← Matrix.map_mul, hadj,
      Matrix.map_one _ (map_zero (y : X.A →+* PadicAlgCl l)) (map_one (y : X.A →+* PadicAlgCl l))]
  have hu' := mul_eq_one_comm.mp hu
  have hM : ∀ t, adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.r t).map (y : X.A →+* PadicAlgCl l) * (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)
      = (adj (X.P.n (K.e v)) * X.P.r t * X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) := by
    intro t
    rw [ptFlag_adj_map, Matrix.map_mul, Matrix.map_mul]
  refine ⟨⟨_, _, hu, hu'⟩, fun s => ?_⟩
  have hs : resLe T.F_le (s : G T.L Ω) ∈ Dec (T.pl (K.e v)) := by
    rw [resLe_mem_Dec, ← K.hA v]
    exact s.2
  have hval : (((⟨_, _, hu, hu'⟩ * ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp
      (Dec (F := T.L) (K.s.A v)).subtype) s * (⟨_, _, hu, hu'⟩)⁻¹ : GL (Fin 4) (PadicAlgCl l))) :
        Matrix (Fin 4) (Fin 4) (PadicAlgCl l))
      = (((K.twc n) (s : G T.L Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) •
        (adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
          (X.P.r (resLe T.F_le (s : G T.L Ω))).map (y : X.A →+* PadicAlgCl l) *
          (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) := by
    rw [Units.val_mul, Units.val_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, Link.rho_val, hr]
    simp only [Units.inv_mk, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, hM, Matrix.map_apply, hpair.flag (K.e v) _ hs i j hij, map_zero, smul_zero]
  · rw [hval, Matrix.smul_apply, hφ.psi_val y v i s hs, smul_eq_mul]
    rfl
