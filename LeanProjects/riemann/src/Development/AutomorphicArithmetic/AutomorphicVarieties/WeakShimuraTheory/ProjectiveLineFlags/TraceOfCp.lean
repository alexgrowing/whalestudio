import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TrNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_of_cp {R k : Type} [CommRing R] [Field k] (f : R →+* k) (M : Matrix (Fin 4) (Fin 4) R) (a : Fin 4 → k)
    (h : M.charpoly.map f = ∏ i, (X - C (a i))) : f M.trace = ∑ i, a i := by
  have h1 := Matrix.trace_eq_neg_charpoly_nextCoeff (M.map f)
  rw [Matrix.charpoly_map, h, Polynomial.prod_X_sub_C_nextCoeff, neg_neg] at h1
  rw [← h1]
  simp [Matrix.trace, map_sum]

theorem UpperTheory.V.Ws.P1.irrL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (x : W.Point K.r) (Q : PD T.ι (G T.F Ω) x.A), T.PsPair h x.K Q → K.IsRho x.ρ Q → Irr (mapRep (algebraMap x.A x.Fr) Q.r) →
          U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) := by
  intro Ω _ _ _ l hl c D T c' h K x Q hP hρ hI
  obtain ⟨hrange, -, -, hidx, hres, -⟩ := UpperTheory.V.Ws.P1.towerGal D T
  have hsurj := (UpperTheory.V.Ws.phiKer K.V).1
  have htow : ∀ a : c'.O, algebraMap (ResidueField c'.O) x.K (residue c'.O a) = algebraMap c'.O x.K a :=
    fun a => (IsScalarTower.algebraMap_apply c'.O (ResidueField c'.O) x.K a).symm
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have h2 : (2 : x.Fr) ≠ 0 := by
    haveI := (UpperTheory.V.Ws.P1.coefRes c').2.1
    intro h0
    have h1 : (2 : x.A) = 0 := hinj (by rw [map_ofNat, map_zero]; exact h0)
    have h3 : (2 : x.K) = 0 := by
      have := congrArg (PowerSeries.constantCoeff : PowerSeries x.K →+* x.K) h1
      rwa [map_ofNat, map_zero] at this
    have h4 : ((2 : ℕ) : ResidueField c'.O) = 0 :=
      (algebraMap (ResidueField c'.O) x.K).injective (by rw [map_natCast, map_zero]; exact_mod_cast h3)
    exact K.s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h4))
  let χ : Fin (3 + 1) → G T.F Ω →* x.Kˣ := fun i =>
    W.pushCh ((algebraMap c'.O x.K).comp (inc h)) ((chi D T.pr i).comp (resQ T.F))
  have hχ : Function.Injective fun i => (χ i).comp T.GalL.subtype := by
    intro i j hij
    refine K.r.chib_inj (MonoidHom.ext fun y => ?_)
    obtain ⟨g, rfl⟩ := hsurj y
    have hg : resLe T.F_le g ∈ T.GalL := hrange ▸ ⟨g, rfl⟩
    have e : algebraMap c'.O x.K (inc h (chi D T.pr i (resQ T.L g))) =
        algebraMap c'.O x.K (inc h (chi D T.pr j (resQ T.L g))) := by
      have e1 := congrArg Units.val (DFunLike.congr_fun hij ⟨_, hg⟩)
      rw [← (hres g).1]
      exact e1
    apply Units.ext
    apply (algebraMap (ResidueField c'.O) x.K).injective
    rw [K.chib, K.chib, htow, htow, map_mul, map_mul, e]
  have htr : T.GalL = ⊤ ∨ ∃ g, g ∉ T.GalL ∧ (mapRep (algebraMap x.A x.Fr) Q.r g).trace ≠ 0 := by
    refine (UpperTheory.V.Ws.P1.trNe T.GalL χ hχ).imp id fun ⟨g, hg, hs⟩ => ⟨g, hg, fun h0 => hs ?_⟩
    have e1 : (Q.r g).trace = 0 := hinj (by
      rw [map_zero, ← h0]
      simp [Matrix.trace, map_sum])
    have e2 := trace_of_cp _ _ _ (hP.cp g)
    rw [e1, map_zero] at e2
    exact e2.symm
  have hM := UpperTheory.V.Ws.P1.irrTr (algebraMap x.Fr x.Fb) T.GalL _ h2 hI hidx htr
  intro U hW
  refine hM U fun y hy v hv => ?_
  rw [← hrange] at hy
  obtain ⟨g, rfl⟩ := hy
  have h5 := hW (K.V.pr g) trivial v hv
  let u : x.Fbˣ := Units.map (((algebraMap x.Fr x.Fb).comp ((algebraMap x.A x.Fr).comp (algebraMap c'.O x.A)) : c'.O →+* x.Fb) : c'.O →* x.Fb) (K.κ g)
  have e : W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF) (K.V.pr g) =
      (u : x.Fb) • mapRep (algebraMap x.Fr x.Fb) (mapRep (algebraMap x.A x.Fr) Q.r) (resLe T.F_le g) := by
    ext i j
    have e0 := congrFun (congrFun (hρ g) i) j
    show algebraMap x.Fr x.Fb (algebraMap x.A x.Fr (W.mat x.ρ (K.V.pr g) i j)) = _
    rw [e0, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    rfl
  rw [e, Matrix.smul_mulVec] at h5
  exact (U.smul_mem_iff u.ne_zero).1 h5
