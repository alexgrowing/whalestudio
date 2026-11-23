import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep

open GroundTheory.Automorphic.HarishChandra in
private noncomputable def UpperTheory.V.Af.CuspFin.vermaRep {n : ℕ} (lam : Fin n → ℂ) :
    U n →ₐ[ℂ] Module.End ℂ (U n ⧸ vermaIdeal lam) where
  toFun x := (vermaIdeal lam).mapQ (vermaIdeal lam) (LinearMap.mulLeft ℂ x)
    (fun _ hy => mul_mem_vermaIdeal lam x hy)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (a * b * y) : U n ⧸ vermaIdeal lam) = Submodule.Quotient.mk (a * (b * y))
    rw [mul_assoc]
  map_zero' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_add' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk ((a + b) * y) : U n ⧸ vermaIdeal lam) =
      Submodule.Quotient.mk (a * y) + Submodule.Quotient.mk (b * y)
    rw [add_mul, Submodule.Quotient.mk_add]
  commutes' r := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (algebraMap ℂ (U n) r * y) : U n ⧸ vermaIdeal lam) =
      r • Submodule.Quotient.mk y
    rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.vermaRep_one {n : ℕ} (lam : Fin n → ℂ) (x : U n) :
    UpperTheory.V.Af.CuspFin.vermaRep lam x (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x := by
  change Submodule.Quotient.mk (x * 1) = _
  rw [mul_one]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.one_notMem_vermaIdeal {n : ℕ} (lam : Fin n → ℂ) :
    (1 : U n) ∉ vermaIdeal lam := by
  intro h
  have h0 := vermaCoord_vermaIdeal lam h
  have hnu : ¬ HasUpper (0 : Fin n × Fin n →₀ ℕ) := by
    rintro ⟨b, -, hne⟩
    exact hne rfl
  have hd : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [← canon_zero, vermaCoord_canon_of_not lam hnu, hd, Finsupp.single_eq_zero] at h0
  simp at h0

open GroundTheory.Automorphic.HarishChandra UpperTheory.V.Af.CuspFin in
theorem UpperTheory.harishChandraProj_quantumDet_eq_prod :
    ∀ (n : ℕ) (u : ℂ), GroundTheory.Automorphic.HarishChandra.hcProjLin (Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) = ∏ k : Fin n, (MvPolynomial.C (u - (k : ℂ)) + MvPolynomial.X k) := by
  intro n u
  refine MvPolynomial.funext fun lam => ?_
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := fun a b c d => e_mul_sub_mul (a, b) (c, d)
  have hgl' : Formalism.REAL.GlRel (fun i j : Fin n => vermaRep lam (e (i, j))) := fun a b c d => by
    have h := congrArg (vermaRep lam) (hgl a b c d)
    simp only [map_sub, map_mul, apply_ite (vermaRep lam), map_zero] at h
    exact h
  have hup : ∀ a, IsUpper a → vermaRep lam (e a) (Submodule.Quotient.mk 1) = 0 := fun a ha => by
    rw [vermaRep_one, Submodule.Quotient.mk_eq_zero]
    exact nPlusU_le_vermaIdeal lam (Submodule.subset_span ⟨1, a, ha, one_mul _⟩)
  have hH : ∀ k, vermaRep lam (e (k, k)) (Submodule.Quotient.mk 1) =
      lam k • (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) := fun k => by
    rw [vermaRep_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← Algebra.algebraMap_eq_smul_one]
    simpa using mul_e_sub_mem_vermaIdeal lam 1 k
  have h1 := rep_apply_of_highestWeight (vermaRep lam) lam hup hH
    (z := Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u)
    (fun k => (Formalism.REAL.qDetCentral _ n _ hgl u k k).symm)
  have h2 := Formalism.REAL.qDetHW _ n _ lam (Submodule.Quotient.mk 1) hgl'
    ⟨hH, fun a b hab => hup (a, b) hab⟩ u
  rw [map_qdet, h2] at h1
  have hv : (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) ≠ 0 := fun h =>
    one_notMem_vermaIdeal lam ((Submodule.Quotient.mk_eq_zero _).1 h)
  rw [← smul_left_injective ℂ hv h1]
  simp
