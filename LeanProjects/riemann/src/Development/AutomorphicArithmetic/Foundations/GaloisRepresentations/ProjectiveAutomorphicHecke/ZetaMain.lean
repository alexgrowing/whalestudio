import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.NormGlob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.NormLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.KPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.NormEmb

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap finiteAdeleMap_algebraMap continuous_finiteAdeleMap)
open GlobalTheory.LFun (KGL)

namespace UpperTheory.Gal.CertificateRingHomMap

open ZetaNonvanishing₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private instance : Nonempty (Plc E) := (GlobalTheory.LvT.Inh.ResFin.infinite_places E).nonempty

private def tau (x : E) : (Af E)ˣ →* (Af E)ˣ :=
  (Units.map ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).toMonoidHom).comp (fN (Kx x) E)

private theorem tau_val (x : E) (y : (Af E)ˣ) :
    (tau x y : Af E) = conjFin (conjE E) (finiteAdeleMap (Kx x) E ((fN (Kx x) E y : (Af (Kx x))ˣ) : Af (Kx x))) := rfl

private theorem scalar_val {A : Type} [CommRing A] (n : ℕ) (t : Aˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : A) • (1 : Matrix (Fin n) (Fin n) A) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, h, Matrix.one_apply]

private theorem sim_scalar {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) (t : Aˣ) (s : Bˣ)
    (h : σ t * t = i s) : (GeneralLinearGroup.scalar (Fin n) t, s) ∈ Sim σ i n := by
  refine mem_Sim.2 ?_
  rw [scalar_val, ← h]
  ext a b
  by_cases e : a = b <;> simp [e, Matrix.one_apply, Matrix.mul_apply, apply_ite σ, eq_comm]

private def zeta (n : ℕ) {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : (Af E)ˣ →* GUf E n :=
  (((GeneralLinearGroup.scalar (Fin n)).comp (tau x)).prod (fN ℚ E)).codRestrict _ fun y => sim_scalar _ _ n _ _ (by
    rw [tau_val, (conjLoc E _ (Classical.arbitrary _)).2.2.2.1, quadConj E d x hd hx, (normGlob ℚ (Kx x)).2.2 E y])

private theorem comp_zeta (n : ℕ) {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (y : (Af E)ˣ) (u : Plc E) :
    comp u (zeta n hd hx y) = GeneralLinearGroup.scalar (Fin n) (Units.map (pLoc E u).toMonoidHom (tau x y)) := by
  refine Units.ext ?_
  rw [scalar_val]
  ext i j : 1
  change pLoc E u ((GeneralLinearGroup.scalar (Fin n) (tau x y)).val i j) = _
  rw [scalar_val]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem zetaEx_holds : ZetaEx := by
  intro E _ _ _ n d x hd hx
  obtain ⟨k1, k2⟩ := kPlace E d x hd hx
  refine ⟨zeta n hd hx, ?_, fun y g => ?_, fun k => ?_, fun w y u h => ?_, fun w y h u => ?_, fun w y h hw u hu => ?_⟩
  · have h1 : Continuous (tau x) := (Units.continuous_map (f := ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).toMonoidHom)
      (((conjLoc E 0 (Classical.arbitrary _)).2.2.2.2).comp continuous_finiteAdeleMap)).comp (normGlob (Kx x) E).1
    have h2 : Continuous (GeneralLinearGroup.scalar (Fin n) : (Af E)ˣ → GL (Fin n) (Af E)) :=
      Units.continuous_map (Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id))
    exact Continuous.subtype_mk ((h2.comp h1).prodMk (normGlob ℚ E).1) _
  · refine Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))
    change (GeneralLinearGroup.scalar (Fin n) (tau x y)).val * _ = _ * (GeneralLinearGroup.scalar (Fin n) (tau x y)).val
    rw [scalar_val, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨e1, e2, e3, e4⟩ := normEmb E d x hd hx k
    let t : Eˣ := Units.map (((conjE E).toRingHom.comp (algebraMap (Kx x) E)).toMonoidHom.comp (Algebra.norm (Kx x))) k
    let s : ℚˣ := Units.map (Algebra.norm ℚ) k
    refine ⟨⟨(GeneralLinearGroup.scalar (Fin n) t, s), sim_scalar _ _ n t s ?_, e3⟩, t, ?_, scalar_val n t, e1, e2⟩
    · refine Eq.trans ?_ e4
      congr 1
      exact IsCMField.complexConj_apply_apply E _
    · refine Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ((normGlob ℚ E).2.1 k)))
      change (GeneralLinearGroup.scalar (Fin n) (tau x (diagF E k))).val =
        (GeneralLinearGroup.scalar (Fin n) t).val.map (algebraMap E (Af E))
      rw [scalar_val, scalar_val, tau_val, (normGlob (Kx x) E).2.1 k, finiteAdeleMap_algebraMap, conjFin_algebraMap]
      ext i j : 1
      by_cases h : i = j
      · simp only [h, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, map_apply]
        rfl
      · simp [h, Matrix.one_apply]
  · rw [comp_zeta]
    have : Units.map (pLoc E u).toMonoidHom (tau x (sgl w y)) = 1 :=
      Units.ext ((conjLoc E _ u).1 ((normLoc (Kx x) E w y (cj u)).1 fun e => h ((k1 _ _).2 e)))
    rw [this, map_one]
  · rw [comp_zeta]
    have h1 : Valued.v ((Units.map (pLoc E u).toMonoidHom (tau x (sgl w y)) : (u.adicCompletion E)ˣ) : u.adicCompletion E) = 1 :=
      (conjLoc E _ u).2.1.trans ((normLoc (Kx x) E w y (cj u)).2.1 h)
    generalize Units.map (pLoc E u).toMonoidHom (tau x (sgl w y)) = t at h1
    have h2 : Valued.v ((t⁻¹ : (u.adicCompletion E)ˣ) : u.adicCompletion E) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have key : ∀ (t : (u.adicCompletion E)ˣ), Valued.v (t : u.adicCompletion E) = 1 → ∀ i j,
        Valued.v ((GeneralLinearGroup.scalar (Fin n) t).val i j) ≤ 1 := fun t ht i j => by
      rw [scalar_val]
      by_cases e : i = j <;> simp [e, Matrix.one_apply, ht]
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨key t h1, by rw [← map_inv]; exact key _ h2⟩
  · refine ⟨_, by rw [comp_zeta, scalar_val], ?_⟩
    exact ((conjLoc E _ u).2.1.trans ((normLoc (Kx x) E w y (cj u)).2.2 h ((k1 _ _).1 hu) (k2 w hw))).trans
      ((conjLoc E 0 u).2.2.1 _).symm

end UpperTheory.Gal.CertificateRingHomMap
