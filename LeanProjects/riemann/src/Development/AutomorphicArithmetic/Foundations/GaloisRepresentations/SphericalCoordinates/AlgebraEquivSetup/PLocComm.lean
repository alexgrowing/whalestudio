import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLocComm :
    LocComm := by
  intro E _ _ _ n w hw x g hg
  have key : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) * comp u g = comp u g * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) := by
    intro u
    by_cases hu : GlobalTheory.Cong.Apart u w
    · rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw hu, one_mul, mul_one]
    · have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
        by_contra h
        exact hu h
      obtain rfl | rfl := GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu'
      · rw [hg, one_mul, mul_one]
      · have hmem : ((mat g).val.map (conjFin (conjE E)))ᵀ * (mat g).val =
            finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E)) := g.2
        have h2 := congrArg (RingHom.mapMatrix (pLoc E w)) hmem
        have e1 : RingHom.mapMatrix (pLoc E w) (((mat g).val.map (conjFin (conjE E)))ᵀ) =
            ((comp (conjSrc (conjE E) w) g).val.map (conjLoc (conjE E) w))ᵀ := by
          refine Matrix.ext fun i k => ?_
          exact pLoc_conjFin (conjE E) _ w
        have e2 : RingHom.mapMatrix (pLoc E w) (mat g).val = 1 := by
          have : (comp w g).val = 1 := by rw [hg]; rfl
          exact this
        have e3 : RingHom.mapMatrix (pLoc E w) (finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E))) =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          ext i k
          by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
        rw [map_mul, e1, e2, mul_one, e3] at h2
        have hM : RingHom.mapMatrix (conjLoc (conjE E) w) (comp (conjSrc (conjE E) w) g).val =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          have := congrArg Matrix.transpose h2
          rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this
          exact this
        have hinj : Function.Injective (RingHom.mapMatrix (conjLoc (conjE E) w) :
            Matrix (Fin n) (Fin n) _ →+* Matrix (Fin n) (Fin n) _) := by
          intro a b hab
          refine Matrix.ext fun i k => ?_
          exact (conjLoc (conjE E) w).injective (congrFun (congrFun hab i) k)
        apply Units.ext
        apply hinj
        rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hM, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.EulerTw.matrix_ext_pLoc E n fun v => ?_)) ?_)
  · have h3 : (comp v (UpperTheory.Gal.CertificateRingHomMap.loc hw x * g)).val = (comp v (g * UpperTheory.Gal.CertificateRingHomMap.loc hw x)).val := by
      rw [map_mul, map_mul, key v]
    exact h3
  · exact mul_comm (sim (UpperTheory.Gal.CertificateRingHomMap.loc hw x)) (sim g)
