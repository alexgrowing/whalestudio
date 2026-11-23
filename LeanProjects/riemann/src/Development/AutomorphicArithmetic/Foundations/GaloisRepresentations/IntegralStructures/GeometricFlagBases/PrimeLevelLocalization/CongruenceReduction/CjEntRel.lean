import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

private theorem cjEnt_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.cjEnt :
    UpperTheory.Gal.Int.Geo.Pl.Tj.CjEnt := by
  intro E _ _ _ n g w i k
  refine ⟨GlobalTheory.SplitPts.conjSrc_conjSrc_cm w, ?_⟩
  have hrel := cjEnt_rel g w
  have hGt : ((comp (cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ)) •
        (comp w g⁻¹).val := by
    rw [map_inv]
    calc _ = ((comp (cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
          ((comp w g).val * ((comp w g)⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, smul_mul_assoc, Matrix.one_mul]
  have h := congrFun (congrFun hGt k) i
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [← (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2, h]
  rfl
