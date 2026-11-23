import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.W2.Seed.pCongConj :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → CongConj := by
  intro _ E _ _ _ n N w g hs hc i k
  have hrel := comp_rel g w
  rw [hs, Units.val_one, map_one, map_one, one_smul] at hrel
  have hG : ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ = ((comp w g)⁻¹).val := by
    calc ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ
        = ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ * ((comp w g).val * ((comp w g)⁻¹).val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, Matrix.one_mul]
  have hv := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2
  have hent : conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k) = (((comp w g)⁻¹).val - 1) k i := by
    rw [← hG]
    by_cases hik : i = k
    · subst hik; simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, Matrix.one_apply, hik, Ne.symm hik]
  calc Valued.v (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)
      = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)) := (hv _).symm
    _ = Valued.v ((((comp w g)⁻¹).val - 1) k i) := by rw [hent]
    _ ≤ Valued.v (N : w.adicCompletion E) := hc k i
    _ = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E)) := by
          rw [map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) N]
    _ = Valued.v (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E) := hv _
