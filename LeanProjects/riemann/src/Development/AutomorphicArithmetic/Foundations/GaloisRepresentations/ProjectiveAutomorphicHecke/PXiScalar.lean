import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Formalism.LocalToGlobal.Columns.InvariantSubspaceNonzeroXOfRegular

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pXiScalar_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar := by
  intro E _ _ _ n W j y s t hy v
  have hy' : y = Formalism.L2.Col.brpSc E t := Units.ext (by rw [hy, Formalism.L2.Col.brpSc_coe])
  have hinv : y⁻¹ = Formalism.L2.Col.brpSc E t⁻¹ := by
    rw [hy']
    exact (map_inv (Units.map (algebraMap E (Matrix (Fin n) (Fin n) E) : E →* Matrix (Fin n) (Fin n) E)) t).symm
  have hemb : embAll E n y⁻¹ = fun u => Formalism.L2.Col.brpSc ℂ (Units.map (u.embedding : E →* ℂ) t⁻¹) := by
    funext u
    ext i k
    rw [hinv]
    change ((((Formalism.L2.Col.brpSc E t⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).map u.embedding) i k = _
    rw [Formalism.L2.Col.brpSc_coe, Formalism.L2.Col.brpSc_coe]
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hr := Formalism.L2.Col.tensorWeights_scalar_action (K := ℂ) W (fun u => Units.map (u.embedding : E →* ℂ) t⁻¹)
  rw [← hemb] at hr
  simp only [xi, MonoidHom.coe_mk, OneHom.coe_mk, Representation.dual_apply]
  rw [MonoidHom.comp_apply, hr]
  ext x
  simp [Module.Dual.transpose_apply, smul_smul]
