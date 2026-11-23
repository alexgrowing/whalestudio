import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CompFinSigR

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem locFE (hF : LocRedField) (hS : LocRedSplit) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (M M' : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E)) (hM : ∀ i j, M i j ∈ intLoc F E v) (hM' : ∀ i j, M' i j ∈ intLoc F E v)
    (hMM : M * M' = 1) (hU : Formalism.UG.cT (sigR (Fv F v) σ) M * J2 (Fv F v ⊗[F] E) n * M = J2 (Fv F v ⊗[F] E) n) :
    ∃ (a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (I : Finset (Fin n)), (∀ i j, a i j ∈ intLoc F E v) ∧
      (a.det ∈ intLoc F E v ∧ ∃ z' ∈ intLoc F E v, a.det * z' = 1) ∧
      ((blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map (sigR (Fv F v) σ)).transpose)⁻¹ * wIm I)).det ∈ intLoc F E v ∧
        ∃ z' ∈ intLoc F E v, (blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map (sigR (Fv F v) σ)).transpose)⁻¹ * wIm I)).det * z' = 1) := by
  obtain ⟨𝔪, h𝔪, horb⟩ := orbit σ hσ hfix v
  exact locSub hF hS (intLoc F E v) (sigR (Fv F v) σ) (sigI σ v) (sigI_sigI σ hσ v) (fun x => sigI_coe _ v x) 𝔪 h𝔪 horb M M' hM hM'
    hMM hU

theorem hmul {D : D7} {n : ℕ} (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    (mat k).map (GlobalTheory.FinPl.compAt D v) * (mat k⁻¹).map (GlobalTheory.FinPl.compAt D v) = 1 := by
  rw [← Matrix.map_mul]
  show (mat (k * k⁻¹)).map _ = 1
  rw [mul_inv_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem locFin_of (hF : LocRedField) (hS : LocRedSplit) : LocFin := by
  intro D n k hk v
  have h := locFE hF hS D.sp.cm.sig sig_sig sig_fix v _ _ (int_of_K k hk v) (int_of_K k⁻¹ (inv_mem hk) v) (hmul k v) (uni_comp k v)
  simp only [LocGood, IsIntUnit, cTv]
  with_reducible_and_instances exact h

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf
