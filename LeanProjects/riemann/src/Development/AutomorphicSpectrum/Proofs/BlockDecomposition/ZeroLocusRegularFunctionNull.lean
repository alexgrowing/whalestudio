import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℤ) (σ : ℤ →+* ℂ) (D : ℕ) (c : GlobalTheory.AlgChart q σ D) (W : X.Opens)
    (h : genericPoint X ∈ W) (g : Γ(X, W)), fnOf W h g ≠ 0 →
    volume (c.e.target ∩ c.e.symm ⁻¹' {y | y ∈ ptsIn q σ W ∧ ev q σ W g y = 0}) = 0 := by
  intro X _ q σ D c W h g hg
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · have ht : c.e.target = ∅ := by rw [← c.e.image_source_eq_target, hs, Set.image_empty]
    simp [ht]
  have sectionFrameQuotient := mem_ptsIn.1 (c.source_subset hy0)
  haveI : Nonempty c.U := ⟨⟨_, sectionFrameQuotient⟩⟩
  have hgU : genericPoint X ∈ c.U := gen_mem sectionFrameQuotient
  haveI := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (fnOf W h g)
  have hal : ∀ t : Γ(X, c.U), algebraMap Γ(X, c.U) X.functionField t = fnOf c.U hgU t :=
    fun _ => rfl
  rw [hal, hal] at hab
  have hb0 : fnOf c.U hgU b ≠ 0 := fun e =>
    nonZeroDivisors.ne_zero hb ((map_eq_zero_iff _ (fnOf_injective _ _)).1 e)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg
    rw [← hab, map_zero, zero_div]
  have hrel : fnOf W h g * fnOf c.U hgU b = fnOf c.U hgU a := by
    rw [← hab, div_mul_cancel₀ _ hb0]
  have hI : genericPoint X ∈ W ⊓ c.U := ⟨h, hgU⟩
  have hres : resG X (inf_le_left : W ⊓ c.U ≤ W) g * resG X (inf_le_right : W ⊓ c.U ≤ c.U) b =
      resG X (inf_le_right : W ⊓ c.U ≤ c.U) a := by
    apply fnOf_injective _ hI
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG]
    exact hrel
  obtain ⟨Q, hQ, r, hQr⟩ := GlobalTheory.ChernNull.exists_poly_dvd _ c.etale a ha0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (RingHom.injective_int σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (GlobalTheory.ChernNull.volume_poly_zero D _ hP)
  rintro v ⟨hv, hyW, hyz⟩
  have hys : c.e.symm v ∈ c.e.source := c.e.map_target hv
  have hyU := c.source_subset hys
  have hyI : c.e.symm v ∈ ptsIn q σ (W ⊓ c.U) := mem_ptsIn_inf.2 ⟨hyW, hyU⟩
  have hay : ev q σ c.U a (c.e.symm v) = 0 := by
    rw [← ev_res inf_le_right hyI, ← hres, ev_mul, ev_res inf_le_left hyI, hyz, zero_mul]
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun i => c.e (c.e.symm v) i) := by
    refine MvPolynomial.ringHom_ext (fun i => ?_) (fun i => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq _ hys]
  have hQy := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at hQy
  show MvPolynomial.eval (fun i => v i) (MvPolynomial.map σ Q) = 0
  rw [c.e.right_inv hv] at hQy
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← hQy, hQr, map_mul, ← ev_eq hyU, hay,
    zero_mul]
