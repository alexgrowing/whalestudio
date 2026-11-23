import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

open scoped ComplexOrder in
theorem UpperTheory.hermitian_lie_combination_integral_model :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (F : GlobalTheory.LieHt.SemiFib K) (t : SAB H (Sp K)) (e : F.P₀.A ≅ t.G), IsMonHom e.hom → LBIso F.P₀.L (t.PP.L.pull e.hom.left) → ∀ (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (m : ℕ) (u : Fin m → Fin F.P₀.g → K) (w : Fin m → (epsR K ⟶ F.P₀.A)), LinearIndependent K u → (∀ i, IsLieComb (u i) F.v (w i)) → ∀ σ : K →+* ℂ, EigenvectorLieDegree.IsArchSq t.G t.PP.L (fun i => w i ≫ e.hom) σ (h.gram σ u).det.re := by
  intro E _ _ _ H K _ _ F t e he hL h hH m u w hu hw σ
  obtain ⟨Λ, Hm, Wc, ⟨Q, -, ψ, v', U, χ, hfib, -, hAH, hvec⟩, hform⟩ := hH σ
  have hφ : IsGrpPullback Q.A t.G (spMap σ) (ψ ≫ e.hom.left) :=
    (hfib.2.1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl
  have hM := pull_isLB t.PP.isLB (ψ ≫ e.hom.left)
  obtain ⟨ι, hι⟩ : LBIso Q.L (t.PP.L.pull (ψ ≫ e.hom.left)) :=
    LBIso.trans Q.isLB (pull_isLB F.P₀.isLB ψ) hM hfib.2.2.symm (GlobalTheory.CM.EllComp.lbIso_pull_comp hL.symm ψ).symm
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hfib.2.1 (hvec i).1 (F.basis.1 i)
  choose w' hw' _ using fun i => GlobalTheory.existsUnique_isVecOver hfib.2.1.1 (w i)
  have hc : ∀ i, IsLieComb (fun k => σ (u i k)) v' (w' i) := fun i =>
    (GlobalTheory.lieComb_baseChange _ _ σ F.P₀.A Q.A ψ hfib.2.1 _ F.v (w i) (u i) v' (w' i) (fun j => (hvec j).1) (hw i)).1 (hw' i)
  have hd : ∀ i, U.IsDiff (∑ k, σ (u i k) • Wc k) (w' i) := fun i =>
    GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ U Wc v' _ _ htan (fun k => (hvec k).2) (hc i)
  have hpos : (0 : ℂ) < (h.gram σ u).det := by
    exact (h.posDef σ m u hu).det_pos
  obtain ⟨h0, hN⟩ := Complex.pos_iff.1 hpos
  refine ⟨Q.A, inferInstance, ψ ≫ e.hom.left, _, GlobalTheory.TorsionTauCompare.transport Q.isLB hM hι U, Hm, χ, w',
    fun i => ∑ k, σ (u i k) • Wc k, hφ, GlobalTheory.TorsionTauCompare.isAH_transport _ _ hι U hAH,
    fun i => ⟨?_, hd i⟩, h0, ?_⟩
  · have := hw' i
    unfold GlobalTheory.IsVecOver at this ⊢
    rw [← Category.assoc, this, Over.comp_left, Category.assoc]
  · have e1 : (((h.gram σ u).det.re : ℝ) : ℂ) = (h.gram σ u).det :=
      Complex.ext rfl ((Complex.ofReal_im _).trans hN)
    rw [e1, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.transpose_apply]
    exact GlobalTheory.LieGram.form_eq_hermForm h σ Hm Wc hform u j i
