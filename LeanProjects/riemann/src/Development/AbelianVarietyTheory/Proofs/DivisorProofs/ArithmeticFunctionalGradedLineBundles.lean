import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousLinPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
import Development.AutomorphicArithmetic.LocalEmbeddings.RootSymSupport
import Development.AutomorphicArithmetic.LocalEmbeddings.NonemptyBunModel
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
open GlobalTheory.BcEigen

noncomputable section

namespace GlobalTheory.BcRead

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.SwapTrue

private theorem rootIdx_eq (ι : Type) (N j : ℕ) (hj : j ≤ N) : rootIdx ι N j = ⇑(blockEquiv ι N j hj).symm := rfl

private theorem ext_pow {ι : Type} [Fintype ι] (d : ℕ) (f g : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, f (lin (fun i => (n i : ℝ)) ^ d) = g (lin (fun i => (n i : ℝ)) ^ d))
    (hf : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → f P = 0)
    (hg : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → g P = 0) : f = g :=
  sub_eq_zero.1 (GlobalTheory.ArInt.Model.eq_zero_of_pow d _ (fun n => by simp [h n, -map_pow])
    fun P e he hP => by simp [hf P e he hP, hg P e he hP])

private theorem numL_eq (hP : Hypotheses2) (hH : HypothesesH) {D : D7} (O : Setup D) (hC : O.Core) (Pc : Finset ℕ) {R : ℝ} (hR : 2 ≤ R)
    (c : O.s.Comp) (W : BunModel O Pc R c)
    (Φ : MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) ℝ →ₗ[ℝ] ℝ)
    (hΦ : IsArFun (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
      VMetric.grLB (W.fl z.1) z.2 ((W.H z.1).pull W.π W.w)) (O.var c).dim Φ) (P : MvPolynomial (DV.Rt D.what₂.Tau O.N) ℝ) :
    numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind Pc) R y c) P) =
      (W.V.ν)⁻¹ * Φ (rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm P) := by
  obtain ⟨xa, _, hcw⟩ := id hC
  have hm : O.met.hm = metsOf xa O.Φ := hcw.hm_eq
  have hdim : (O.var c).dim = dimFl D.what₂.Tau O.N := O.dim_eq c
  obtain ⟨-, hT⟩ := GlobalTheory.ArTopTrue.arTop_true hP.p4 hH.deg GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s
    xa O.Φ c R hR
  obtain ⟨M, L, m, Ψ, hL, hΨ, hnum⟩ := hT (DV.Rt D.what₂.Tau O.N)
    (fun y => rootSym O.S.Dw (ArIn.ind Pc) (some R) (DV.tauEmb D y.1) y.2) (fun y => rootSym_support O _ R y)
  have hcmp := GlobalTheory.CoverModelTop.top_eq hP.p4 hH.deg (O.var c) (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le)
    (fun y => adlOf (O.Φ.C c) (metsOf xa O.Φ c) (rootSym O.S.Dw (ArIn.ind Pc) (some R) (DV.tauEmb D y.1) y.2))
    (fun _ => rfl) M L m Ψ hL hΨ W.V _ Φ (fun z => by have := W.ind z.1 z.2; rw [hm] at this; exact this) hΦ
  have key := ext_pow (dimFl D.what₂.Tau O.N + 1)
    (numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1) ∘ₗ
      (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind Pc) R y c)).toLinearMap)
    ((W.V.ν)⁻¹ • Φ ∘ₗ (rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm).toLinearMap)
    (fun n => ?_) (fun Q e he hQ => numL_homog _ _ _ he _ hQ.rename_isHomogeneous)
    (fun Q e he hQ => by
      have h0 := hΦ.2 _ e (hdim ▸ he) (hQ.rename_isHomogeneous
        (f := (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm))
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h0, smul_zero])
  · exact LinearMap.congr_fun key P
  · have h1 := GlobalTheory.NumLRename.numL_rename_of_agree _ ((O.var c).dim + 1) _ Ψ _ hnum
      (lin (fun z => (n z : ℝ)) ^ ((O.var c).dim + 1)) (isHomogeneous_lin_pow _ _)
    have h2 := hcmp n
    rw [hdim] at h1 h2
    have h3 : rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm (lin fun z => (n z : ℝ)) =
        lin fun z => (n (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le z) : ℝ) := by
      rw [← rename_lin_comp (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm]
      simp only [Equiv.apply_symm_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    rw [map_pow (rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le).symm), h3, hm, inv_mul_eq_div]
    exact h1.trans h2

end GlobalTheory.BcRead

end

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.SwapTrue GlobalTheory.BcRead in
theorem _root_.GlobalTheory.T.arithmetic_functional_graded_line_bundles : Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R →
    ∃ (M : ∀ c : O.s.Comp, BunModel O ∅ R c)
      (Φ Ψ : O.s.Comp → MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) ℝ →ₗ[ℝ] ℝ)
      (κ : O.s.Comp → ℝ),
      (∀ c, IsArFun (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
        VMetric.grLB ((M c).fl z.1) z.2 (((M c).H z.1).pull (M c).π (M c).w)) (O.var c).dim (Φ c)) ∧
      (∀ c, IsGeoFun (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
        VMetric.grLB ((M c).fl z.1) z.2 (((M c).H z.1).pull (M c).π (M c).w)) (O.var c).dim (Ψ c)) ∧
      ∀ P : MvPolynomial (DV.Rt D.what₂.Tau O.Y.N) ℝ,
        O.Y.arDeg ∅ R P = ∑ c, κ c * Φ c (rename (rootIdx D.what₂.Tau O.Y.N O.Y.j) P) ∧
        O.Y.chern P = ∑ c, κ c * Ψ c (rename (rootIdx D.what₂.Tau O.Y.N O.Y.j) P) := by
  intro hP hH _ D O hC hf A T H h R hR
  have M : ∀ c : O.s.Comp, BunModel O ∅ R c := fun c => (GlobalTheory.BcLie.nonempty_bunModel O hC hR c).some
  have ex := fun c => (hP.p4.arExists (𝓞 D.what₂.LL) (M c).V.X (M c).V.p (O.var c).dim (M c).V.ar).2 _
    (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
      VMetric.grLB ((M c).fl z.1) z.2 (((M c).H z.1).pull (M c).π (M c).w))
  choose Φ hΦ using fun c => (ex c).1
  choose Ψ hΨ using fun c => (ex c).2
  refine ⟨M, Φ, Ψ, fun c => ((M c).V.ν)⁻¹, hΦ, hΨ, fun (P : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ) => ⟨?_, ?_⟩⟩
  · show (arIn O.s O.Φ O.met.hm).arDeg ∅ R P = ∑ c, ((M c).V.ν)⁻¹ * Φ c (rename (rootIdx D.what₂.Tau O.N O.j) P)
    rw [rootIdx_eq _ _ _ O.indef.2.le]
    exact (LinearMap.sum_apply _ _ _).trans
      (Finset.sum_congr rfl fun c _ => numL_eq hP hH O hC ∅ hR c (M c) (Φ c) (hΦ c) P)
  · show (∑ c, (O.s.cx O.L O.B O.fl).volC c) * Formalism.L2.Geo.degFlL D.what₂.Tau O.N P =
      ∑ c, ((M c).V.ν)⁻¹ * Ψ c (rename (rootIdx D.what₂.Tau O.N O.j) P)
    rw [rootIdx_eq _ _ _ O.indef.2.le, Formalism.L2.Geo.degFlL_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [geo_eq hP hH O hC ∅ hR c (M c) (Ψ c) (hΨ c), rename_rename, Equiv.self_comp_symm, rename_id_apply,
      mul_assoc, inv_mul_cancel_left₀ (M c).V.ν_pos.ne']
