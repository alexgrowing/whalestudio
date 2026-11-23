import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousLinPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionFlagDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open scoped Classical

namespace GlobalTheory.SwapTrue

theorem rootSym_support {D : D7} (O : Setup D) (Pc : Finset ℕ) (R : ℝ) (x : DV.Rt D.what₂.Tau O.N) :
    ∀ a ∈ (rootSym O.S.Dw (ArIn.ind Pc) (some R) (DV.tauEmb D x.1) x.2).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
  intro a ha
  unfold rootSym at ha
  split_ifs at ha <;>
  · rw [Finsupp.support_single_ne_zero _ (by norm_num)] at ha
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨Pc.finite_toSet.subset fun q hq => by simpa [ArIn.ind] using hq, rfl⟩

theorem swapEq_true : Hypotheses2 → HypothesesH → RegularAlteration → BunSt → ∀ G, Homog G → SwapFl G →
    OnObj fun _ O _ _ _ _ => ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R →
      SwapEq O.Y G (O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R) O.Y.chern := by
  intro hP hH _ hBS G _ hSF D O hC hf A T H h B hB R hR
  show ∀ (τ : D.what₂.Tau) (a b : Fin O.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ O.j → ∀ n : D.what₂.Tau × Fin O.N → ℤ,
    (arIn O.s O.Φ O.met.hm).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (lin (fun z => (n z : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1)) +
      (arIn O.s O.Φ O.met.hm).arDeg (GlobalTheory.FlagAr.setB O.Y B) R
        (lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1)) =
      (O.Y.vol • Formalism.L2.Geo.degFlL D.what₂.Tau O.N) (swapPol G (dimFl D.what₂.Tau O.N) (τ, a) (τ, b) n)
  intro τ a b hab hbj n
  obtain ⟨xa, Pc, hcw⟩ := id hC
  have hm : O.met.hm = metsOf xa O.Φ := hcw.hm_eq
  have hdim : ∀ c, (O.var c).dim = dimFl D.what₂.Tau O.N := O.dim_eq
  obtain ⟨A', i, i', hii, hei, hei'⟩ := exists_adj O.indef.2.le τ a b hab hbj
  have key : ∀ c : O.s.Comp, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) R y c)
          (lin (fun z => (n z : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1))) +
      numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) R y c)
          (lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1))) =
      A.w c * degFl D.what₂.Tau O.N (swapPol G (dimFl D.what₂.Tau O.N) (τ, a) (τ, b) n) := by
    intro c
    obtain ⟨W⟩ := hBS D O hC B hB R hR c
    haveI := W.int
    obtain ⟨⟨Φc, hΦc⟩, Ψc, hΨc⟩ := (hP.p4.arExists (𝓞 D.what₂.LL) W.V.X W.V.p (O.var c).dim W.V.ar).2 _
      (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
        VMetric.grLB (W.fl z.1) z.2 ((W.H z.1).pull W.π W.w))
    have hS := hSF (𝓞 D.what₂.LL) W.B W.V.X W.q W.V.p _ _ W.ar W.V.ar W.π W.w (D.what₂.Tau × Bool) W.E _ W.h W.H W.fl
      W.univ Φc Ψc hΦc hΨc A' i i' hii (fun z => n ((blockEquiv D.what₂.Tau O.N O.j O.indef.2.le) z))
    have hG := GlobalTheory.T.geometric_function_flag_degree hP hH D O hC hf A T H h B hB R hR c W Ψc hΨc
    obtain ⟨-, hT⟩ := GlobalTheory.ArTopTrue.arTop_true hP.p4 hH.deg GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s
      xa O.Φ c R hR
    obtain ⟨M, L, m, Ψ, hL, hΨ, hnum⟩ := hT (DV.Rt D.what₂.Tau O.N)
      (fun y => rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (DV.tauEmb D y.1) y.2)
      (fun y => rootSym_support O _ R y)
    have hcmp := GlobalTheory.T.adelic_line_bundle_induced_arith hP.p4 hH.deg (O.var c) (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le)
      (fun y => adlOf (O.Φ.C c) (metsOf xa O.Φ c)
        (rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (DV.tauEmb D y.1) y.2))
      (fun _ => rfl) M L m Ψ hL hΨ W.V _ Φc (fun z => by have := W.ind z.1 z.2; rw [hm] at this; exact this) hΦc
    have hnum' : ∀ n' : DV.Rt D.what₂.Tau O.N → ℤ, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) R y c)
          (lin (fun z => (n' z : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1))) =
        Φc (lin (fun z => (n' ((blockEquiv D.what₂.Tau O.N O.j O.indef.2.le) z) : ℝ)) ^ (dimFl D.what₂.Tau O.N + 1)) / W.V.ν := by
      intro n'
      rw [hm]
      have h1 := GlobalTheory.NumLRename.numL_rename_of_agree _ ((O.var c).dim + 1) _ Ψ _ hnum
        (lin (fun z => (n' z : ℝ)) ^ ((O.var c).dim + 1)) (isHomogeneous_lin_pow _ _)
      have h2 := hcmp n'
      rw [hdim c] at h1 h2
      exact h1.trans h2
    rw [hG, rename_swapPol, hei, hei'] at hS
    simp only [hdim c] at hS
    rw [hnum' n, hnum' (fun z => n (swapAt τ a b z)), ← add_div, div_eq_iff W.V.ν_pos.ne', mul_comm _ W.V.ν,
      ← mul_assoc]
    convert hS using 4
    congr 1
    funext z
    congr 2
    exact swapAt_comp_equiv _ _ _ τ a b hei hei' z
  have hvol := (GlobalTheory.T.weights_sum_to_volume_proportional hP hH D O hC hf A T H h).2.1
  rw [LinearMap.smul_apply, Formalism.L2.Geo.degFlL_apply, smul_eq_mul, hvol, Finset.sum_mul]
  simp only [ArIn.arDeg, LinearMap.sum_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => key c

end GlobalTheory.SwapTrue
