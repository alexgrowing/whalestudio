import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibrStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
  GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefGeneric

theorem ratDeg_nonneg : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q),
    IsArithVar q 1 → ArInt.NefFib L → 0 ≤ ratDeg q L.B := by
  intro k _ W q L hW hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective k W q 1 hW 2 L.B L.isLB
  obtain ⟨hproj, hdim⟩ := GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one k W q hW 2
  letI := GlobalTheory.algebraΓOfHom
    (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod 2))))
  have h := GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod 2 _ hproj hdim _ (LB.isLB_pull L.isLB _)
    (fun Z i _ _ _ hZ => GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres k W q L 2 hL Z i hZ)
  rw [ratDeg, degOfRank, ← e1, ← e2]
  simpa [degOfRank] using h

theorem isNef_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (L : HermLB P.p),
    ArInt.NefFib L → IsNef F (L.B.pull P.j) := by
  intro F _ _ Y P L hL
  refine ⟨LB.isLB_pull L.isLB P.j, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hz, hpb⟩ := GlobalTheory.T.complete_curve_arith_model_closure F Y P Z hZ
  have e := GlobalTheory.T.curve_model_rational_degree F Y P Z hZ W w z hW hz hpb L.B L.isLB
  have h0 := ratDeg_nonneg (𝓞 F) W (w ≫ P.p) (L.pull w rfl) hW
    (ArInt.nefFib_pull (𝓞 F) P.X W P.p (w ≫ P.p) P.ar.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ P.p) (L.B.pull w) at h0
  rw [e] at h0
  have hpos : (0 : ℤ) < (Module.finrank ℚ F : ℤ) := by exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h0

end GlobalTheory.NefGeneric

theorem GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F)
    (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib → Y.nef M.D := by
  intro _ _ F _ _ C Y M _ ⟨P, L, k, cf, ⟨_, r, hr, _⟩, hL⟩
  have h := GlobalTheory.NefGeneric.isNef_model F Y P L hL
  exact (Var.nef_nsmul_iff k.pos).1 ((Var.nef_iff_of_toPic_eq _ hr.toPic_eq).2 h)

end
