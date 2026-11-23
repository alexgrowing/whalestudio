import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerRegularImpliesGeneration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_regular_implies_generation : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), (∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1)) (y : (Φ.C k).Y.X), y ∈ ((Φ.C k).π ⁻¹ᵁ V) → (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).RegularAt y (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q)) → ∀ (ht : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ⨆ q, nonzeroLocus (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x q) = ⊤) (K : Type) [Field K] (a : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme) (c : Γ(gen s.T.Z, V) →+* K), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c → ∀ (y : (Φ.C k).Y.X) (ψ : (Φ.C k).Y.X.presheaf.stalk y →+* K) (P : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι = spMap ψ ≫ stalkPt (Φ.C k).Y y → (∀ τ, IsUnit (P τ).det) → B = T * P.map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) → (∀ τ i l, i < l → T τ i l = 0) → (∀ τ i, ∃ u : (Φ.C k).Y.Fnˣ, T τ i i = u ∧ ((Φ.C k).gr τ i).IsEqn y u) → ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ∃ hv, a ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x) = GlobalTheory.ProjSpace.pt c (GlobalTheory.FlagAmple.PlkLoc.plkFn (P.map ψ) x) hv := by
  first | exact @GlobalTheory.FlagAmple.PlkVal.value | exact GlobalTheory.FlagAmple.PlkVal.value | (intros; apply GlobalTheory.FlagAmple.PlkVal.value <;> assumption)
