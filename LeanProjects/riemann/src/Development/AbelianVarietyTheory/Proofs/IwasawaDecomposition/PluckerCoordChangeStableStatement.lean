import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordChangeStable
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
theorem _root_.GlobalTheory.T.plucker_coord_change_stable : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ ((Φ.C k).π ⁻¹ᵁ V)) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → ∀ (K : Type) [Field K] (a : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme) (c : Γ(gen s.T.Z, V) →+* K), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = spMap c → ∃ (y : (Φ.C k).Y.X) (ψ : (Φ.C k).Y.X.presheaf.stalk y →+* K) (P : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι = spMap ψ ≫ stalkPt (Φ.C k).Y y ∧ (∃ h : EigFrame s.T.Z (c.comp φ) ((spMap c ≫ hV.fromSpec) ≫ genι s.T.Z), (Φ.C k).Carries (a ≫ ((Φ.C k).π ⁻¹ᵁ V).ι) h ∧ g.Coord c h (P.map ψ)) ∧ (∀ τ, IsUnit (P τ).det) ∧ B = T * P.map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) ∧ (∀ τ i l, i < l → T τ i l = 0) ∧ ∀ τ i, ∃ u : (Φ.C k).Y.Fnˣ, T τ i i = u ∧ ((Φ.C k).gr τ i).IsEqn y u := by
  first | exact @GlobalTheory.FlagAmple.PlkLoc.exists_carried_frame_coord | exact GlobalTheory.FlagAmple.PlkLoc.exists_carried_frame_coord | (intros; apply GlobalTheory.FlagAmple.PlkLoc.exists_carried_frame_coord <;> assumption)
