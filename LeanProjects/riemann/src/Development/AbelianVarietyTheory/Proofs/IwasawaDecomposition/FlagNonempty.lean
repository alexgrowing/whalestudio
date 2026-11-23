import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicPackageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnifStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnifStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.KitEx

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

theorem flag_nonempty (s : FinalTheorems S κ) : Nonempty s.Flag :=
  GlobalTheory.T.smooth_of_alg_closed_unif _ _ _ _ _ _ _ _ s.T.Z _ κ.e _ _ (s.U κ.σ₀) κ.good_σ₀ s.isUnf
    (fun _ => GlobalTheory.OrbitScalar.exists_mem_dom _) s.geo s.T.smooth s.T.snc

theorem key_nonempty (s : FinalTheorems S κ) : Nonempty (KeySec s.Xo κ.c) :=
  GlobalTheory.T.exists_key_section_unif _ _ _ _ _ _ _ _ (s.U κ.σ₀) κ.good_σ₀ s.isUnf
    (fun _ => GlobalTheory.OrbitScalar.exists_mem_dom _) (s.unf _ κ.good_σ₀).2.2.1 s.geo S.two_le (CmDim.cm_dim D A).2.1

def kitOf (s : FinalTheorems S κ) (L : CmList A) (C : CxSt D.what₂.LL)
    {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    (Φ : s.Flag) (key : KeySec s.Xo κ.c) (pad : PadPkg D N j s.Comp jC ng) : Kit s L C jC ng where
  Φ := Φ
  dim_eq := (CmDim.cm_dim D A).2.2 N j S κ s Φ
  key := key
  B := GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _
  fl := 1
  Mb := fun _ _ _ _ => ⟨0, 1, fun σ => C.fsMet _ σ 0 (k := Empty) Empty.elim, 0, 0⟩
  pad := { pad with levIn := κ.inK }
  levIn := fun _ => Iff.rfl

theorem kit_of_parts (s : FinalTheorems S κ) (L : CmList A) (C : CxSt D.what₂.LL)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg)
    (Φ : s.Flag) (key : KeySec s.Xo κ.c) (pad : PadPkg D N j s.Comp jC ng) : Nonempty (Kit s L C jC ng) :=
  ⟨kitOf s L C Φ key pad⟩

theorem kits_nonempty : ∀ D : D7, ∃ ng : NgPkg, ∀ (A : Amb D) (F : SrcFam A) (L : CmList A) (C : CxSt D.what₂.LL)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)), Nonempty (Kits F L C jC ng) := by
  intro D
  obtain ⟨ng, hng⟩ := GlobalTheory.T.exists_padic_package D
  refine ⟨ng, fun A F L C jC => ⟨fun N j hN hj κ => ?_⟩⟩
  exact kitOf _ L C (flag_nonempty _).some (key_nonempty _).some (hng N j _ jC hj).some

end GlobalTheory.ShFam.KitEx
