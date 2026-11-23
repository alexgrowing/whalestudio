import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisLocalRingReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_local_ring_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R)))))
    (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) (c : Fin n → W) (a : W)
    (s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap φ)))), a ∈ maximalIdeal W →
    LinA t.G t.PP.L N (toBase φ) b (fun i => GlobalTheory.OneBasis.fnR (c i)) (GlobalTheory.OneBasis.fnR a) s →
    ∃ z : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ((residue W).comp φ)))),
      Lin t.G t.PP.L N (toBase ((residue W).comp φ)) b (fun i => GlobalTheory.OneBasis.fnR (residue W (c i))) z ∧
      Lin t.G t.PP.L N (toBase ((residue W).comp φ)) b (fun _ => 0) z := by
  first | exact @GlobalTheory.TorRef.lin_residue_of_linA | exact GlobalTheory.TorRef.lin_residue_of_linA | (intros; apply GlobalTheory.TorRef.lin_residue_of_linA <;> assumption)
