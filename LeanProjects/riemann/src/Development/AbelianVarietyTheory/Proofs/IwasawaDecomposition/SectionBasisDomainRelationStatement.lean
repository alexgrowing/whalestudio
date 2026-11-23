import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionBasisDomainRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_basis_domain_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R)))))
    (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (c : Fin n → W) (a : W)
    (s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap φ))))
    (s' : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ((algebraMap W (FractionRing W)).comp φ))))),
    Lin t.G t.PP.L N (jC φ (algebraMap W (FractionRing W))) (fun _ : Fin 1 => s) (fun _ => 1) s' →
    LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b
      (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i))) (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) s' →
    LinA t.G t.PP.L N (toBase φ) b (fun i => GlobalTheory.OneBasis.fnR (c i)) (GlobalTheory.OneBasis.fnR a) s := by
  first | exact @GlobalTheory.TorRef.linA_of_fractionRing | exact GlobalTheory.TorRef.linA_of_fractionRing | (intros; apply GlobalTheory.TorRef.linA_of_fractionRing <;> assumption)
