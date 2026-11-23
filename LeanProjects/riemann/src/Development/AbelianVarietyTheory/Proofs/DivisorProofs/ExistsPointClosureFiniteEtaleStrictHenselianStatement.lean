import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian : ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D → GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (exact GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale  <;> assumption)
