import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace Formalism.MainNotions.N.GlobalTheory

open Formalism.WeaklyAdmissibleFiltrations

def CoefJumpGen : Prop :=
  ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    (f : LL →ₐ[Qp] LL') {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (τ : K →ₐ[Qp] LL) (a : ℤ),
    IsJumpV PD ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL ≃ₐ[LL] _).toAlgHom.toRingHom.toMonoidHom.comp M)
        τ a ↔
      IsJumpV PD ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL' ≃ₐ[LL'] _).toAlgHom.toRingHom.toMonoidHom.comp
        ((f.mapMatrix : Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
        (f.comp τ) a

end Formalism.MainNotions.N.GlobalTheory
