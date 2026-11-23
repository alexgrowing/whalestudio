import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.DefsNN

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Def

def TensorFockProduct : Prop :=
  ∀ (T σ : Type) [Fintype T] [DecidableEq T] (p q : T → MvPolynomial σ ℂ),
    Formalism.REAL.fockF (∏ τ, rename (Prod.mk τ) (p τ)) (∏ τ, rename (Prod.mk τ) (q τ)) = ∏ τ, Formalism.REAL.fockF (p τ) (q τ)

def KroneckerProductDet : Prop :=
  ∀ (R T : Type) [CommRing R] [Fintype T] [DecidableEq T] (I : T → Type) [∀ τ, Fintype (I τ)]
    [∀ τ, DecidableEq (I τ)] (A : ∀ τ, Matrix (I τ) (I τ) R),
    (Matrix.of fun i j : (∀ τ, I τ) => ∏ τ, A τ (i τ) (j τ)).det =
      ∏ τ, (A τ).det ^ (∏ τ' ∈ Finset.univ.erase τ, Fintype.card (I τ'))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalFibreLattice (D : D7) : Prop :=
  ∀ (ell : D.what₂.Tau → HLat D.what₂.LL), (∀ τ, (ell τ).Good ∧ (ell τ).rank = 1) →
    ∀ (κ : D.what₂.Tau → DomWeight (nW D)) (c : XDef D) (w : HeightOneSpectrum (𝓞 D.what₂.LL))
      (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL),
      (∀ τ, Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (TxLat D ell c τ) =
        Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (colSpan D (B τ))) →
      ∀ F : MvPolynomial (VarT D) D.what₂.LL,
        F ∈ Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (FibLat D ell κ c) ↔
          twAct D B (fun τ => (κ τ).detShift) F ∈ Formalism.HermitianLatticesTheory.loc (K := D.what₂.LL) w.asIdeal (intLat D κ)

end Formalism.L2.Geo.Def
