import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

def GenAt (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ} (jc : Fin (N + 1))
    (x : Fin N → Ω) (V : ValuationSubring (OmS Ω D N)) : Prop :=
  ∃ ht : ∀ p, sImg jc x p ∈ V,
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω (OmS Ω D N))
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω (OmS Ω D N))) (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
      ((algebraMap _ (IsLocalRing.ResidueField V)).comp
        (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω (OmS Ω D N)))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω)))
      (fun p => IsLocalRing.residue V ⟨sImg jc x p, ht p⟩)

def PtSepSt : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (jc : Fin (N + 1)) (x : Fin N → Ω),
    Algebra.trdeg K Ω = D →
    ∀ V V' : ValuationSubring (OmS Ω D N), GenAt K jc x V → GenAt K jc x V' →
      V.comap (algebraMap Ω (OmS Ω D N)) = V'.comap (algebraMap Ω (OmS Ω D N)) → V = V'

def LocStructSt : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (jc : Fin (N + 1)) (x : Fin N → Ω),
    Algebra.trdeg K Ω = D →
    ∀ (Z : Type) [Fintype Z] (v : Z → Valuation (OmS Ω D N) (WithZero (Multiplicative ℤ))),
      (∀ ζ, GenAt K jc x (v ζ).valuationSubring) →
      (∀ ζ, ∃ a : OmS Ω D N,
        v ζ a = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      ∀ g : OmS Ω D N, (∀ ζ, v ζ g ≤ 1) →
      ∃ f d : MvPolynomial (TVar D N) Ω,
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (f.coeff e)) ≤ 1) ∧
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (d.coeff e)) ≤ 1) ∧
        (∀ ζ, v ζ (aeval (sImg jc x) d) = 1) ∧
        aeval (sImg jc x) f = aeval (sImg jc x) d * g

end Formalism.L2.Pj.LocAlg
