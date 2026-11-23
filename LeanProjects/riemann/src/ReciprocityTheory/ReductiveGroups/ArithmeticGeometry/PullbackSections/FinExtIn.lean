import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortValDesc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def CDVRExtSt : Prop :=
  ∀ (T : CDVR), T.FinRes → ∀ (K : Type) [Field K] (jK : T.Fr →+* K),
    (letI := jK.toAlgebra; FiniteDimensional T.Fr K) →
    ∃ (T' : CDVR) (κ : K →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (κ (jK a)) = (e' : ℤ) * vV T.V a) ∧ T'.FinRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IntFrBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (yI : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e' : ℕ), 0 < e' →
    (∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a) →
    ∃ yI' : IntFr Xo c T' (iT.comp io),
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1

def CoverPtSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j n).Xo₂ (T.dδ j n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j n) yI₂.1 yI'.1

def ShortSplitSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (Λ : GenLat D.host.E n) (N : ℕ),
    Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → Λ.LevOK N (T.dδ j n).l₂.M →
    ∀ (K : Type) [Field K] [Algebra (T.dδ j n).c₂.F K] (y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ K),
    ∃ (K' : Type) (_ : Field K') (jK : K →+* K'), (letI := jK.toAlgebra; FiniteDimensional K K') ∧
      ∀ (L : Type) [Field L] [Algebra (T.dδ j n).c₂.F L] (ψ : K →ₐ[(T.dδ j n).c₂.F] L),
        (∃ ψ' : K' →+* L, ψ'.comp jK = ψ.toRingHom) →
        ∀ yL : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ L, FrMap ψ y yL →
        ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
              (ptO (T.dδ j n).Xo₂ yL.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
          (tp : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin n →
              (ptO (T.dδ j n).Xo₂ yL.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
          (F : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
              LB.Sec (LPow (T.dδ j n).Xo₂.univ.t.G (T.dδ j n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                (ptO (T.dδ j n).Xo₂ yL.x))),
          ShortData Λ N yL z tp F

def VtSplitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (n : ℕ) (x : Fin n → (T.Q.Dw j).La)
    (K : Type) [Field K] [Algebra T.Q.c.F K] (y : FrPt (T.Q.Xo j) T.Q.c K),
    ∃ (K' : Type) (_ : Field K') (jK : K →+* K'), (letI := jK.toAlgebra; FiniteDimensional K K') ∧
      ∀ (L : Type) [Field L] [Algebra T.Q.c.F L] (ψ : K →ₐ[T.Q.c.F] L), (∃ ψ' : K' →+* L, ψ'.comp jK = ψ.toRingHom) →
        ∀ yL : FrPt (T.Q.Xo j) T.Q.c L, FrMap ψ y yL →
        ∃ F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yL.x)),
          ∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yL.s (levPt (T.Q.Xo j) yL.x (x b)) (F b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
