import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section Expr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def shortExpr (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) : S :=
  algebraMap c.F S (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
      ((N : c.F) ^ P.totalDegree)⁻¹) *
    ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) *
      ∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)

def ShortData {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) : Prop :=
  (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧
    (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧
    ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)

end Expr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def ShortValDescSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
      (φ : S →ₐ[c.F] K) (y : FrPt Xo c K), FrMap φ y0 y →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M →
        ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
        ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v

def ShortValFinExtSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j)
    (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M →
    Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j w.n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j w.n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j w.n) yI₂.1 yI'.1 ∧
        ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin w.n →
              (ptO (T.dδ j w.n).Xo₂ yI₂.1.x ⟶ (T.dδ j w.n).Xo₂.univ.t.G))
          (tp : (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) → Fin w.n →
              (ptO (T.dδ j w.n).Xo₂ yI₂.1.x ⟶ (T.dδ j w.n).Xo₂.univ.t.G))
          (F : (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin w.n →
              LB.Sec (LPow (T.dδ j w.n).Xo₂.univ.t.G (T.dδ j w.n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                (ptO (T.dδ j w.n).Xo₂ yI₂.1.x))),
          ShortData Λ N yI₂.1 z tp F ∧
          iT (evI yI g) = evI yI₂ (T.dδ j w.n).cδ *
            shortExpr (T.dδ j w.n).nab₂ ((T.dδ j w.n).w x0) Λ ((T.dδ j w.n).eF (betaH (Dw := T.Q.Dw j) T.Q.c Λ)) N
              (MvPolynomial.map ((T.dδ j w.n).eF : T.Q.c.F →+* (T.dδ j w.n).c₂.F) P) yI₂.1 F

def FinExtRootShortSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (Λ : GenLat D.host.E n) (N : ℕ),
    Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → Λ.LevOK N (T.dδ j n).l₂.M →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j n).Xo₂ (T.dδ j n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j n) yI₂.1 yI'.1 ∧
          ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
                (ptO (T.dδ j n).Xo₂ yI₂.1.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
            (tp : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin n →
                (ptO (T.dδ j n).Xo₂ yI₂.1.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
            (F : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
                LB.Sec (LPow (T.dδ j n).Xo₂.univ.t.G (T.dδ j n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                  (ptO (T.dδ j n).Xo₂ yI₂.1.x))),
            ShortData Λ N yI₂.1 z tp F

def FrOverBCSt {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [Algebra c.F k] [Algebra d.c₂.F k] [Algebra c.F k'] [Algebra d.c₂.F k']
    (κ₁ : k →ₐ[c.F] k') (κ₂ : k →ₐ[d.c₂.F] k'), (κ₁ : k →+* k') = κ₂ →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k) (y₂' : FrPt d.Xo₂ d.c₂ k') (y' : FrPt Xo c k'),
      FrOver d y₂ y → FrMap κ₁ y y' → FrMap κ₂ y₂ y₂' → FrOver d y₂' y'

def HarmLMapSt {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  ∀ (Λ : GenLat E n) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ a

def ShortExprIndepSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
      (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M →
      ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
      ∀ (z z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
        (tp tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
        (F F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
          LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
        ShortData Λ N y z tp F → ShortData Λ N y z' tp' F' →
          shortExpr nab w Λ β N P y F = shortExpr nab w Λ β N P y F'

end ReciprocityTheory.ChartRestriction.G.PullbackSections
