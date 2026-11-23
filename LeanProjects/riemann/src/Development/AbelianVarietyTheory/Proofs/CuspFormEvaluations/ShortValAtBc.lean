import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionPolynomialExpressionCoeffFieldExtensioStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem shortExpr_bc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F)
    (β : c.F) (a b N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) {J : Type} [Fintype J] (k : ℤ)
    (F : (Fin n → LevQ Dw l) → J → Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    algebraMap c'.F S ((incF c c' hle β)⁻¹ * ((a : c'.F))⁻¹ * ((b : c'.F))⁻¹ *
        ((N : c'.F) ^ (MvPolynomial.map (incF c c' hle) P).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c'.F S (incF c c' hle (w q)) *
        ∑ i, ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support,
          algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) *
          ∏ j, nabBC hle nab y k (F q i j) (colOf m j) =
    algebraMap c.F S (β⁻¹ * ((a : c.F))⁻¹ * ((b : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ j, nab (y.res hle h) k (F q i j) (colOf m j) := by
  have h' : ∀ x : c.F, algebraMap c'.F S (incF c c' hle x) = algebraMap c.F S x := h
  have hd : (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree := by
    simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P (incF c c' hle).injective]
  congr 1
  · rw [hd, ← h']
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  · refine finsum_congr fun q => ?_
    rw [h']
    congr 1
    exact Finset.sum_congr rfl fun i _ => (GlobalTheory.T.connectionPolynomialExpression_coeffFieldExtension E H Dw l Xo c c' hle nab n P S h y k (F q i)).2

theorem shortValAt_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (v : S), ShortValAt Xo c' (nabBC hle nab) (fun q => incF c c' hle (w q)) Λ (incF c c' hle β) N (MvPolynomial.map (incF c c' hle) P) y v ↔ ShortValAt Xo c nab w Λ β N P (y.res hle h) v := by
  intro E _ _ _ H Dw l Xo c c' hle nab n w Λ β N P S _ _ _ h y v
  constructor
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c.F S' := resAlg hle S'
    have h' : AlgOver c c' hle S' := fun _ => rfl
    let φ₀ : S →ₐ[c.F] S' := { φ.toRingHom with commutes' := fun x => (congrArg φ (h x).symm).trans (φ.commutes _) }
    exact ⟨S', i1, i3, φ₀, y'.res hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' y' _ F)⟩
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, hff, hfr, hz, hg, htp, hF, hv⟩
    letI i3 : Algebra c'.F S' := (φ.toRingHom.comp (algebraMap c'.F S)).toAlgebra
    have h' : AlgOver c c' hle S' := fun x => (congrArg φ (h x)).trans (φ.commutes x)
    let φ₀ : S →ₐ[c'.F] S' := { φ.toRingHom with commutes' := fun _ => rfl }
    exact ⟨S', i1, i3, φ₀, y'.ext hle h', z, tp, F, hff, hfr, hz, hg, htp, hF,
      hv.trans (shortExpr_bc hle nab w β _ _ N P h' (y'.ext hle h') _ F).symm⟩

end GlobalTheory.FieldBC
