import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndNab

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ExpUniqTanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (x x' : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G),
    IsExpChart y x → IsExpChart y x' → x = x'

def KillAddValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n : ℕ)
    (g : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
    MvPowerSeries.constantCoeff q = 0 → (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) →
    (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
        Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, expVal (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)

def FrTruncOfGermsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y),
    (∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
      ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) → FrTruncC y C

def ChartIndepTruncSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y), FrTruncC y C → FrTruncC y C' → ∀ (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P

theorem chartIndepTrunc_of (hE : ExpChartOfSt) (hG : ExpGaugeOfSt) (hT : TieSt) (hU : ExpUniqTanSt)
    (hGU : GaugeUniqSt) (hK : KillAddValSt) : ChartIndepTruncSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C C' hC hC' k n F f f' hf hf' a P hP

  have key : ∀ (x x' : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), x' = x → IsExpChart y x →
      ∀ (e : ∀ m, ExpFr y x m) (e' : ∀ m, ExpFr y x' m), IsExpGauge y x e → IsExpGauge y x' e' →
      ∀ (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
      (∀ b, IsExpGerm y x e k (F b) (g b)) → (∀ b, IsExpGerm y x' e' k (F b) (g' b)) →
      (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) := by
    intro x x' hxx hx e e' he he' g g' hg hg'
    subst hxx
    obtain ⟨q, hq0, hq2, hqc, hqf⟩ := hGU E H Dw l Xo c S y _ hx e e' he he'
    have hgg : ∀ b, g' b = g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) :=
      fun b => hqf k (F b) (g b) (g' b) (hg b) (hg' b)
    simp only [hgg]
    exact (hK E H Dw l c S k n g q hq0 hq2 hqc a P hP).symm
  obtain ⟨φ, hφ, hx⟩ := hE E H Dw l Xo c S y C
  obtain ⟨φ', hφ', hx'⟩ := hE E H Dw l Xo c S y C'
  obtain ⟨e, he, heo⟩ := hG E H Dw l Xo c hstar S y C hC φ hφ hx
  obtain ⟨e', he', heo'⟩ := hG E H Dw l Xo c hstar S y C' hC' φ' hφ' hx'
  choose g hg hgv using fun b => hT E H Dw l Xo c hstar S y C φ hφ e heo k (F b) (f b) (hf b)
  choose g' hg' hgv' using fun b => hT E H Dw l Xo c hstar S y C' φ' hφ' e' heo' k (F b) (f' b) (hf' b)
  have h1 : chartVal C k f P =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
    simp only [chartVal, hgv]
  have h2 : chartVal C' k f' P =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) := by
    simp only [chartVal, hgv']
  rw [h1, h2]
  exact key _ _ (hU E H Dw l Xo c S y _ _ hx' hx) hx e e' he he' g g' hg hg'

end Formalism.MainNotions.ModuliIntegralCharts.H1
