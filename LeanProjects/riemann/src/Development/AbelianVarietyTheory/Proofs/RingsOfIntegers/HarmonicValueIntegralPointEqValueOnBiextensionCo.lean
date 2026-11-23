import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValueStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

def letterEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ) :
    Lt1 Dw × Fin n ≃ LtN Dw n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toK_prod_evV (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (K : Type) [CommRing K] [Algebra V K] {d n : ℕ}
    (f : Fin n → PS V 1 d) :
    FB.toK K (∏ b, evV (n := n) ![pt V d b] (f b)) =
      GlobalTheory.PowGerm.boxSer (fun b => MvPowerSeries.map (algebraMap V K) (f b)) := by
  have key : ∀ b : Fin n, evV (n := n) ![pt V d b] (f b) =
      MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (f b) := by
    intro b
    have hX : ∀ j : Fin 1 × Fin d,
        MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d))
          (MvPowerSeries.X j : MvPowerSeries (Fin 1 × Fin d) V) =
        (fun p : Fin 1 × Fin d => (![pt V d b] : Fin 1 → Pt V n d) p.1 p.2) j := by
      rintro ⟨i, j⟩
      rw [Fin.fin_one_eq_zero i, MvPowerSeries.rename_X]
      simp [pt]
    show evC _ (f b) = _
    exact evC_eq_algHom _ (fun j => by
      have h := (hX j).symm
      simp only at h
      rw [h, MvPowerSeries.rename_X]
      simp) _ hX (f b)
  simp only [FB.toK, key, map_prod, GlobalTheory.PowGerm.boxSer, MvPowerSeries.rename_map]

theorem nabValN_boxSer_eq_chartVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (g : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k g P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer g) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map (algebraMap c.F S) P) := by
  classical
  have hcc : MvPowerSeries.constantCoeff C.h = 0 := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.11
  have hcol : ∀ (m : LtN Dw n →₀ ℕ) (b : Fin n),
      ReciprocityTheory.ChartRestriction.G.TB.colM (Finsupp.mapDomain (letterEquiv Dw n).symm m) b = colOf m b := by
    intro m b
    unfold ReciprocityTheory.ChartRestriction.G.TB.colM colOf
    congr 1
    funext ℓ
    have hℓ : ((ℓ, b) : Lt1 Dw × Fin n) = (letterEquiv Dw n).symm ⟨ℓ.1, (ℓ.2, b)⟩ := rfl
    rw [hℓ, Finsupp.mapDomain_apply (letterEquiv Dw n).symm.injective]
  have hP : MvPolynomial.map (algebraMap c.F S) P = MvPolynomial.rename (letterEquiv Dw n)
      (MvPolynomial.rename (letterEquiv Dw n).symm (MvPolynomial.map (algebraMap c.F S) P)) := by
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
  rw [hP, GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 hcc k n g (Lt1 Dw) (LtN Dw n) (letterEquiv Dw n)
    (fun ℓ => ℓ.2.2) C.uvec (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename]
  unfold chartVal
  rw [MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  simp only [hcol]

theorem hv_eq_nabValN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C nab hnab B hB k n F f hF w P hP
  letI := io.toAlgebra
  obtain ⟨hG, hAct, -⟩ := hB
  have hgen := C.gen.1
  have hFK : B.FK T.Fr = C.ch.B.FK T.Fr := by
    unfold FB.FK FGLaw.mapF
    funext i
    simp [hG, hgen.1 i]
  have hAK : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    unfold FB.actK
    funext i
    simp [hAct, hgen.2.1 a i]
  have h1 := GlobalTheory.T.harmonicValue_eq_chart_value E H Dw l Xo c hstar nab hnab T.Fr y.1 C.ch k n F
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) (fun b => hF b) w P hP
  rw [h1, nabValN_boxSer_eq_chartVal C.ch k _ P, ← toK_prod_evV T.V T.Fr f]
  exact GlobalTheory.ChartCmp.nabValN_congr_FK C.ch.B B T.Fr hFK hAK _ _ _ _ _ _ _

end GlobalTheory.PlaceInt
