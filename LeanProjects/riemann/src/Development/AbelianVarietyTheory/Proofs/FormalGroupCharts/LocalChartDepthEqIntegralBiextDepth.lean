import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nabValN_congr_FK {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) (B' : FB R' d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [Algebra R' k]
    (hF : B'.FK k = B.FK k) (hA : ∀ a, B'.actK k a = B.actK k a)
    (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {κ : Type} [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    nabValN B k h w0 m f cp u P = nabValN B' k h w0 m f cp u P := by
  unfold nabValN FB.hL
  rw [hF, hA]

theorem isIntPS_iff_exists_map (T : CDVR) {n d : ℕ} (f : PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro hf
    choose g hg using hf
    refine ⟨g, ?_⟩
    ext m
    exact (MvPowerSeries.coeff_map _ _ _).trans (hg m)
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem nuLocC_eq_nuAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  intro E _ _ _ H Dw l Xo c _ T io y C
  letI := io.toAlgebra
  intro BT hF hA e k a n
  unfold nuLocC nuAlg
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    refine iInf_le_of_le (MvPowerSeries.map (algebraMap T.V T.Fr) g) ?_
    refine iInf_le_of_le ((isIntPS_iff_exists_map T _).2 ⟨g, rfl⟩) ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _))
  · refine le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨g, rfl⟩ := (isIntPS_iff_exists_map T _).1 hf
    refine iInf_le_of_le g ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _)).symm

end GlobalTheory.ChartCmp
