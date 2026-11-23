import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def IsComplexData : Prop :=
  l.A = 1 ∧ ∀ σ, GoodEmb c σ → IsUnf (U σ) ∧
    (∃ Kf th hr, IsLevelK (V σ) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (V σ) (dict σ) Kf th hr) ∧
    FinVol (V σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def partLat (Z : Comp Xo c) (G : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U G) :=
  (latOn U Z G).map ((Submodule.inclusion (cuspOn_le U Z G)).restrictScalars (𝓞 c.F))

def normRes (Z : Comp Xo c) (G : WTZ D.host.E) (σ : c.F →+* ℂ) (f : cuspOn U Z G) : ℝ :=
  petW U (xiR D) V dict G σ f

def degRes (Z : Comp Xo c) (G : WTZ D.host.E) : ℝ := deg (normRes U V dict Z G) (latOn U Z G)

def mass (Z : Comp Xo c) (σ : c.F →+* ℂ) : ℝ :=
  (muQ1 (V (goodOf c σ))
    (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z))).toReal

def Splits (G : WTZ D.host.E) : Prop :=
  (∀ F : cuspW Xo c U G, (F : Rul Xo c) = ∑ᶠ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∧
    ∃ h : ∀ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∈ cuspOn U Z G,
      (F ∈ latW U G ↔ ∀ Z, (⟨_, h Z⟩ : cuspOn U Z G) ∈ latOn U Z G)) ∧
  (iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) ∧ ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G) ∧
  iSupIndep (fun Z : Comp Xo c => partLat U Z G) ∧ ⨆ Z : Comp Xo c, partLat U Z G = latW U G

def Orthogonal (G : WTZ D.host.E) : Prop :=
  ∀ σ : c.F →+* ℂ,
    (∀ f : ∀ Z : Comp Xo c, cuspOn U Z G,
      petW U (xiR D) V dict G σ (∑ᶠ Z, (f Z : Rul Xo c)) ^ 2 = ∑ᶠ Z, normRes U V dict Z G σ (f Z) ^ 2) ∧
    ∀ (Z : Comp Xo c) (f : cuspOn U Z G),
      normRes U V dict Z G σ f ^ 2 = mass U V dict Z σ * normOn U (xiR D) V dict Z G σ f ^ 2

def Adds (G : WTZ D.host.E) : Prop :=
  (GoodW U (xiR D) V dict G ↔ ∀ Z, GoodOn U (xiR D) V dict Z G) ∧
  (GoodW U (xiR D) V dict G →
    (∀ Z, HasGram (normRes U V dict Z G)) ∧
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G ∧
    (∀ Z, rankOn U Z G ≠ 0 → ∀ σ, 0 < mass U V dict Z σ) ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, (degOn U (xiR D) V dict Z G -
      (rankOn U Z G : ℝ) / 2 * ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (finrank ℚ c.F : ℝ))))

def OrthSum : Prop :=
  ∀ (la : Weight Dw) (m : ℤ),
    Splits U (wtOf Dw la m) ∧ Orthogonal U V dict (wtOf Dw la m) ∧ Adds U V dict (wtOf Dw la m)

def ComponentSum : Prop :=
  ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → OrthSum U V dict

def ComponentSumDeep : Prop :=
  ∀ (D : D7) (j e : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
    InR D j → H.d = D.host.d → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD →
    IsDatW D j Dw → l.M = D.host.g 0 * D.host.g 1 * 15 ^ e → FnAlgClosed Xo c →
    IsComplexData U (fun _ => D.sp.W j) dict → OrthSum U (fun _ => D.sp.W j) dict

theorem ComponentSum.deep (h : ComponentSum) : ComponentSumDeep :=
  fun D _ _ H Dw l Xo c U dict _ _ _ _ _ _ _ hc => h D H Dw l Xo c _ U _ dict hc

theorem finite_comp : Finite (Comp Xo c) := CompFin.finite_comp Xo c

theorem partLat_le (Z : Comp Xo c) (G : WTZ D.host.E) : partLat U Z G ≤ latW U G := by
  rintro _ ⟨f, hf, rfl⟩
  exact (mem_latOn U).1 hf

theorem isComplexData_of_laws {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) :
    IsComplexData (T.U j) (T.V j) (T.dict j) :=
  ⟨h.pins.2.1.2, fun σ hσ => ⟨h.unf j hj σ hσ, by
    obtain ⟨th, hr, h1, h2⟩ := h.dictU j hj σ hσ
    exact ⟨T.Kf j σ, th, hr, h.pins.2.1.1 ▸ h.levelK j hj σ hσ, h1, h2⟩, h.finVol j hj σ hσ, h.xiAbs j hj σ hσ⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
