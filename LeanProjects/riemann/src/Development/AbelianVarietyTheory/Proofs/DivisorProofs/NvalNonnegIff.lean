import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem nval_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) (x : K') :
    0 ≤ nval V e x ↔ (x ≠ 0 → 0 ≤ vV V x) := by
  by_cases hx : x = 0
  · subst hx; simp [nval_zero]
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast he), zero_mul]
  simp only [ne_eq, hx, not_false_eq_true, forall_const]
  norm_cast

theorem intAt_iff {Xo : Moduli Dw l} {c : Coeff l} (f : Rul Xo c) :
    IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
      evI y f ≠ 0 → 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io y hy hne
    obtain ⟨la, e, ho⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T io hy
    have := h la _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho y hy () trivial, rfl⟩
    exact (nval_nonneg_iff ho.1 _).1 this hne
  · rintro h la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    exact (nval_nonneg_iff ho.1 _).2 (h T ι y hy)

theorem pull_intAt_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → (IntAt d.Xo₂ d.c₂ g ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hO a n f hf g hg hP
  rw [intAt_iff, intAt_iff]
  constructor
  · intro hG T io y hy hne
    obtain ⟨T', iT, e, y', io₂, y₂, ⟨he, hv, φ, hφ, hm⟩, hfin, hio, hover⟩ :=
      GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c 0 d hlev T io y hy
    have h1 : evI y₂ g = evI y' f := by
      letI := (iT.comp io).toAlgebra
      letI := io₂.toAlgebra
      exact GlobalTheory.CoverDown.evR_eq_of_pull hf hg hP (fun a => hio a) hover
    have h2 : evI y' f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      have := GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1
        (GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y.1) y'.1 hm
      show evR Xo c f y'.1 = iT (evR Xo c f y.1)
      rw [this]
      exact DFunLike.congr_fun hφ _
    have key := hG T' io₂ y₂ hfin (by rw [h1, h2]; exact (map_ne_zero iT).2 hne)
    rw [h1, h2, hv] at key
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast he)).1 key
  · intro hF T io₂ y₂ hy hne
    obtain ⟨y, hyalg, -, hval⟩ := GlobalTheory.CoverDown.exists_intFr_below E H Dw l Xo c d hpq hlev hO T io₂ y₂ hy
    rw [hval a n f hf g hg hP] at hne ⊢
    exact hF T _ y hyalg hne

end GlobalTheory.CoverInt
