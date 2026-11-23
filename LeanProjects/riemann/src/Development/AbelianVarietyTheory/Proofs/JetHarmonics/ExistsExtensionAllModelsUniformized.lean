import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.IntegralPull

theorem exists_ext_all_models_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), y'.IsAlg ∧ 0 < e' ∧ (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧ letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr, (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  intro E _ _ _ H Dw l Xo c T io y hy
  have hy' : T.FinRes := hy
  obtain ⟨y, hft, hint⟩ := y
  have hint0 := hint
  obtain ⟨G, t', m1, m2, -⟩ := hint
  have : Finite (ResidueField T.V) := hy'
  obtain ⟨W', _, _, _, _, _, hfin, hinj, hres, hS⟩ :=
    GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have : CharZero W' := charZero_of_injective_algebraMap hinj
  let T' : Formalism.L2.Pj.CDVR :=
    { V := W', cr := inferInstance, dom := inferInstance, dvr := inferInstance, cpl := inferInstance,
      ch0 := inferInstance }
  have hg : Function.Injective ((algebraMap T'.V T'.Fr).comp (algebraMap T.V W')) :=
    (IsFractionRing.injective T'.V T'.Fr).comp hinj
  let ψ : T.Fr →+* T'.Fr := IsFractionRing.lift hg
  have hψ : ∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (algebraMap T.V W' a) :=
    fun a => IsFractionRing.lift_algebraMap hg a
  letI := io.toAlgebra
  letI := (ψ.comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] T'.Fr := { ψ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c T.Fr T'.Fr φ y
  have hzT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    unfold FromTest at hft ⊢
    obtain ⟨p, φ0, y0, h0⟩ := hft
    exact ⟨p, φ.comp φ0, y0, ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 _ _ _ φ0 φ y0 y z h0).1 hz⟩
  have hzI : Integral T' (ψ.comp io) z :=
    integral_baseChange T T' io (ψ.comp io) (algebraMap T.V W') hinj φ (fun a => hψ a) y z hz hint0
  have : Module.Finite T.V W' := hfin
  have : FaithfulSMul T.V W' := (faithfulSMul_iff_algebraMap_injective T.V W').mpr hinj
  have : IsLocalHom (algebraMap T.V W') := inferInstance
  obtain ⟨r, hr0, hr⟩ := exists_index (K' := T.Fr) (K'' := T'.Fr) (algebraMap T.V W') ψ hψ
  have hx : z.x = spMap ψ ≫ y.x := hz.1
  refine ⟨T', ψ.comp io, ⟨z, hzT, hzI⟩, r, hres, hr0, ?_, φ, fun a _ => hr a, hz⟩
  intro I'
  exact exists_unif_of_split T T' (algebraMap T.V W') ψ hψ m1 m2 hx I'.m1 I'.m2 hS

end GlobalTheory.IntegralPull
