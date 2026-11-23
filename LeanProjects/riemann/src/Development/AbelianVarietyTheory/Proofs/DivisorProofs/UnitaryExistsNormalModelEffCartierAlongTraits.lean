import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaTuplesLeastOrdersUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitDivisorSupportNotMemModuliRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOrdersAllTraitsOverModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_zhModel_effCartier_orders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsProjOver X₁.M.s → ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ hproj
  obtain ⟨ι, K, hK, Jk, hJ, t, hι, ht, hloc⟩ := GlobalTheory.T.exists_finite_theta_tuples_least_orders_unitary E H Dw hpq φ hφ l Xo c C X₁
  obtain ⟨Y, πY, U₀, EE, out, hhom, hprop, hAdm, hEE, hdiv⟩ :=
    GlobalTheory.Poinc.exists_admissible_projective_theta_model X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big X₁.M hproj K Jk t ht
  obtain ⟨D, hDU, hDord⟩ := GlobalTheory.T.exists_effectiveCartier_gluing_localTuples E H Dw hpq φ hφ l Xo c C X₁ ι K Jk t ht Y U₀ EE out hAdm hdiv
    (hloc Y U₀ EE out hAdm hEE)
  have hsupp := GlobalTheory.T.unitaryTraitDivisor_support_not_mem_moduli_range E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hDU hDord
  exact ⟨ι, Y, πY, D, hι, hhom, hprop, hAdm.1.normal, hsupp,
    GlobalTheory.T.divisor_orders_all_traits_over_moduli E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hEE hhom ι D hsupp hDord⟩
