import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GoodRedU

theorem subsingleton_lattice_of_range_subset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out _ T ξ hξ ⟨ξ₀, hξ₀, hlies⟩
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1

  have hr : Set.range ξ ⊆ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hξ
  let ξ' : Sp T.V ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι ξ hr
  have hξ' : ξ' ≫ U₀.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hK : jK T.V ≫ ξ' = ξ₀ := by
    rw [← cancel_mono U₀.ι, Category.assoc, hξ', hξ₀]
  let q : Sp T.V ⟶ Sp X₁.S.R := ξ' ≫ out.u₀
  have hB := GlobalTheory.isAbelianScheme_pullback_obj q X₁.ρ.P.A X₁.ρ.P.isAb

  obtain ⟨g, hg⟩ := Spec.map_surjective (ξ₀ ≫ out.u₀)
  have hf : X₁.Lies (spMap g.hom) T.y := by
    show X₁.Lies (Spec.map (CommRingCat.ofHom g.hom)) T.y
    rw [CommRingCat.ofHom_hom, hg]; exact hlies
  obtain ⟨G, _, α, β, hα, hβ, -⟩ := hf.uOver
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₂.cart hβ
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (isGrpPullback_pullback T.t.G (jK T.V)) m₁.cart
  haveI := he₁
  haveI := he₂
  have hq : spMap g.hom = jK T.V ≫ q := by
    show Spec.map (CommRingCat.ofHom g.hom) = _
    rw [CommRingCat.ofHom_hom, hg, ← hK, Category.assoc]
  have h₁ := ((isGrpPullback_of_iso e₂).comp ((isGrpPullback_of_iso e₁).comp hα)).congr
    (by rw [Category.id_comp, Category.id_comp, hq]) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback q).obj X₁.ρ.P.A) (jK T.V)).comp
    (isGrpPullback_pullback X₁.ρ.P.A q)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨Eiso, -, -⟩ := TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso Eiso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map Eiso.hom))
    rw [← Over.w Eiso.hom]
    infer_instance
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus T.t.G := fun _ _ _ _ _ => inferInstance
  exact ChartNotAb.subsingleton_of_closed_mem_abLocus T.P hc

end GlobalTheory.UPoinc.GoodRedU
