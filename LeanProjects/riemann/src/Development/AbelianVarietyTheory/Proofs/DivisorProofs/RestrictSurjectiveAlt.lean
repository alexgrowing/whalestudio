import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOntoSpread

theorem restrict_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → Function.Surjective ρ := by
  intro R _ _ _ _ G _ _ hG D A U V _ _ _ _ G' _ _ _ D' A' U' g β _ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, m₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψl, hm₁, hj, _, _, _, hΩ, h₀j⟩ := hsp
  haveI := hψl; haveI := hj
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ G G₁ m₁ hm₁ hG
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V₁) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V₁) 0 ≫ j := by
    haveI : IsSeparated G₁.hom := hG₁.separated
    have hjac : maximalIdeal V₁ ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V₁ (maximalIdeal V₁) hjac (splitTorus (Sp V₁) F) G₁ _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V₁ := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V₁ ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V₁).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V₁ →+* V₁ ⧸ maximalIdeal V₁ ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback G₁ (thick V₁ (maximalIdeal V₁) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V₁ ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V₁ (maximalIdeal V₁) e G₁) G (spMap (q.comp ψ))
        (pullback.fst G₁.hom (thick V₁ (maximalIdeal V₁) e) ≫ m₁) :=
      (he.comp hm₁).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha hR
    obtain ⟨ρe, hρe⟩ := hfac D'.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance
    have hres : ∀ x ∈ maximalIdeal V₁ ^ (e + 1), residue V₁ x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres hm₀
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V₁).comp ψ) x = 0 := fun x hx =>
      h₀ x (by rw [zero_add, pow_one]; exact Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus hm₀ j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he hm₀ (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres hm₀).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (U.gt e) ha' hm₀' :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V₁) hres) (U.gt e) ha ha' hR hm₀' ke
        (RingHom.ext fun x => rfl)
        (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst])
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha' hm₀'
    obtain ⟨u, hu⟩ := hfac' D.toPre.X (GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _ =
      pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :=
    (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U'.gt 0) hb hn').1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOntoSpread
