import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValCmp

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem pt_eq_comp (M : RatModel k Ω) (z : M.Z) :
    M.pt = spMap (M.O z).val.toRingHom ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z) := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine h1.symm.trans ?_
  rw [← h2, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem hasDiv_of_forall_cDvr : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (J J' : Type) [Fintype J] (th : J → Ω) (e : J' → Ω) (D : ℕ), 1 ≤ D → Geo.Tor.IsNormalScheme M.Z → M.HasDiv e → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V), jK V ≫ ξ = spMap emb ≫ M.pt → ∀ j₀, e j₀ ≠ 0 → (∀ j, emb (e j / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V))) → M.HasDiv th := by
  intro k Ω _ _ _ _ _ M J J' _ th e D hD hN he H z
  obtain ⟨j₀, hj₀, hej⟩ := he z
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧
        ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V)) := by
    intro V _ _ _ hV φ hφ
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have e1 : jK V ≫ spMap φ = spMap emb ≫ spMap (M.O z).val.toRingHom := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact (hemb r).symm
    have hcomp : jK V ≫ (spMap φ ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z)) = spMap emb ≫ M.pt := by
      rw [pt_eq_comp M z, ← Category.assoc, e1, Category.assoc]
    refine ⟨emb, hemb, H V hV _ emb hcomp j₀ hj₀ fun j => ⟨φ ⟨_, hej j⟩, (hemb ⟨_, hej j⟩).symm⟩⟩
  have hmem : ∀ b, th b ^ D / e j₀ ∈ M.O z := by
    intro b
    obtain ⟨a, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (th b ^ D / e j₀)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ a := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian (M.O z) a s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, h1, -⟩ := key V hV φ hφ
      obtain ⟨v, hv⟩ := h1 b
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  obtain ⟨emb, hemb, -, b, hb, w, hw⟩ := key V hV φ hφ
  have hu : IsUnit (⟨th b ^ D / e j₀, hmem b⟩ : M.O z) := by
    apply isUnit_of_map_unit φ
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, map_one, hw, ← hemb, ← map_mul]
    have e2 : algebraMap (M.O z) Ω ⟨th b ^ D / e j₀, hmem b⟩ * (e j₀ / th b ^ D) = 1 := by
      change th b ^ D / e j₀ * (e j₀ / th b ^ D) = 1
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      field_simp
    rw [e2, map_one]
  have hinv := ((RatModel.isUnit_O_iff _).1 hu).2
  refine ⟨b, hb, fun b' => ?_⟩
  have hp : (th b' / th b) ^ D ∈ M.O z := by
    have h3 := mul_mem (hmem b') hinv
    have e3 : th b' ^ D / e j₀ * (th b ^ D / e j₀)⁻¹ = (th b' / th b) ^ D := by
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      rw [inv_div, div_pow]
      field_simp
    simpa only [e3] using h3
  have hint : IsIntegral (M.O z) (th b' / th b) := by
    refine IsIntegral.of_pow (n := D) (by omega) ?_
    have := isIntegral_algebraMap (R := M.O z) (A := Ω) (x := ⟨_, hp⟩)
    simpa using this
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

end GlobalTheory.ValCmp
