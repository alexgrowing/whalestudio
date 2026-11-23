import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy.MultIso

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  have : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  have hIJ : Ideal.span {e a} = (Ideal.span {a}).map (e : A →+* B) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e hIJ
  let f : (A ⧸ Ideal.span {a}) →ₛₗ[(e : A →+* B)] (B ⧸ Ideal.span {e a}) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun r x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        show q (Ideal.Quotient.mk _ (r * y)) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ y)
        rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, map_mul, map_mul] }
  rw [Ring.ord, Ring.ord, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f q.bijective)]

theorem ordFrac_ringEquiv {A B K L : Type} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (e : A ≃+* B) (φ : K →+* L) (h : ∀ a, φ (algebraMap A K a) = algebraMap B L (e a)) (f : K) :
    Ring.ordFrac B (φ f) = Ring.ordFrac A f := by
  have key : ∀ a : A, Ring.ordFrac B (algebraMap B L (e a)) = Ring.ordFrac A (algebraMap A K a) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    have hea : e a ≠ 0 := by simpa using ha
    rw [Ring.ordFrac_eq_ord (R := B) (K := L) hea, Ring.ordFrac_eq_ord (R := A) (K := K) ha]
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, ha, hea, not_false_eq_true, if_true,
      ord_ringEquiv]
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  dsimp only at hxy
  subst hxy
  have hspec := IsLocalization.mk'_spec K x y
  have h1 : Ring.ordFrac A (IsLocalization.mk' K x y) * Ring.ordFrac A (algebraMap A K y) =
      Ring.ordFrac A (algebraMap A K x) := by rw [← map_mul, hspec]
  have h2 : Ring.ordFrac B (φ (IsLocalization.mk' K x y)) * Ring.ordFrac B (algebraMap B L (e y)) =
      Ring.ordFrac B (algebraMap B L (e x)) := by rw [← map_mul, ← h, ← map_mul, hspec, h]
  rw [key, key] at h2
  have hy : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hc : Ring.ordFrac A (algebraMap A K y) ≠ 0 := (map_ne_zero _).mpr hy
  exact mul_right_cancel₀ hc (h2.trans h1.symm)

private theorem isIso_stalkMap_restrict_of_isIso {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (x : s ⁻¹ᵁ U) : IsIso ((s ∣_ U).stalkMap x) := by
  have h : IsOpenImmersion (s ∣_ U) := inferInstance
  exact LocallyRingedSpace.IsOpenImmersion.stalk_iso (H := h) (s ∣_ U).toLRSHom x

theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (w : Y) (hw : s w ∈ U) : IsIso (s.stalkMap w) := by
  have hw' : w ∈ s ⁻¹ᵁ U := hw
  have e := morphismRestrictStalkMap s U ⟨w, hw'⟩
  have hi : IsIso ((s ∣_ U).stalkMap ⟨w, hw'⟩) := isIso_stalkMap_restrict_of_isIso s U _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp hi

theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{0}} (s : Y ⟶ X) (w : Y)
    [IsIso (s.stalkMap w)] : Order.coheight w = Order.coheight (s w) := by
  apply WithBot.coe_injective
  rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv).symm

theorem ord_functionFieldMap_of_isIso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (w : Y)
    [IsIso (s.stalkMap w)] (f : X.functionField) :
    Scheme.ord (functionFieldMap s f) w = Scheme.ord f (s w) := by
  have hco := coheight_eq_of_isIso_stalkMap s w
  by_cases hc : Order.coheight (s w) = 1
  · have hw : Order.coheight w = 1 := hco.trans hc
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hw, Scheme.ord_eq_ordHom_of_coheight_eq_one hc]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (s w)) := krullDimLE_of_coheight_le hc.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    congr 2
    exact ordFrac_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv (functionFieldMap s)
      (fun a => functionFieldMap_algebraMap s w a) f
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hc,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hc (hco ▸ h))]

theorem coheight_eq_and_mult_pullCart : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  intro X Y _ _ s _ _ _ U hU w hw
  haveI := hU
  haveI := isIso_stalkMap_of_isIso_restrict s U w hw
  refine ⟨coheight_eq_of_isIso_stalkMap s w, fun D => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn (s w)
  rw [(isEqn_pullCart s hg).mult_eq, hg.mult_eq]
  exact ord_functionFieldMap_of_isIso s w (g : X.functionField)

end GlobalTheory.Discrepancy.MultIso
