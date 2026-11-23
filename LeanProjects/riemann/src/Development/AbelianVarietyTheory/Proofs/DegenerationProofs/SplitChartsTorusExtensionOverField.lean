import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSumOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.SplitChartsField

open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS

include hinj in

theorem exists_mem_basicOpen (P : Γ(G.left, q ⁻¹ᵁ V) → Prop)
    (hP : ∀ x ∈ q ⁻¹ᵁ V, ∃ b, IsWt i _ b 0 ∧ x ∈ G.left.basicOpen b ∧ P b) {y : B} (hy : y ∈ V) :
    ∃ c : Γ(B, V), y ∈ B.basicOpen c ∧ P ((q.app V).hom c) := by
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  let s : Set Γ(B, V) := {c | P ((q.app V).hom c)}
  let α : Γ(B, V) →+* wtZero i (q ⁻¹ᵁ V) := (q.app V).hom.codRestrict _ fun c => (h₀ _).2 ⟨c, rfl⟩
  have hα : Function.Bijective α := ⟨fun a b h => hinj (congrArg Subtype.val h), fun a => by
    obtain ⟨c, hc⟩ := (h₀ a.1).1 a.2
    exact ⟨c, Subtype.ext hc⟩⟩
  have h1 : Ideal.span ((q.app V).hom '' s) = ⊤ := by
    rw [← (hV.preimage q).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hb, hxb, hPb⟩ := hP x hx
    obtain ⟨c, rfl⟩ := (h₀ b).1 hb
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, c, hPb, rfl⟩, hxb⟩
  have h2 : (1 : wtZero i (q ⁻¹ᵁ V)) ∈ (Ideal.span s).map α := hG.mem_map _ α 1 (by
    rw [Ideal.map_span]
    exact h1.ge trivial)
  have h3 : Ideal.span s = ⊤ := by
    obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).1 h2
    rw [Ideal.eq_top_iff_one, ← hα.1 (e.trans (map_one α).symm)]
    exact hc
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV.self_le_iSup_basicOpen_iff.2 h3 hy)
  exact ⟨c.1, hc, c.2⟩

theorem isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by
  have e : q ⁻¹ᵁ B.basicOpen c = G.left.basicOpen ((q.app V).hom c) := Scheme.preimage_basicOpen _ _
  have hle := B.basicOpen_le c
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  have hS' : Stable i (q ⁻¹ᵁ B.basicOpen c) := e ▸ stable_basicOpen hS (hasWt_iff.2 ((h₀ _).2 ⟨c, rfl⟩))
  have hG' : Graded i (q ⁻¹ᵁ B.basicOpen c) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ ((hV.basicOpen c).preimage q) (preimage_le_of_stable hS')
  have hw : ∀ x, IsWt i _ ((q.app (B.basicOpen c)).hom (rs hle x)) 0 := fun x => by
    rw [app_rs]
    exact ((h₀ _).2 ⟨x, rfl⟩).res _
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  constructor
  · intro ha
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul (hV.preimage q) (q.preimage_mono hle) _ a e
    rw [← app_rs q hle] at hy
    obtain ⟨x, hx, hx'⟩ := hG.exists_lift hG' (rs (q.preimage_mono hle)) (fun _ _ hx => hx.res _) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (S := wtZero i _) (hw c) n) ha)
    obtain ⟨x, rfl⟩ := (h₀ x).1 hx
    refine ⟨(v⁻¹).val ^ n * rs hle x, ?_⟩
    rw [map_mul, app_rs, hx', hy, ← hv, ← map_pow _ v.val, ← _root_.mul_assoc, ← map_mul, ← mul_pow,
      Units.inv_mul, one_pow, map_one, _root_.one_mul]
  · rintro ⟨c', rfl⟩
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c c' rfl
    have e' : c' = (v⁻¹).val ^ n * rs hle y := by
      rw [hy, ← hv, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
    have h1 : IsWt i _ (Units.map (q.app (B.basicOpen c)).hom.toMonoidHom v).val 0 := by
      have := hw c
      rwa [← hv] at this
    have h2 := h1.inv
    rw [neg_zero] at h2
    rw [e', map_mul, map_pow]
    exact mul_mem (pow_mem (S := wtZero i _) h2 n) (hw y)

omit hi h₀ hS in
include hinj in

theorem injective_basicOpen (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this

omit hi hV h₀ hS in

theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  obtain ⟨B, q, hp, ha, V, hcov, hV⟩ := Charts.Torus.exists_proper_quotient K H C d c i hT
  obtain ⟨hm, hf, hs, hsm, hfib⟩ := GlobalTheory.LocTriv.main (Sp K) (Fin d → ℤ) H B i q hT.hom ha fun y => by
    obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    obtain ⟨haff, h, hinj, h₀⟩ := hV a
    have hS := hT.stable a
    have hl := GlobalTheory.LocalWeightUnits.main K H C d c i hT a
    generalize C.W a = W at h hinj h₀ hS hl
    subst h
    rw [Scheme.Hom.appLE_eq_app] at hinj h₀
    have h₀' := fun u => hasWt_iff.symm.trans (h₀ u)
    obtain ⟨b, hb, hb₁, u, hu⟩ := exists_mem_basicOpen hT.hom haff h₀' hinj hS
      (fun b => Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ,
        ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ)
      (fun x hx => (hl x hx).imp fun b hb => ⟨hasWt_iff.1 hb.1, hb.2⟩) hy
    refine ⟨B.left.basicOpen b, hb, haff.basicOpen b, isWt_basicOpen_iff hT.hom haff h₀' hS b,
      injective_basicOpen haff hinj b, ?_⟩
    rw [Scheme.preimage_basicOpen]
    exact ⟨preimage_le_of_stable hb₁, u, fun χ => hasWt_iff.1 (hu χ)⟩
  obtain ⟨g, hcomm, hq, hker⟩ :=
    GlobalTheory.grpObj_of_flat_coset_quotient (Sp K) H _ B i q hT.hom hm hf hs inferInstance hfib
  have : GeometricallyConnected (q.left ≫ B.hom) := by rwa [Over.w]
  refine ⟨B, g, q, ⟨hcomm, hsm inferInstance, hp, geometricallyConnected_of_surjective q.left B.hom⟩, hq, hf, hs, ha,
    hker, fun a => ?_⟩
  obtain ⟨haff, h, -, h₀⟩ := hV a
  exact ⟨V a, h, haff, h₀⟩

end GlobalTheory.SplitChartsField
