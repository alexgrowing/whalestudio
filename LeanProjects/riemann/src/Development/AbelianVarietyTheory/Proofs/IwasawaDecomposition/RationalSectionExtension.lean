import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

set_option autoImplicit false

namespace GlobalTheory.RestrictRatSec

theorem top_le_of_below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) {U : Z.Opens}
    (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_appLE {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) (y : Sp K ⟶ Y)
    (z : Sp K ⟶ X) (e : z = y ≫ j) {U : X.Opens} {W : Y.Opens} (l : W ≤ j ⁻¹ᵁ U) (hW : below y ∈ W)
    (h : genericPoint Y ∈ W) (hz : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) :
    valAt y (fnOf W h ((j.appLE U W l).hom a)) =
      (z.appLE U ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  subst e
  rw [OfModel.valAt_fnOf y hW (top_le_of_below y hW), ← Scheme.Hom.appLE_comp_appLE y j U W ⊤ l
    (top_le_of_below y hW)]
  rfl

theorem mem_pullU {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c : (B.pull j).ι) (x : Y) :
    x ∈ (B.pull j).U c ↔ j x ∈ B.U (c PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem inf_le_pull {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    (B.pull j).U c ⊓ (B.pull j).U c' ≤ j ⁻¹ᵁ (B.U (c PUnit.unit) ⊓ B.U (c' PUnit.unit)) :=
  fun x hx => ⟨(mem_pullU B j c x).1 hx.1, (mem_pullU B j c' x).1 hx.2⟩

theorem val_pull_g {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    ((B.pull j).g c c').val =
      (j.appLE _ _ (inf_le_pull B j c c')).hom (B.g (c PUnit.unit) (c' PUnit.unit)).val := by
  have : (B.pull j).g c c' =
      res (inf_le_pull B j c c') (pullU j _ (B.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem exists_lift {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [SurjectiveOnStalks j] (x : Y)
    {f : Y.functionField} (hf : UnitAt x f) :
    ∃ (W : X.Opens) (hx : j x ∈ W) (a : Γ(X, W)), j x ∈ X.basicOpen a ∧
      fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.appLE W _ le_rfl).hom a) = f := by
  obtain ⟨b, -, hb⟩ := id hf
  obtain ⟨b', rfl⟩ := j.stalkMap_surjective x b
  obtain ⟨W, hx, a, rfl⟩ := X.presheaf.exists_germ_eq b'
  have e : fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.app W).hom a) = f := by
    rw [← algebraMap_germ (x := x) hx, ← hb]
    exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j W x hx a).symm
  refine ⟨W, hx, a, ?_, by rw [← Scheme.Hom.app_eq_appLE]; exact e⟩
  have := (unitAt_fnOf_iff (U := j ⁻¹ᵁ W) (x := x) hx _ _).1 (e ▸ hf)
  rw [← Scheme.preimage_basicOpen] at this
  exact this

theorem exists_restriction : ∀ (X Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (j : Y ⟶ X) [SurjectiveOnStalks j] (i : Z ⟶ X) (x : Y), i (genericPoint Z) = j x → ∀ (B : LB X), B.IsLB → ∀ (r : (B.pull j).ι → Y.functionFieldˣ), IsRatSec (B.pull j) r → ∀ (u : Y.functionFieldˣ), (∀ c, x ∈ (B.pull j).U c → UnitAt x ((u * r c : Y.functionFieldˣ) : Y.functionField)) → ∃ s : (B.pull i).ι → Z.functionFieldˣ, IsRatSec (B.pull i) s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Y) (y' : Sp K ⟶ Z) (c : B.ι), y ≫ j = y' ≫ i → below y = x → below y' = genericPoint Z → j x ∈ B.U c → valAt y' (s (fun _ => c) : Z.functionField) = valAt y ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) := by
  intro X Y Z _ _ j _ i x hi B hB r hr u hu
  obtain ⟨c₀, hc₀⟩ := exists_chart hB (j x)
  have hx₀ : x ∈ (B.pull j).U (fun _ => c₀) := (mem_pullU B j _ x).2 hc₀
  obtain ⟨W, hW, a, ha, e⟩ := exists_lift j x (hu _ hx₀)
  have hgW : genericPoint Z ∈ i ⁻¹ᵁ W := show i _ ∈ W from hi ▸ hW
  have hg₀ : genericPoint Z ∈ (B.pull i).U (fun _ => c₀) := (mem_pullU B i _ _).2 (hi ▸ hc₀)
  have hne : fnOf (i ⁻¹ᵁ W) hgW ((i.appLE W _ le_rfl).hom a) ≠ 0 := by
    refine UnitAt.ne_zero (x := genericPoint Z) ((unitAt_fnOf_iff hgW _ _).2 ?_)
    rw [← Scheme.Hom.app_eq_appLE, ← Scheme.preimage_basicOpen]
    exact show i _ ∈ X.basicOpen a from hi ▸ ha
  refine ⟨fun c => frameRat (B.pull i) _ hg₀ c * Units.mk0 _ hne, fun c c' h => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, isRatSec_frameRat (LB.isLB_pull hB i) _ hg₀ c c' h, mul_assoc]
  intro K _ y y' c hy hyx hy' hc
  have hxc : x ∈ (B.pull j).U (fun _ => c) := (mem_pullU B j _ x).2 hc
  have hgc : genericPoint Z ∈ (B.pull i).U (fun _ => c) := (mem_pullU B i _ _).2 (hi ▸ hc)
  have hb : below (y ≫ j) = j x := hyx ▸ rfl
  have h₁ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.U c ⊓ B.U c₀) := top_le_of_below _ (hb ▸ memInf hc hc₀)
  have h₂ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ W := top_le_of_below _ (hb ▸ hW)
  have hxx := memInf hxc hx₀
  have hgg := memInf hgc hg₀
  have e₁ : ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) =
      fnOf _ (gen_mem hxx) ((B.pull j).g (fun _ => c) (fun _ => c₀)).val *
        ((u * r (fun _ => c₀) : Y.functionFieldˣ) : Y.functionField) := by
    rw [Units.val_mul, Units.val_mul, hr _ _ (gen_mem hxx), mul_left_comm]
  have hxW : x ∈ j ⁻¹ᵁ W := hW
  rw [← hyx] at hxx hxW
  rw [← hy'] at hgg hgW
  have v₁ := valAt_appLE j y _ rfl (inf_le_pull B j (fun _ => c) (fun _ => c₀)) hxx (gen_mem hxx) h₁
    (B.g c c₀).val
  have v₂ := valAt_appLE i y' _ hy (inf_le_pull B i (fun _ => c) (fun _ => c₀)) hgg (gen_mem hgg) h₁
    (B.g c c₀).val
  have w₁ := congrArg (fun t => valAt y (fnOf _ (gen_mem hxx) t)) (val_pull_g B j (fun _ => c) (fun _ => c₀))
  have w₂ := congrArg (fun t => valAt y' (fnOf _ (gen_mem hgg) t)) (val_pull_g B i (fun _ => c) (fun _ => c₀))
  have t₁ := valAt_appLE j y _ rfl le_rfl hxW (gen_mem hxW) h₂ a
  have t₂ := valAt_appLE i y' _ hy le_rfl hgW (gen_mem hgW) h₂ a
  rw [e₁, ← e, OfModel.valAt_mul y (regAt_fnOf hxx _ _) (regAt_fnOf hxW _ _), Units.val_mul, Units.val_mk0]
  refine (congrArg (fun t => valAt y' (t * _)) (val_frameRat _ hg₀ _ hgc)).trans ?_
  refine (OfModel.valAt_mul y' (regAt_fnOf hgg _ _) (regAt_fnOf hgW _ _)).trans ?_
  exact congrArg₂ (· * ·) ((w₂.trans v₂).trans (w₁.trans v₁).symm) (t₂.trans t₁.symm)

end GlobalTheory.RestrictRatSec
