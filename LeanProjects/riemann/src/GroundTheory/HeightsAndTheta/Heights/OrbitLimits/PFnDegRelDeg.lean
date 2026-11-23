import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsFnDegRelDeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

namespace FnDegRelDeg

theorem exists_div_of_mem_adjoin {F R L : Type*} [Field F] [CommRing R] [Field L] [Algebra F L]
    (τ : R →+* L) (hF : ∀ c : F, ∃ x, τ x = algebraMap F L c) {z : L}
    (hz : z ∈ IntermediateField.adjoin F (Set.range τ)) : ∃ x y, z = τ x / τ y := by
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  let S : Subalgebra F L := { τ.rangeS with algebraMap_mem' := fun c => RingHom.mem_rangeS.2 (hF c) }
  have hle : Algebra.adjoin F (Set.range τ) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact RingHom.mem_rangeS.2 ⟨x, rfl⟩)
  obtain ⟨x, rfl⟩ := RingHom.mem_rangeS.1 (hle hr)
  obtain ⟨y, rfl⟩ := RingHom.mem_rangeS.1 (hle hs)
  exact ⟨x, y, rfl⟩

theorem isFractionRing_codRestrict {R L F' : Type*} [CommRing R] [Field L] [Field F'] [Algebra F' L]
    (E : IntermediateField F' L) (τ : R →+* L) (hτ : Function.Injective τ) (hmem : ∀ x, τ x ∈ E)
    (hq : ∀ z ∈ E, ∃ x y, z = τ x / τ y) :
    letI := (τ.codRestrict E hmem).toAlgebra
    IsFractionRing R E := by
  let _ := (τ.codRestrict E hmem).toAlgebra
  have hinj : Function.Injective (algebraMap R E) := fun a b h => hτ (congrArg Subtype.val h)
  have : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 hinj
  refine IsFractionRing.of_field R E fun z => ?_
  obtain ⟨x, y, hxy⟩ := hq z z.2
  refine ⟨x, y, Subtype.ext ?_⟩
  rw [IntermediateField.coe_div]
  exact hxy

theorem finrank_eq_relfinrank {F R₁ R₂ L : Type*} [Field F] [CommRing R₁] [CommRing R₂] [Field L]
    [Algebra F L] [Algebra R₁ R₂] (ρ : R₂ →+* L) (hρ : Function.Injective ρ)
    (E H : IntermediateField F L) (hEH : E ≤ H)
    (hτ : Function.Injective (ρ.comp (algebraMap R₁ R₂)))
    (hτE : ∀ x, ρ (algebraMap R₁ R₂ x) ∈ E) (hρH : ∀ x, ρ x ∈ H)
    (hEq : ∀ z ∈ E, ∃ x y, z = ρ (algebraMap R₁ R₂ x) / ρ (algebraMap R₁ R₂ y))
    (hHq : ∀ z ∈ H, ∃ x y, z = ρ x / ρ y) :
    Module.finrank R₁ R₂ = IntermediateField.relfinrank E H := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hEH]
  set H' := IntermediateField.extendScalars hEH
  have hρH' : ∀ x, ρ x ∈ H' := fun x => (IntermediateField.mem_extendScalars hEH).2 (hρH x)
  let _ : Algebra R₁ E := ((ρ.comp (algebraMap R₁ R₂)).codRestrict E hτE).toAlgebra
  let _ : Algebra R₂ H' := (ρ.codRestrict H' hρH').toAlgebra
  let _ : Algebra R₁ H' := ((algebraMap R₂ H').comp (algebraMap R₁ R₂)).toAlgebra
  have : IsScalarTower R₁ R₂ H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ E H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing R₁ E := isFractionRing_codRestrict E _ hτ hτE hEq
  have : IsFractionRing R₂ H' := isFractionRing_codRestrict H' ρ hρ hρH' fun z hz =>
    hHq z ((IntermediateField.mem_extendScalars hEH).1 hz)
  exact (IsFractionRing.finrank_eq R₁ E R₂ H').symm

section Dehom

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem dehom_mem_homFracDegZero (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) (f : MRing ι F) :
    IntNumPoint.dehom V i f ∈ homFracDegZero V := by
  have : (IntNumPoint.dehom V i).range ≤ (homFracDegZero V).toSubalgebra := by
    rw [IntNumPoint.dehom, aeval_range]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin F _
      ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
        isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
  exact this ⟨f, rfl⟩

theorem div_eq_dehom_div (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) {b : K → ℕ} {f g : MRing ι F}
    (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) :
    algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V f) /
        algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V g) =
      IntNumPoint.dehom V i f / IntNumPoint.dehom V i g := by
  rw [← IntNumPoint.cls_apply, ← IntNumPoint.cls_apply,
    ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hf, ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hg,
    mul_div_mul_right _ _ (IntNumPoint.chartProd_ne_zero i hi b)]

end Dehom

section Contract

variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')

theorem contractFracMap_algebraMap (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl

theorem contractFracMap_comp_dehom :
    (contractFracMap j P').comp (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))) =
      (IntNumPoint.dehom P' i').comp (rename (blockIncl j ι')) := by
  refine MvPolynomial.algHom_ext fun r => ?_
  simp only [AlgHom.comp_apply, IntNumPoint.dehom, aeval_X, rename_X, map_div₀, IntNumPoint.xc,
    contractFracMap_algebraMap]
  rfl

end Contract

theorem proof : FnDegRelDeg.Statement.{u} := by
  intro F _ K K' _ _ _ _ ι _ ι' _ κ v hκv P' hP' i' hi
  have := hP'.isPrime
  set j : K ↪ K' := ⟨κ, hκv.1⟩

  have hu : ∀ q : Σ k, ι k, ∃ r : ι' (j q.1), blockIncl j ι' ⟨q.1, r⟩ = v q := by
    intro q
    have h := hκv.2.2.1 q
    revert h
    generalize v q = q'
    obtain ⟨k', r⟩ := q'
    rintro (h : k' = κ q.1)
    subst h
    exact ⟨r, rfl⟩
  let ucoord : (Σ k, ι k) → (Σ k, ι' (j k)) := fun q => ⟨q.1, (hu q).choose⟩
  have hucoord : blockIncl j ι' ∘ ucoord = v := funext fun q => (hu q).choose_spec
  have hw : ∀ r : Σ k, ι' (j k), ∃ q, v q = blockIncl j ι' r := fun r => hκv.2.2.2 _ ⟨r.1, rfl⟩
  let wcoord : (Σ k, ι' (j k)) → (Σ k, ι k) := fun r => (hw r).choose
  have hwcoord : v ∘ wcoord = blockIncl j ι' := funext fun r => (hw r).choose_spec
  have hi0 : ∀ k, (X ⟨k, i' (j k)⟩ : MRing (fun k => ι' (j k)) F) ∉ contractPrime j P' := by
    intro k h
    have h' := Ideal.mem_comap.1 h
    rw [rename_X] at h'
    exact hi (j k) h'

  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal P' i') (IntNumPoint.dehom P' i')
    (fun a ha => IntNumPoint.dehom_eq_zero_of_mem_chartIdeal i' hi hP'.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = IntNumPoint.dehom P' i' f := fun f => rfl
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (IntNumPoint.mem_chartIdeal_of_dehom_eq_zero i' hi ha)
  let _ := (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i').toAlgebra
  have hτ : ∀ p : MRing ι F, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ p)) =
      IntNumPoint.dehom P' i' (rename v p) := fun p => rfl
  have key : ∀ p : MRing ι F, IntNumPoint.dehom P' i' (rename v p) =
      contractFracMap j P' (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))
        (rename ucoord p)) := by
    intro p
    have e : rename v p = rename (blockIncl j ι') (rename ucoord p) := by
      rw [rename_rename, hucoord]
    rw [e]
    exact (AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') _).symm
  have key2 : ∀ f, contractFracMap j P' (IntNumPoint.dehom (contractPrime j P')
      (fun k => i' (j k)) f) =
      ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (rename wcoord f))) := by
    intro f
    rw [hτ, rename_rename, hwcoord]
    exact AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') f
  have hρH : ∀ x, ρ x ∈ homFracDegZero P' := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact dehom_mem_homFracDegZero P' i' hi f
  have hτE : ∀ x, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) ∈
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ, key]
    exact (IntermediateField.mem_map _).2 ⟨_, dehom_mem_homFracDegZero _ _ hi0 _, rfl⟩
  have hHq : ∀ z ∈ homFracDegZero P', ∃ x y, z = ρ x / ρ y := by
    intro z hz
    refine exists_div_of_mem_adjoin ρ.toRingHom (fun c => ⟨algebraMap F _ c, ρ.commutes c⟩) ?_
    revert z
    show homFracDegZero P' ≤ _
    unfold homFracDegZero
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [div_eq_dehom_div P' i' hi hf hg]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ f, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ g, rfl⟩)
  have hEq : ∀ z ∈ (homFracDegZero (contractPrime j P')).map (contractFracMap j P'),
      ∃ x y, z = ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) /
        ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' y) := by
    intro z hz
    refine exists_div_of_mem_adjoin (ρ.toRingHom.comp (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i'))
      (fun c => ⟨Ideal.Quotient.mk _ (C c), ?_⟩) ?_
    · show ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (C c))) = _
      rw [hτ, rename_C]
      exact (IntNumPoint.dehom P' i').commutes c
    revert z
    show (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ _
    unfold homFracDegZero
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    rw [div_eq_dehom_div _ _ hi0 hf hg, map_div₀, key2, key2]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord f), rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord g), rfl⟩)
  have hEH : (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤
      homFracDegZero P' := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := hEq z hz
    exact div_mem (hρH _) (hρH _)
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg relDeg
  exact finrank_eq_relfinrank ρ.toRingHom hρinj _ _ hEH
    (fun a b h => Ideal.quotientMap_injective (hρinj h)) hτE hρH hEq hHq

end FnDegRelDeg

end

end GroundTheory.Heights₂.Heights.Targets
