import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularSequence
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

def quotSMulTopQuotIdealSMulTopEquiv {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (I : Ideal B) (y : B) :
    QuotSMulTop y (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B]
      (QuotSMulTop y M ⧸ (I • ⊤ : Submodule B (QuotSMulTop y M))) :=
  (Submodule.quotEquivOfEq ((y • (⊤ : Submodule B M)).map (I • (⊤ : Submodule B M)).mkQ) (y • ⊤)
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).symm ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (I • ⊤) (y • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (I • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])

theorem FlatLocalRegularElement.iterate (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by
  induction ys generalizing M with
  | nil =>
    refine ⟨IsWeaklyRegular.nil B M, ?_⟩
    have e : (M ⧸ (Ideal.ofList ([] : List B) • (⊤ : Submodule B M))) ≃ₗ[B] M :=
      Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  | cons y ys ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hyM, hflat'⟩ := h A B hA hB hl M hfin hflat y (hys y List.mem_cons_self) hreg.1
    have hfin' : Module.Finite B (QuotSMulTop y M) := inferInstance
    obtain ⟨h1, h2⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (QuotSMulTop y M) hfin' hflat'
      (((quotSMulTopQuotIdealSMulTopEquiv _ y).isWeaklyRegular_congr ys).mp hreg.2)
    refine ⟨(isWeaklyRegular_cons_iff M y ys).mpr ⟨hyM, h1⟩, ?_⟩
    have : Module.Flat A (QuotSMulTop y M ⧸ (Ideal.ofList ys • (⊤ : Submodule B (QuotSMulTop y M)))) := h2
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ys).restrictScalars A)

theorem FlatLocalRegularSequence.proof (h : FlatLocalRegularElement.Statement) :
    FlatLocalRegularSequence.Statement := by
  intro A B _ _ _ _ _ hA hB hl hflat rs ys hrs hreg hys hfib
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  have hfib' : IsWeaklyRegular (B ⧸ (I • ⊤ : Submodule B B)) ys := by
    have e : (B ⧸ I) ≃ₗ[B] (B ⧸ (I • ⊤ : Submodule B B)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])
    rw [← Ideal.Quotient.algebraMap_eq, isWeaklyRegular_map_algebraMap_iff] at hfib
    exact (e.isWeaklyRegular_congr ys).mp hfib
  obtain ⟨hysB, hflatQ⟩ :=
    FlatLocalRegularElement.iterate h hA hB hl ys hys B inferInstance hflat hfib'
  have hrsN : IsWeaklyRegular (B ⧸ (Ideal.ofList ys • (⊤ : Submodule B B))) rs :=
    ((TensorProduct.lid A _).isWeaklyRegular_congr rs).mp (hreg.isWeaklyRegular_rTensor)
  have happ : IsWeaklyRegular B (ys ++ rs.map (algebraMap A B)) :=
    (isWeaklyRegular_append_iff B ys _).mpr
      ⟨hysB, (isWeaklyRegular_map_algebraMap_iff B _ rs).mpr hrsN⟩
  have : IsNoetherian B B := hB
  refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happ List.perm_append_comm ?_
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hys r hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal a).mp (hrs a ha) (isUnit_of_map_unit _ _ hu)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
