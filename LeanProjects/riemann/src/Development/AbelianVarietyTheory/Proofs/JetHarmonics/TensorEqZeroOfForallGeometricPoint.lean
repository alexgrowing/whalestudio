import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem exists_algHom_ker_eq_of_isMaximal (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb
  refine ⟨(e.symm : (B ⧸ m) →ₐ[F] F).comp (Ideal.Quotient.mkₐ F m), fun b h => ?_⟩
  have h' : e.symm (Ideal.Quotient.mk m b) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

theorem tensor_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by
  intro O F _ _ _ _ hinj A _ _ _ _ _ M _ _ _ t ht
  classical
  haveI : IsArtinianRing (TensorProduct O F A) := IsArtinianRing.of_finite F _
  have hpt : ∀ m : MaximalSpectrum (TensorProduct O F A),
      ∃ ψ : TensorProduct O F A →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m.asIdeal := fun m =>
    haveI := m.isMaximal
    exists_algHom_ker_eq_of_isMaximal F _ m.asIdeal
  choose ψ hψ using hpt
  let φ : MaximalSpectrum (TensorProduct O F A) → (A →ₐ[O] F) := fun m =>
    ((ψ m).restrictScalars O).comp Algebra.TensorProduct.includeRight
  let L : A →ₗ[O] (MaximalSpectrum (TensorProduct O F A) → F) :=
    LinearMap.pi fun m => (φ m).toLinearMap
  have hR : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O F A) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hR
    rw [map_zero]
    have hmem : (Algebra.TensorProduct.includeRight a : TensorProduct O F A) ∈
        Ideal.jacobson (⊥ : Ideal (TensorProduct O F A)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hψ ⟨J, hJ⟩ _ (congrFun ha ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := TensorProduct O F A)
    have h2 := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsNilpotent.eq_zero ⟨n, by simpa using h2⟩
  have hLM : Function.Injective (L.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  haveI : Fintype (MaximalSpectrum (TensorProduct O F A)) := Fintype.ofFinite _
  apply hLM
  rw [map_zero]
  apply (TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)).injective
  rw [map_zero]
  funext m
  have key : ∀ s : TensorProduct O A M,
      TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)
        (L.rTensor M s) m
      = TensorProduct.map (φ m).toLinearMap (LinearMap.id : M →ₗ[O] M) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [L, TensorProduct.piLeft]
    | add s s' h h' => rw [map_add, map_add, Pi.add_apply, h, h', map_add]
  rw [key, ht]
  rfl

end GlobalTheory
