import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe

open IsLocalRing TensorProduct

namespace GlobalTheory.QuotientBaseChange

open MvPowerSeries

open IsLocalRing TensorProduct in
open MvPowerSeries in
private theorem monomial_one_mem_span_X_pow_degree {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    MvPowerSeries.monomial α (1 : R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ (Finsupp.degree α) := by
  induction α using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [← one_mul (1 : R), ← MvPowerSeries.monomial_mul_monomial, map_add, Finsupp.degree_single,
      pow_add, ← MvPowerSeries.X_pow_eq]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self a)) b) ih

open IsLocalRing TensorProduct in
open MvPowerSeries in

theorem _root_.GlobalTheory.QuotientBaseChange.nonempty_tensor_quotient_equiv : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal T), I.FG → IsAdicComplete (I.map (algebraMap T O)) O → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ T) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : T →+* MvPowerSeries σ T) I → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → Nonempty ((O ⊗[T] (MvPowerSeries σ T ⧸ Ideal.span (Set.range f))) ≃ₐ[O] (MvPowerSeries σ O ⧸ Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j)))) := by
  intro T O _ _ _ I hI hO σ ι hσ hι f M hM hfree hfin
  classical
  haveI := hfree
  haveI := hfin
  haveI := hO
  let J : Ideal O := I.map (algebraMap T O)
  let A := MvPowerSeries σ T ⧸ Ideal.span (Set.range f)
  let f' : ι → MvPowerSeries σ O := fun j => MvPowerSeries.map (algebraMap T O) (f j)
  let Q := MvPowerSeries σ O ⧸ Ideal.span (Set.range f')
  let S := O ⊗[T] A
  let μ : MvPowerSeries σ T →ₐ[T] MvPowerSeries σ O := MvPowerSeries.mapAlgHom (Algebra.ofId T O)
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker ((Ideal.Quotient.mkₐ T (Ideal.span (Set.range f'))).comp μ) :=
    Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact (RingHom.mem_ker).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)))
  let g : A →ₐ[T] Q := Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ T _).comp μ) (fun a ha => hker ha)
  let φ : S →ₐ[O] Q := Algebra.TensorProduct.lift (Algebra.ofId O Q) g (fun _ _ => Commute.all _ _)
  have hφ1 : ∀ p : MvPowerSeries σ T,
      φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (μ p) := fun p => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  let b := Algebra.TensorProduct.basis O (Module.Free.chooseBasis T A)
  haveI h1 : IsAdicComplete J S := _root_.GlobalTheory.FlatComplete.isAdicComplete_of_finite_basis b J
  let K : Ideal S := J.map (algebraMap O S)
  haveI h2 : IsAdicComplete K S := (IsAdicComplete.map_algebraMap_iff J S).mpr h1
  let h : MvPowerSeries σ T →ₐ[T] S :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ T (Ideal.span (Set.range f)))
  let hR : MvPowerSeries σ T →+* S := h
  have hf0 : ∀ j, h (f j) = 0 := fun j => by
    show Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (f j)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), map_zero]
  let L : Ideal S := Ideal.map hR (Ideal.span (Set.range MvPowerSeries.X))
  have hLK : L ^ M ≤ K := by
    rw [← Ideal.map_pow]
    refine (Ideal.map_mono hM).trans ?_
    rw [Ideal.map_sup]
    refine sup_le ?_ ?_
    · rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      show h (f j) ∈ K
      rw [hf0 j]
      exact K.zero_mem
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have e : (MvPowerSeries.C a : MvPowerSeries σ T) = algebraMap T _ a := by
        simp [MvPowerSeries.algebraMap_apply]
      show h (MvPowerSeries.C a) ∈ K
      rw [e, h.commutes, IsScalarTower.algebraMap_apply T O S]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  let J' : Ideal S := K ⊔ L
  haveI : IsAdicComplete J' S :=
    _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le S K J' 1 (1 + M) (by rw [pow_one]; exact le_sup_left)
      (Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le (pow_one K).le hLK)) h2
  let x : σ → S := fun i => h (MvPowerSeries.X i)
  have hx : ∀ i, x i ∈ J' := fun i =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
  let ψ0 : MvPowerSeries σ O →ₐ[O] S := _root_.GlobalTheory.mvEvalAdic O J' x hx
  have hX : ∀ i, ((ψ0.restrictScalars T).comp μ) (MvPowerSeries.X i) = x i := fun i => by
    show ψ0 (MvPowerSeries.map (algebraMap T O) (MvPowerSeries.X i)) = x i
    rw [MvPowerSeries.map_X]
    exact _root_.GlobalTheory.mvEvalAdic_X J' x hx i
  have hcomp : (ψ0.restrictScalars T).comp μ = h :=
    _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff J' (fun i => (hX i).symm ▸ hx i) hX
  have hψ0 : ∀ j, ψ0 (f' j) = 0 := fun j => by
    calc ψ0 (f' j) = ((ψ0.restrictScalars T).comp μ) (f j) := rfl
      _ = h (f j) := by rw [hcomp]
      _ = 0 := hf0 j
  have hker' : Ideal.span (Set.range f') ≤ RingHom.ker ψ0 :=
    Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact (RingHom.mem_ker).mpr (hψ0 j))
  let ψ : Q →ₐ[O] S := Ideal.Quotient.liftₐ _ ψ0 (fun a ha => hker' ha)
  have hψφ : ψ.comp φ = AlgHom.id O S := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.ext
      intro q
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      show ψ (φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ p)) = (1 : O) ⊗ₜ Ideal.Quotient.mk _ p
      rw [hφ1]
      exact DFunLike.congr_fun hcomp p
  have hCmap : (MvPowerSeries.map (algebraMap T O)).comp (MvPowerSeries.C : T →+* MvPowerSeries σ T) =
      (MvPowerSeries.C : O →+* MvPowerSeries σ O).comp (algebraMap T O) :=
    RingHom.ext fun a => by simp
  have hmono : ∀ α : σ →₀ ℕ, Finsupp.degree α = M →
      MvPowerSeries.monomial α (1 : O) ∈ Ideal.span (Set.range f') ⊔ Ideal.map MvPowerSeries.C J := by
    intro α hα
    have hT := hM (hα ▸ monomial_one_mem_span_X_pow_degree (R := T) α)
    have hm := Ideal.mem_map_of_mem (MvPowerSeries.map (algebraMap T O)) hT
    rw [MvPowerSeries.map_monomial, map_one, Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
      Ideal.map_map, hCmap, ← Ideal.map_map] at hm
    exact hm
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g0, rfl⟩ := Ideal.Quotient.mk_surjective q
    letI := Fintype.ofFinite ι
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.CompleteBaseChange.exists_polynomial_sub_mem (hI.map (algebraMap T O)) f' M hmono g0
    refine ⟨MvPolynomial.aeval x p, ?_⟩
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hφx : (fun i => φ (x i)) = fun i => Ideal.Quotient.mkₐ O (Ideal.span (Set.range f')) (MvPowerSeries.X i) := by
      funext i
      show φ ((1 : O) ⊗ₜ Ideal.Quotient.mk _ (MvPowerSeries.X i)) = _
      rw [hφ1]
      show Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap T O) (MvPowerSeries.X i)) = _
      rw [MvPowerSeries.map_X]
      rfl
    rw [hφx, ← _root_.GlobalTheory.algHom_coe_mvPolynomial]
    exact (Ideal.Quotient.eq.mpr hp).symm
  have hinj : Function.Injective φ :=
    Function.LeftInverse.injective (g := ψ) (fun s => DFunLike.congr_fun hψφ s)
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end GlobalTheory.QuotientBaseChange
