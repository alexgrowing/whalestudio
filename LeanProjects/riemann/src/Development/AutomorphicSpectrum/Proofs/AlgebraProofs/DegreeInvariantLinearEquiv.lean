import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

def tr (e : V ≃ₗ[K] V') (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    Module.Basis (Fin (Module.finrank K V')) K V' :=
  (b.map e).reindex (finCongr e.finrank_eq)

theorem isLatOf_tr (e : V ≃ₗ[K] V') {i : C.I} {b : Module.Basis (Fin (Module.finrank K V)) K V}
    {L : AddSubgroup V} {L' : AddSubgroup V'} (hb : IsLatOf C i b L)
    (h : ∀ x, x ∈ L ↔ e x ∈ L') : IsLatOf C i (tr e b) L' := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← h, hb]
  simp only [tr, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (finCongr e.finrank_eq q)⟩

theorem det_tr (e : V ≃ₗ[K] V') (a b : Module.Basis (Fin (Module.finrank K V)) K V) :
    (tr e a).det (tr e b) = a.det b := by
  unfold tr
  rw [Module.Basis.coe_reindex, Module.Basis.det_reindex, Module.Basis.det_map]
  congr 1
  funext q
  simp

theorem deg_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'),
    IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  intro K _ C V _ _ _ V' _ _ _ L L' e ⟨hl, b0, hb0⟩ h
  choose b hb using hl
  have hb' : ∀ i, IsLatOf C i (tr e (b i)) (L' i) := fun i => isLatOf_tr C e (hb i) (h i)
  refine ⟨⟨fun i => ⟨_, hb' i⟩, tr e b0,
    hb0.subset fun i hi hc => hi (isLatOf_tr C e hc (h i))⟩, ?_⟩
  rw [Inhab.deg_eq C _ hb', Inhab.deg_eq C _ hb]
  set c := (Module.finBasis K V').det (tr e (Module.finBasis K V)) with hc
  have hc0 : c ≠ 0 := ((Module.finBasis K V').isUnit_det _).ne_zero
  have hd0 : ∀ i, (Module.finBasis K V).det (b i) ≠ 0 := fun i =>
    ((Module.finBasis K V).isUnit_det _).ne_zero
  have h1 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V').det (tr e (b i)))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ (tr e (Module.finBasis K V)), det_tr, ← hc, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hc0) ((Valuation.ne_zero_iff _).2 (hd0 i)),
      mul_add]
  simp only [h1]
  rw [finsum_add_distrib, C.prod c hc0, zero_add]
  · exact (C.fin c hc0).subset fun i hi h1 => hi (by simp [h1])
  · refine (hb0.union (C.fin _ ((Module.finBasis K V).isUnit_det b0).ne_zero)).subset
      fun i hi => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    apply hi
    show (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) = 0
    rw [← Module.Basis.det_mul_det _ b0, map_mul, hn.2, Inhab.v_det C hn.1 (hb i)]
    simp

end GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv
