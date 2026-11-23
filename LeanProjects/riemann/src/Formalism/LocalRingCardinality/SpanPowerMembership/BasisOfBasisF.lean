import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open scoped TensorProduct nonZeroDivisors

section Kap

variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]

theorem isFrac_tensor (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A) := inferInstance
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  · intro r hr
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := A) (I := Ideal.span {r}) hr0
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)
    have hu : IsUnit (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B d)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) _
        ⟨_, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0, rfl⟩⟩
    rw [hs, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu

def kap (hinj : Function.Injective (algebraMap A B)) : (B ⊗[A] FractionRing A) ≃ₐ[B] FractionRing B :=
  haveI := isFrac_tensor A B hinj
  IsLocalization.algEquiv B⁰ _ _

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def vecE (hinj : Function.Injective (algebraMap A B)) :
    (ι → FractionRing B) ≃ₗ[B] B ⊗[A] (ι → FractionRing A) :=
  (LinearEquiv.piCongrRight fun _ : ι => (kap A B hinj).symm.toLinearEquiv) ≪≫ₗ
    (TensorProduct.piRight A B B (fun _ : ι => FractionRing A)).symm

theorem vecE_single (hinj : Function.Injective (algebraMap A B)) (a : ι) :
    vecE A B ι hinj (Pi.single a 1) = (1 : B) ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) := by
  unfold vecE
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  funext j
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show (kap A B hinj).symm ((Pi.single a 1 : ι → FractionRing B) j) = _
  by_cases h : j = a
  · subst h
    rw [Pi.single_eq_same, map_one]
    show (1 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single j 1 : ι → FractionRing A) j
    rw [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne h, map_zero]
    show (0 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) j
    rw [Pi.single_eq_of_ne h, TensorProduct.tmul_zero]

theorem single_li (hB : Function.Injective (algebraMap B (FractionRing B))) :
    LinearIndependent B (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) := by
  have h := (Pi.basisFun (FractionRing B) ι).linearIndependent
  have h2 := h.restrict_scalars (R := B) (by
    intro x y hxy
    simpa [Algebra.smul_def] using hB (by simpa [Algebra.smul_def] using hxy))
  have e : (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) = ⇑(Pi.basisFun (FractionRing B) ι) :=
    funext fun a => (Pi.basisFun_apply _ _ a).symm
  rw [e]; exact h2

end Kap

theorem basis_of_basisF {K F W M ι κ : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module F M] [Fintype ι] [Fintype κ] (σ : K →+* F) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent F (fun i => e (b i)) ∧ Submodule.span F (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent F (fun i => e (b' i)) ∧ Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι F M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank F M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm

end Formalism.BasicNotions.Examples₂.NZ
