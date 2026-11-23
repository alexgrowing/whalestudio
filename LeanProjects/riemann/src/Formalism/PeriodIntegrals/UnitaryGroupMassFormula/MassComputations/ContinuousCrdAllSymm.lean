import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.AlgebraMapMemOv

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

def crdAll : (Fin n → Af F ⊗[F] E) ≃ₗ[Af F] (Fin n → Fin (Module.finrank F E) → Af F) :=
  LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun

theorem continuous_crdAll : Continuous (crdAll (F := F) (E := E) (n := n)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).toLinearMap
  exact h

theorem continuous_crdAll_symm : Continuous (crdAll (F := F) (E := E) (n := n)).symm := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).symm.toLinearMap
  exact h

theorem ratV_single (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e) = Pi.single i ((1 : Fv F v) ⊗ₜ[F] e) := by
  funext j
  unfold ratV
  rcases eq_or_ne j i with rfl | h
  · simp [inclR]
  · simp [h, inclR]

theorem single_mem_Bint (i : Fin n) (k : Fin (Module.finrank F E)) :
    (Pi.single i (Module.finBasis F E k) : Fin n → E) ∈ Bint (F := F) n := by
  unfold Bint
  rw [Set.mem_setOf_eq]
  intro i' k'
  rcases eq_or_ne i' i with rfl | h
  · rw [Pi.single_eq_same, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Pi.single_eq_of_ne h, map_zero, Finsupp.zero_apply]
    exact isIntegral_zero

theorem mem_latHat_Bint_iff (x : Fin n → Af F ⊗[F] E) :
    x ∈ latHat (F := F) (Bint (F := F) (E := E) n) ↔ ∀ i k, crd (Af F) (x i) k ∈ Ohat F := by
  constructor
  · intro hx i k v
    have h := crd_mem_of_latLoc v (hx v) i k
    simp only [pv, crd_tens] at h
    exact h
  · intro hx v
    set Btv := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    have hc : ∀ i k, crd (Fv F v) (pv v x i) k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [pv, crd_tens]
      exact hx i k v
    rw [← Finset.univ_sum_single (pv v x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e1 : pv v x i = ∑ k, crd (Fv F v) (pv v x i) k • Btv k := (Btv.sum_equivFun (pv v x i)).symm
    have e2 : (Pi.single i (pv v x i) : Fin n → Fv F v ⊗[F] E) =
        ∑ k, crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := by
      conv_lhs => rw [e1]
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [e2]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hm : (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) ∈ latLoc (E := E) v (Bint (F := F) n) := by
      refine Submodule.subset_span ⟨Pi.single i (Module.finBasis F E k), single_mem_Bint i k, ?_⟩
      rw [ratV_single, Algebra.TensorProduct.basis_apply]
    have e3 : crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) =
        (⟨_, hc i k⟩ : v.adicCompletionIntegers F) • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := rfl
    rw [e3]
    exact Submodule.smul_mem _ _ hm

theorem latHat_Bint_eq : latHat (F := F) (Bint (F := F) (E := E) n) =
    (crdAll (F := F) (E := E) (n := n)) ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => Ohat F) := by
  ext x
  rw [mem_latHat_Bint_iff]
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  rfl

theorem isOpen_latHat_Bint : IsOpen (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ohat F).preimage continuous_crdAll

theorem isCompact_latHat_Bint : IsCompact (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq, ← LinearEquiv.image_symm_eq_preimage]
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Ohat F).image continuous_crdAll_symm

theorem mem_std_iff (μ : Fin n → E) :
    μ ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (μ i) := by
  unfold stdSub
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Algebra.linearMap_apply]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨μ i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem exists_bint_to_std : ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ Bint (F := F) (E := E) n,
    N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set b := Module.finBasis F E
  obtain ⟨N, hN0, hN⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  refine ⟨N, hN0, fun μ hμ => (mem_std_iff _).2 fun i => ?_⟩
  have hb : ∀ k, IsIntegral ℤ (N • b k) := fun k => hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have e : (N • μ) i = ∑ k, algebraMap F E (b.repr (μ i) k) * (N • b k) := by
    rw [Pi.smul_apply]
    conv_lhs => rw [← b.sum_repr (μ i)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, Algebra.smul_def]
  rw [e]
  exact IsIntegral.sum _ fun k _ => ((hμ i k).algebraMap).mul (hb k)

theorem exists_std_to_bint : ∃ M : ℤ, M ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)),
    M • μ ∈ Bint (F := F) (E := E) n := by
  classical
  set b := Module.finBasis F E
  set β := RingOfIntegers.basis E
  obtain ⟨M, hM0, hM⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Module.finrank F E) =>
      b.repr (algebraMap (𝓞 E) E (β p.1)) p.2)
  refine ⟨M, hM0, fun μ hμ i k => ?_⟩
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))
  rw [Algebra.linearMap_apply] at ha
  have e : b.repr ((M • μ) i) k =
      ∑ j, (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [Pi.smul_apply, ← ha]
    conv_lhs => rw [← β.sum_repr a]
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  rw [e]
  refine IsIntegral.sum _ fun j _ => ?_
  have h := hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, k)))
  have h2 : (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) =
      ((β.repr a j : ℤ) : F) * (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [zsmul_eq_mul]
  rw [h2]
  have hc : IsIntegral ℤ ((β.repr a j : ℤ) : F) := by
    rw [← eq_intCast (algebraMap ℤ F)]; exact isIntegral_algebraMap
  exact hc.mul h

end Hat

theorem stdHatOpen_holds : StdHatOpen := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_bint_to_std (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) := {x | (N : F)⁻¹ • x ∈ latHat (F := F) (Bint (F := F) (E := E) n)}
  have hWo : IsOpen W := (isOpen_latHat_Bint (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [smul_zero]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem stdHatCompact_holds : StdHatCompact := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_std_to_bint (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  set L : Submodule (𝓞 E) (Fin n → E) := stdSub
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L span_std))).preimage (continuous_pv v)
  refine ((isCompact_latHat_Bint (F := F) (E := E) (n := n)).image
    (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

theorem kCompactOpen_holds : KCompactOpen :=
  kCompactOpen_of_std @KCptW.stdHatOpen_holds @KCptW.stdHatCompact_holds

end MassDataMassesW
