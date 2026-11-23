import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.exists_finset_span_of_integral_multiples :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module ℚ V] (n : ℕ) (kp : V ≃+ (Fin n → F)), ∃ s : Finset V, Submodule.span ℚ (s : Set V) = ⊤ ∧ ∀ (x : V) (N : ℕ) (c : Fin n → 𝓞 F), (∀ i, (c i : F) = (N : F) * kp x i) → N • x ∈ AddSubgroup.closure (s : Set V) := by
  intro F V _ _ _ _ n kp
  classical
  let ib := NumberField.integralBasis F
  let b := NumberField.RingOfIntegers.basis F
  let g : Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 F) → V :=
    fun ij => kp.symm (Pi.single ij.1 (ib ij.2))
  have hg : ∀ i j, g (i, j) ∈ ((Finset.univ.image g : Finset V) : Set V) := fun i j =>
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro v -
    have hsum : v = ∑ i, kp.symm (Pi.single i (kp v i)) := by
      rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    let Φ : F →+ V := kp.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin n => F) i)
    have hΦa : ∀ y, kp.symm (Pi.single i y) = Φ y := fun y => rfl
    rw [hΦa, ← ib.sum_repr (kp v i), map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_rat_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hg i j))
  · intro x N c hc
    have hx : N • x = kp.symm (fun i => (c i : F)) := by
      apply kp.injective
      rw [AddEquiv.apply_symm_apply, map_nsmul]
      funext i
      rw [Pi.smul_apply, hc i, nsmul_eq_mul]
    rw [hx, ← Finset.univ_sum_single (fun i => (c i : F)), map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    beta_reduce
    let Φ : F →+ V := kp.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin n => F) i)
    have hΦa : ∀ y, kp.symm (Pi.single i y) = Φ y := fun y => rfl
    have hci : ((c i : 𝓞 F) : F) = ∑ j, (b.repr (c i) j) • ib j := by
      calc ((c i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ j, b.repr (c i) j • b j) := by
            rw [b.sum_repr]
        _ = ∑ j, (b.repr (c i) j) • ib j := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_zsmul, NumberField.integralBasis_apply]
    rw [hΦa, hci, map_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hg i j)) _
