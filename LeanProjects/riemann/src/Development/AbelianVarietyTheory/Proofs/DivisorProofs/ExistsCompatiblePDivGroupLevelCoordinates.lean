import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers

set_option autoImplicit false

open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_aug_dUnit_eq {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] (w : Cot R A) :
    ∃ a : A, Coalgebra.counit (R := R) a = 0 ∧ dUnit R a = w := by
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective w
  exact ⟨x, x.2, AugCot.d_coe _ x⟩

theorem exists_aug_lift_dUnit_eq {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Bialgebra R A]
    [Bialgebra R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) (a : A)
    (ha : Coalgebra.counit (R := R) a = 0) (w : Cot R C) (hw : cotMap f w = dUnit R a) :
    ∃ c : C, Coalgebra.counit (R := R) c = 0 ∧ dUnit R c = w ∧ f c = a := by
  obtain ⟨y, hy, rfl⟩ := exists_aug_dUnit_eq w
  have h1 : dUnit R (f y - a) = 0 := by
    rw [dUnit, map_sub, sub_eq_zero]
    exact (cotMap_d f y).symm.trans hw
  have h2 : Bialgebra.counitAlgHom R A (f y - a) = 0 := by simp [hy, ha]
  rw [dUnit, AugCot.d_eq_zero_iff, h2, map_zero, sub_zero] at h1
  have h3 : f y - a ∈ Ideal.map (f : C →ₐ[R] A) (augIdeal R C ^ 2) := by
    rw [Ideal.map_pow]
    have := kerIdeal_of_surjective hf
    rw [kerIdeal] at this
    rw [this]
    exact h1
  obtain ⟨z, hz, hfz⟩ := (Ideal.mem_map_iff_of_surjective (f : C →ₐ[R] A) hf).1 h3
  have hz0 : Bialgebra.counitAlgHom R C z = 0 := Ideal.pow_le_self two_ne_zero hz
  have hz1 : Coalgebra.counit (R := R) z = 0 := hz0
  refine ⟨y - z, by rw [map_sub, hy, hz1, sub_zero], ?_, ?_⟩
  · rw [dUnit, map_sub, (AugCot.d_eq_zero_iff _ z).2 (by rw [hz0, map_zero, sub_zero]; exact hz), sub_zero]
  · have : f z = f y - a := hfz
    rw [map_sub, this, sub_sub_cancel]

theorem exists_compatible_dUnit_eq {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (w : G.omega) :
    ∃ x : ∀ n, G.A n, (∀ n, Coalgebra.counit (R := O) (x n) = 0) ∧ (∀ n, G.res n (x (n + 1)) = x n) ∧
      ∀ n, dUnit O (x n) = w.1 n := by
  obtain ⟨a, ha⟩ := exists_aug_dUnit_eq (w.1 0)
  have step : ∀ (n : ℕ) (a : {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 n}),
      ∃ c : {a : G.A (n + 1) // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 (n + 1)},
        G.res n c.1 = a.1 := fun n a => by
    obtain ⟨c, h1, h2, h3⟩ := exists_aug_lift_dUnit_eq (G.res_surjective n) a.1 a.2.1 (w.1 (n + 1))
      ((w.2 n).trans a.2.2.symm)
    exact ⟨⟨c, h1, h2⟩, h3⟩
  choose s hs using step
  let x : ∀ n, {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 n} :=
    fun n => Nat.rec ⟨a, ha⟩ s n
  exact ⟨fun n => (x n).1, fun n => (x n).2.1, fun n => hs n (x n), fun n => (x n).2.2⟩

theorem exists_compatible_coordinates (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O) :
    ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧
      (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit O (x n i)) = ⊤) ∧
      ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}),
        ∀ i j, l i (PDiv.dUnit O (x n j)) = if i = j then 1 else 0 := by
  have : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨h1, h2⟩ := omega_finite_projective p C v O hv G
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O G.omega
  choose x hx0 hx1 hx2 using fun i => exists_compatible_dUnit_eq G (b i)
  refine ⟨_, fun n i => x i n, fun n i => hx0 i n, fun n i => hx1 i n, fun n => ?_, fun n => ?_⟩
  · have : (fun i => dUnit O (x i n)) = G.omegaLevel n ∘ b := funext fun i => hx2 i n
    rw [this, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 (G.omegaLevel_surjective n)]
  · have hker : ∀ i, LinearMap.ker (G.omegaLevel n) ≤
        LinearMap.ker ((Ideal.span {(p : O) ^ n}).mkQ ∘ₗ b.coord i) := fun i w hw => by
      obtain ⟨u, rfl⟩ := (G.omega_val_eq_zero_iff n w).1 hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨fun i => ((LinearMap.ker (G.omegaLevel n)).liftQ _ (hker i)) ∘ₗ
      ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm.toLinearMap, fun i j => ?_⟩
    have h : ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm (dUnit O (x j n)) =
        Submodule.Quotient.mk (b j) := by
      rw [LinearEquiv.symm_apply_eq, hx2]
      rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply, b.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]

end GlobalTheory.PDiv
