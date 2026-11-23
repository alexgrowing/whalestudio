import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Mathlib.Algebra.Module.Lattice
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_stable_lattice {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A)
    (hd : d ≠ 0) (h : ∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) :
    ∃ L : Submodule A (Fin m → F), Submodule.IsLattice F L ∧
      ∀ g, ∀ x ∈ L, (r g : Matrix (Fin m) (Fin m) F) *ᵥ x ∈ L := by
  classical
  let S : Set (Fin m → F) :=
    Set.range fun p : G × Fin m => (r p.1 : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single p.2 1)
  have hd' : algebraMap A F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
  refine ⟨Submodule.span A S, ⟨?_, ?_⟩, ?_⟩
  · let N : Submodule A (Fin m → F) :=
      Submodule.span A (Set.range fun i : Fin m => (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F))
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, j⟩, rfl⟩
    choose a ha using h g
    have e : (r g : Matrix (Fin m) (Fin m) F) *ᵥ (Pi.single j 1) =
        ∑ i, a i j • (Pi.single i (algebraMap A F d)⁻¹ : Fin m → F) := by
      funext k
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Algebra.smul_def, ← ha]
      field_simp
    simp only [SetLike.mem_coe]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff, ← (Pi.basisFun F (Fin m)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by
      simp only [map_one, Units.val_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by
        simp only [map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.V.Pa.Det.latInt :
    ∀ {A F G : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Group G] {m : ℕ} (r : G →* GL (Fin m) F) (d : A), d ≠ 0 → (∀ g i j, ∃ a : A, algebraMap A F d * r g i j = algebraMap A F a) → ∃ (Q : GL (Fin m) F) (r₀ : G →* GL (Fin m) A), ∀ g, r g * Q = Q * pushRep (algebraMap A F) r₀ g := by
  intro A F G _ _ _ _ _ _ _ m r d hd h
  classical
  obtain ⟨L, hL, hst⟩ := exists_stable_lattice r d hd h
  have hr : Module.finrank A L = m := by
    simpa using Submodule.IsLattice.finrank_of_pi F L
  let bL : Module.Basis (Fin m) A L := Module.finBasisOfFinrankEq A L hr
  let b : Module.Basis (Fin m) F (Fin m → F) := bL.extendOfIsLattice F
  let Q₀ : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix b
  have hQ : IsUnit Q₀ := by
    letI := (Pi.basisFun F (Fin m)).invertibleToMatrix b
    exact isUnit_of_invertible _
  have hQa : ∀ i j, Q₀ i j = (bL j : Fin m → F) i := fun i j => by
    simp [Q₀, b, Module.Basis.toMatrix_apply]
  let M : G → Matrix (Fin m) (Fin m) A := fun g k j => bL.repr ⟨_, hst g _ (bL j).2⟩ k
  have hM : ∀ g, (r g : Matrix (Fin m) (Fin m) F) * Q₀ = Q₀ * (M g).map (algebraMap A F) := by
    intro g
    ext i j
    have e := congrArg (fun x : L => (x : Fin m → F) i) (bL.sum_repr ⟨_, hst g _ (bL j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Algebra.smul_def] at e
    simp only [Matrix.mul_apply, hQa, Matrix.map_apply]
    refine Eq.trans e.symm ?_
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have inj : ∀ X Y : Matrix (Fin m) (Fin m) A,
      Q₀ * X.map (algebraMap A F) = Q₀ * Y.map (algebraMap A F) → X = Y := fun X Y hXY =>
    Matrix.map_injective (IsFractionRing.injective A F) (hQ.mul_left_cancel hXY)
  let M' : G →* Matrix (Fin m) (Fin m) A :=
    { toFun := M
      map_one' := inj _ _ (by rw [← hM]; simp)
      map_mul' := fun g g' => inj _ _ (by
        rw [← hM, Matrix.map_mul, ← mul_assoc, ← hM, mul_assoc, ← hM, map_mul, Units.val_mul,
          mul_assoc]) }
  refine ⟨hQ.unit, M'.toHomUnits, fun g => Units.ext ?_⟩
  exact hM g
