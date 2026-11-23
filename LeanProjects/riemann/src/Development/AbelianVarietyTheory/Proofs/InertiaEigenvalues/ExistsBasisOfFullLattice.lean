import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

theorem exists_basis_of_fullLattice {R F M V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V]
    (f : M →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (m : M), f (c • m) = algebraMap R F c • f m)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ m, algebraMap R F c • v = f m)
    (b0 : Module.Basis ι R M) :
    ∃ b : Module.Basis ι F V, (∀ j, b j = f (b0 j)) ∧
      ∀ m i, b.repr (f m) i = algebraMap R F (b0.repr m i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) g :=
    { map_units := fun s => by
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        exact MulAction.bijective (β := V) (Units.mk0 _ h0 : Fˣ)
      surj := fun v => by
        obtain ⟨c, hc, m, hm⟩ := hfull v
        exact ⟨(m, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b0.ofIsLocalizedModule F (nonZeroDivisors R) g,
    fun j => b0.ofIsLocalizedModule_apply F _ g j,
    fun m i => b0.ofIsLocalizedModule_repr_apply F _ g m i⟩

theorem exists_basis_of_locLat {R G F LL O ι : Type} [CommRing R] [IsDomain R] [Group G]
    [TopologicalSpace G] [Field F] [Field LL] [Algebra F LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] [Algebra R F] [IsFractionRing R F] [Algebra R O] [Fintype ι]
    (T : LocLat G F LL O)
    (hc : ∀ c : R, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hden : ∀ a : LL, ∃ c : R, c ≠ 0 ∧
      ∃ o : O, algebraMap O LL o = algebraMap F LL (algebraMap R F c) * a) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b0 : Module.Basis ι R ↥T.L.T, ∃ b : Module.Basis ι F T.V, (∀ j, b j = (b0 j : T.V)) ∧
      (∀ (m : ↥T.L.T) i, b.repr (m : T.V) i = algebraMap R F (b0.repr m i)) ∧
      (∀ (a : O) j i, b.repr (algebraMap O LL a • b j) i =
        algebraMap R F (b0.repr ⟨_, T.L.T.smul_mem a (b0 j).2⟩ i)) ∧
      ∀ v : T.V, (∀ i, ∃ c : R, b.repr v i = algebraMap R F c) → v ∈ T.L.T := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b0
  have key : ∀ (c : R) (w : T.V), algebraMap R F c • w = algebraMap R O c • w := by
    intro c w
    rw [← algebraMap_smul LL (algebraMap R F c) w, ← algebraMap_smul LL (algebraMap R O c) w, hc]
  have hfull : ∀ v : T.V, ∃ c : R, c ≠ 0 ∧ algebraMap R F c • v ∈ T.L.T := by
    intro v
    have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', hy⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, map_mul, mul_smul, key c']
        exact T.L.T.smul_mem _ hx
      · rw [map_mul, mul_smul, key c]
        exact T.L.T.smul_mem _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', o, ho⟩ := hden a
      refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
      have := T.L.T.smul_mem o hx
      rw [← algebraMap_smul LL, ho, mul_smul, algebraMap_smul,
        smul_comm a (algebraMap R F c) x] at this
      rwa [map_mul, mul_smul]
  obtain ⟨b, hb, hr⟩ := exists_basis_of_fullLattice (R := R) (F := F)
    (T.L.T.subtype.toAddMonoidHom) Subtype.val_injective
    (fun c m => (key c m).symm)
    (fun v => by
      obtain ⟨c, hc, hv⟩ := hfull v
      exact ⟨c, hc, ⟨_, hv⟩, rfl⟩) b0
  refine ⟨b, hb, hr, fun a j i => ?_, fun v hv => ?_⟩
  · rw [← hr, hb, algebraMap_smul]
    rfl
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hv i
    rw [hc, key, hb]
    exact T.L.T.smul_mem _ (b0 i).2

theorem exists_ratBasis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ b : Module.Basis (Fin d) ℚ_[l] T.V, (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) ∧ (∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr ((a : ↥LL.1) • b j) i)) ∧ ∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  intro l _ K LL T d M A h
  letI := zlMod LL T
  obtain ⟨b0, hM, hA⟩ := h
  obtain ⟨b, hb, hr, ha, hv⟩ := exists_basis_of_locLat (R := ℤ_[l]) T (fun _ => rfl) (fun a => by
    have ha : IsAlgebraic ℤ_[l] a :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
    exact ⟨c, hc, ⟨c • a, hint⟩, Algebra.smul_def c a⟩) b0
  refine ⟨b, fun g i j => ?_, fun a i j => ?_, fun v => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · have e : T.ρ g (b j) = ((actTZ LL T g (b0 j) : ↥T.L.T) : T.V) := congrArg (T.ρ g) (hb j)
    rw [e]
    exact (hM g i j).trans
      (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (hr (actTZ LL T g (b0 j)) i).symm)
  · exact (hA a i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (ha a j i).symm)
  · exact (congrArg norm (hr ⟨v, h⟩ i)).trans_le (b0.repr ⟨v, h⟩ i).2
  · exact hv v fun i => ⟨⟨_, h i⟩, rfl⟩

end GlobalTheory.Cyc
