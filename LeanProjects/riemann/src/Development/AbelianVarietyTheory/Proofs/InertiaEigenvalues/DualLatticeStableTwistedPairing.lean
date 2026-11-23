import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLat

variable {LL O V W : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W] [FiniteDimensional LL W]

theorem exists_dual (m : V →ₗ[LL] W →ₗ[LL] LL)
    (h3 : ∀ y : W, (∀ x : V, m x y = 0) → y = 0)
    (h4 : finrank LL V = finrank LL W)
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) :
    ∃ T' : Submodule O W, T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set W) = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a, m x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a, m x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O T
  let bV0 : Module.Free.ChooseBasisIndex O T → V := fun i => (b i : V)
  have hTspan : Submodule.span O (Set.range bV0) = T := by
    rw [show bV0 = T.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hliO : LinearIndependent O bV0 := b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL bV0 := (LinearIndependent.iff_fractionRing O LL).mp hliO
  have hspL : ⊤ ≤ Submodule.span LL (Set.range bV0) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hTspan] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  let bV := Basis.mk hliL hspL
  have hbV : ∀ i, bV i = bV0 i := fun i => Basis.mk_apply hliL hspL i
  let φ : W →ₗ[LL] Module.Dual LL V := m.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact h3 y (fun x => by simpa [φ] using LinearMap.congr_fun hy x)
  have hdim : finrank LL W = finrank LL (Module.Dual LL V) := by
    rw [Subspace.dual_finrank_eq, h4]
  let e : W ≃ₗ[LL] Module.Dual LL V := LinearMap.linearEquivOfInjective φ hφ hdim
  let f' := bV.dualBasis.map e.symm
  have key1 : ∀ x j, m x (f' j) = bV.repr x j := by
    intro x j
    have h : φ (f' j) = bV.dualBasis j := by
      show e (e.symm (bV.dualBasis j)) = bV.dualBasis j
      exact e.apply_symm_apply _
    calc m x (f' j) = φ (f' j) x := rfl
      _ = bV.dualBasis j x := by rw [h]
      _ = bV.repr x j := Basis.dualBasis_apply _ _ _
  have key2 : ∀ i y, m (bV i) y = f'.repr y i := by
    intro i y
    have : m (bV i) = f'.coord i := f'.ext (fun j => by
      rw [key1, Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
        Finsupp.single_apply]
      simp only [eq_comm])
    rw [this, Basis.coord_apply]
  haveI : IsTorsionFree O LL := inferInstance
  refine ⟨Submodule.span O (Set.range f'), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · exact Module.Free.of_basis (Basis.span ((LinearIndependent.iff_fractionRing O LL).mpr f'.linearIndependent))
  · rw [Submodule.span_span_of_tower, f'.span_eq]
  · intro y
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hy x hx
      rw [← hTspan] at hx
      have hle : Submodule.span O (Set.range bV0) ≤
          Submodule.comap ((m.flip y).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        obtain ⟨a, ha⟩ := hy i
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key2, hbV]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hx)
      exact ⟨a, ha.symm⟩
    · intro hy i
      obtain ⟨a, ha⟩ := hy (bV i) (by rw [hbV, ← hTspan]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← key2, ha]⟩
  · intro x
    have hTeq : T = Submodule.span O (Set.range bV) := by
      rw [show (bV : _ → V) = bV0 from funext hbV, hTspan]
    refine (SetLike.ext_iff.mp hTeq x).trans ?_
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hx y hy
      have hle : Submodule.span O (Set.range f') ≤
          Submodule.comap ((m x).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        obtain ⟨a, ha⟩ := hx j
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key1]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hy)
      exact ⟨a, ha.symm⟩
    · intro hx j
      obtain ⟨a, ha⟩ := hx (f' j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← key1, ha]⟩

end GlobalTheory.DualLat

namespace GlobalTheory.DualLat

theorem dualLattice_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m LA hD hc
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hO
  obtain ⟨h1, h2, h3, h4⟩ := hD
  obtain ⟨T', hfg, hfree, hspan, hmem1, hmem2⟩ := exists_dual (O := O) m h3 h4 LA.T LA.fg LA.free LA.span
  have hstab : ∀ g, ∀ y ∈ T', (A'.ρ g) y ∈ T' := by
    intro g y hy
    rw [hmem1] at hy ⊢
    intro x hx
    obtain ⟨c, hcg⟩ := hc g
    obtain ⟨a, ha⟩ := hy (A.ρ g⁻¹ x) (LA.stable g⁻¹ x hx)
    refine ⟨c * a, ?_⟩
    have hx' : x = A.ρ g (A.ρ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx', h1, ha, hcg, map_mul]
  let LA' : WeaklyAdmissibleFiltrations.Lattice (O := O) A'.ρ :=
    { T := T', stable := hstab, fg := hfg, free := hfree, span := hspan }
  refine ⟨LA', ⟨⟨h1, h2, h3, h4⟩, hmem1⟩, ⟨⟨?_, ?_, ?_, h4.symm⟩, ?_⟩⟩
  · intro g y x
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  · intro y hy
    exact h3 y (fun x => by simpa only [LinearMap.flip_apply] using hy x)
  · intro x hx
    exact h2 x (fun y => by simpa only [LinearMap.flip_apply] using hx y)
  · intro y
    simpa only [LinearMap.flip_apply] using hmem2 y

end GlobalTheory.DualLat
