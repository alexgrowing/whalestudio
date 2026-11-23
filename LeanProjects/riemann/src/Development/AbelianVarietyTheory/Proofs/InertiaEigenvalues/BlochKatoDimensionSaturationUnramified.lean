import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a :=
  antitone_int_of_succ_le PD.Fil_anti h

theorem filV_anti {a b : ℤ} (h : a ≤ b) :
    FilV PD (LL := LL) (V := V) b ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    refine ⟨v ⊗ₜ ⟨(c : BdR), fil_anti PD h c.2⟩, ?_⟩
    simp
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem exists_mem_filV (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, v ⊗ₜ ⟨c, ha⟩, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem exists_DdRE_le_filV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ a, DdRE PD ρ τ ≤ FilV PD (LL := LL) (V := V) a := by
  have key : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s _ ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := exists_mem_filV PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact filV_anti PD (min_le_right a b) hb
      · exact filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ : (DdRE PD ρ τ).FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨a, ha⟩ := key s
  exact ⟨a, hs ▸ Submodule.span_le.mpr ha⟩

theorem finsum_multV_neg (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) := by
  obtain ⟨a₀, ha₀⟩ := exists_DdRE_le_filV PD ρ τ
  have hF : ∀ b ≤ a₀, FildR PD ρ τ b = DdRE PD ρ τ := fun b hb =>
    inf_eq_left.mpr (ha₀.trans (filV_anti PD hb))
  set N : ℕ := (-a₀).toNat with hN
  have hNa : -(N : ℤ) ≤ a₀ := by have := Int.self_le_toNat (-a₀); omega
  set f : ℤ → ℤ := fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ) with hf
  have hg : ∀ a, multV PD ρ τ a = f a - f (a + 1) := fun a => rfl
  have hzero : ∀ a, a < -(N : ℤ) → multV PD ρ τ a = 0 := by
    intro a ha
    have h1 := hF a (by omega)
    have h2 := hF (a + 1) (by omega)
    rw [multV, h1, h2, sub_self]
  let e : ℕ ↪ ℤ := ⟨fun i => -((i : ℤ) + 1), fun i j h => by
    have : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega⟩
  have he : ∀ i, e i = -((i : ℤ) + 1) := fun _ => rfl
  have hsum : ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ a ∈ (Finset.range N).map e, multV PD ρ τ a := by
    apply finsum_mem_eq_sum_of_inter_support_eq (s := Set.Iio (0 : ℤ))
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_map, Finset.coe_range,
      Set.mem_image, Set.mem_Iio, Function.mem_support, he]
    constructor
    · rintro ⟨ha, hs⟩
      refine ⟨⟨(-a - 1).toNat, ?_, ?_⟩, hs⟩
      · by_contra h; exact hs (hzero a (by omega))
      · omega
    · rintro ⟨⟨i, hi, rfl⟩, hs⟩
      exact ⟨by omega, hs⟩
  rw [hsum, Finset.sum_map]
  have hT := Finset.sum_range_sub (fun i : ℕ => f (-(i : ℤ))) N
  have h2 : ∀ i ∈ Finset.range N, multV PD ρ τ (e i) = f (-((i + 1 : ℕ) : ℤ)) - f (-(i : ℤ)) := by
    intro i _
    rw [hg, he]
    congr 2 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h2, hT]
  simp only [Nat.cast_zero, neg_zero, hf]
  rw [hF (-(N : ℤ)) hNa]

end Gen
end GlobalTheory.FiltrationJumpMultiplicity

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Sat
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem coboundary_mem_blochKatoCocycles (ρ : Representation LL G V) (hc : ∀ x, Continuous fun g => ρ g x) (x : V) :
    cob ρ x ∈ finiteCocycles PD ρ := by
  have hcob : ∀ g, cob ρ x g = ρ g x - x := fun g => rfl
  refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : (cob ρ x : G → V) = fun g => ρ g x + (-x) := funext fun g => by rw [hcob, sub_eq_add_neg]
    rw [this]
    exact (hc x).add continuous_const
  · simp only [hcob, map_mul, Module.End.mul_apply, map_sub]
    abel
  · rw [hcob, sub_tmul]
    simp [actVB]

theorem mem_H1fT_of_smul (ρ : Representation LL G V) (L : Lattice (O := O) ρ)
    (hc : ∀ x, Continuous fun g => ρ g x) (κ : LatticeCohomology L) (a : O) (ha : algebraMap O LL a ≠ 0)
    (h : a • κ ∈ latticeFiniteCohomology PD L) : κ ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  obtain ⟨c', hc', hq⟩ := h
  rw [← Submodule.Quotient.mk_smul] at hq
  have hq' := (Submodule.Quotient.eq _).mp hq
  obtain ⟨x, -, hx⟩ := hq'
  have hx' : (c' : G → V) - a • (c : G → V) = cob ρ x := by
    have h3 : ((latticeCocycles L).subtype (c' - a • c) : G → V) = (c' : G → V) - a • (c : G → V) := by simp
    rw [← h3, ← hx]; rfl
  have h1 : a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have : a • (c : G → V) = (c' : G → V) - cob ρ x := by rw [← hx']; abel
    rw [this]
    exact (finiteCocycles PD ρ).sub_mem hc'.2 (coboundary_mem_blochKatoCocycles PD ρ hc x)
  have h2 : (c : G → V) ∈ finiteCocycles PD ρ := by
    have e : a • (c : G → V) = algebraMap O LL a • (c : G → V) := (algebraMap_smul LL a _).symm
    rw [e] at h1
    have := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h1
    rwa [inv_smul_smul₀ ha] at this
  exact ⟨c, ⟨c.2, h2⟩, rfl⟩

end Sat

theorem blochKato_dimension_saturation_unramified : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm19 D := by
  intro D l _ K LL hA
  haveI := K.2
  haveI := LL.2
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ _ _ _ _ _ _ _ ρ hc hcrys
    letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have hBK := GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL
      (GlobalTheory.H1fGeneratorBoundAlt.splits_of_good hA.2.2) V ρ hc hcrys
    rw [hBK, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    haveI := ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL V ρ).1 τ).1
    exact (finsum_multV_neg _ ρ τ).symm
  · intro V _ _ _ _ _ _ _ _ _ _ _ ρ L hc _ κ a ha h
    refine mem_H1fT_of_smul _ ρ L hc κ a ?_ h
    intro h0
    exact ha (Subtype.ext h0)
  · exact GlobalTheory.T.unramified_trivial_local l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.FiltrationJumpMultiplicity
