import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module

section Lin

end Lin

section Period

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

section Mul

variable {R : Type} [CommRing R] [Algebra Qp R]

theorem mp_tmul (b c : R) (v : V) :
    mulPeriod (Qp := Qp) (LL := LL) (V := V) b (v ⊗ₜ c) = v ⊗ₜ (b * c) := by
  simp [mulPeriod]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
variable {R : Type} [CommRing R] [Algebra Qp R] in
theorem _root_.GlobalTheory.DeRhamCompare.comm_mp (b : R) (x : V ⊗[Qp] R) :
    TensorProduct.comm Qp V R (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) b x) =
      b • TensorProduct.comm Qp V R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem finite_of_finrank_eq [FiniteDimensional LL V] (S : Submodule LL (V ⊗[Qp] R)) {n : ℕ}
    (hn : 0 < n) (h : finrank LL S = n * finrank LL V) : FiniteDimensional LL S := by
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.1 h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos hn h0)

end Mul

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdR (x : V ⊗[Qp] BdR) :
    x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ ↔ ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x = x := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem mem_Dcris (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, sub_eq_zero]

theorem mem_DdRE (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR) : x ∈ DdRE PD ρ τ ↔
    x ∈ DdR PD ρ ∧ ∀ c : K, mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c x = τ c • x := by
  simp [DdRE, sub_eq_zero]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mulK_mem (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) x ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
  rw [_root_.GlobalTheory.DeRhamCompare.mem_DdR] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[Qp] BdR,
      _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V)
        (algebraMap K BdR c) y) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c)
        (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v r => simp [_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR, _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [key, hx g]

theorem mulK₀_mem (c : K₀) (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K₀ B c) x ∈ Dcris PD ρ := by
  rw [mem_Dcris] at hx ⊢
  intro g
  conv_rhs => rw [← hx g]
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mp_tmul, actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.finite_DdR [FiniteDimensional LL V] (h : _root_.Formalism.MainNotions.N.IsDR PD ρ) :
    FiniteDimensional LL (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := by
  have hK : FiniteDimensional Qp K := by cases PD; assumption
  unfold _root_.Formalism.MainNotions.N.IsDR at h
  by_cases hV : Module.finrank LL V = 0
  · have hsV : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hzero : ∀ z : V ⊗[Qp] BdR, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul v r => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    have hsub : Subsingleton (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :=
      ⟨fun x y => Subtype.ext (by rw [hzero x, hzero y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem finite_Dcris [FiniteDimensional LL V] (h : IsCrys PD ρ) :
    FiniteDimensional LL (Dcris PD ρ) := by
  have := PD.finK₀
  exact finite_of_finrank_eq _ finrank_pos h

theorem tmul_mem_FilV (v : V) {a : ℤ} {b : BdR} (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

theorem FilV_induction {a : ℤ} {p : V ⊗[Qp] BdR → Prop} (h0 : p 0)
    (ht : ∀ v, ∀ b ∈ PD.Fil a, p (v ⊗ₜ b)) (ha : ∀ x y, p x → p y → p (x + y))
    {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) : p x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul v b => simpa using ht v b b.2
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.FildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR
  refine inf_le_inf_left _ ?_
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    PD.Fil_anti a
  rintro x ⟨y, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

theorem isJumpV_of_multV_ne {τ : K →ₐ[Qp] LL} {a : ℤ} (h : multV PD ρ τ a ≠ 0) :
    IsJumpV PD ρ τ a := fun h' => h (by rw [multV, h', sub_self])

end Period

section Comparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def DdRK : Submodule K (BdR ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V BdR).symm y ∈ DdR PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V BdR).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul BdR, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK_mem PD ρ c x hy

def DcrisK : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V B).symm y ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V B).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul B, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK₀_mem PD ρ c x hy

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdRK (y : BdR ⊗[Qp] V) :
    y ∈ _root_.GlobalTheory.DeRhamCompare.DdRK PD ρ ↔ (TensorProduct.comm Qp V BdR).symm y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  Iff.rfl

theorem mem_DcrisK (y : B ⊗[Qp] V) :
    y ∈ DcrisK PD ρ ↔ (TensorProduct.comm Qp V B).symm y ∈ Dcris PD ρ := Iff.rfl

def toK (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) : DdRK PD ρ :=
  ⟨TensorProduct.comm Qp V BdR x, by rw [mem_DdRK, LinearEquiv.symm_apply_apply]; exact hx⟩

def mulβ : BdR →ₗ[K] DdRK PD ρ →ₗ[K] BdR ⊗[Qp] V :=
  (Algebra.lsmul K K (BdR ⊗[Qp] V) (A := BdR)).toLinearMap.compl₂ (DdRK PD ρ).subtype

theorem mulβ_apply (b : BdR) (y : DdRK PD ρ) : mulβ PD ρ b y = b • (y : BdR ⊗[Qp] V) := rfl

def InjPeriods : Prop :=
  ∀ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR),
    LinearIndependent K b → (∀ i, d i ∈ DdR PD ρ) →
    ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) = 0 → ∀ i, d i = 0

def InjVectors : Prop :=
  ∀ (m : ℕ) (x : Fin m → V ⊗[Qp] BdR), (∀ j, x j ∈ DdR PD ρ) →
    (∀ c : Fin m → K,
      ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (c j) (x j) = 0 → ∀ j, c j = 0) →
    ∀ b : Fin m → BdR,
      ∑ j, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b j) (x j) = 0 → ∀ j, b j = 0

theorem ιV_mp (c : B) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulPeriod (Qp := Qp) (LL := LL) (V := V) c x) =
      mulPeriod (Qp := Qp) (LL := LL) (V := V) (PD.ι c) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mp_tmul, ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

end Comparison

section Filtered

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def LatticeAt : Prop :=
  FilV PD (LL := LL) (V := V) 0 = ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil 0),
    (filDdR PD ρ a).map
      (mulPeriod (Qp := Qp) (LL := LL) (V := V) (((tdR PD ^ (-a) : BdRˣ) : BdR) * b))

def FilteredAt (n : ℤ) : Prop :=
  FilV PD (LL := LL) (V := V) n = ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil (n - a)),
    (filDdR PD ρ a).map (mulPeriod (Qp := Qp) (LL := LL) (V := V) b)

def co (φ : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ φ.rTensor BdR

@[simp] theorem co_tmul (φ : V →ₗ[Qp] Qp) (v : V) (b : BdR) : co φ (v ⊗ₜ b) = φ v • b := by
  simp [co]

end Filtered

end GlobalTheory.DeRhamCompare
