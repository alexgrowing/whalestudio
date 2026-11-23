import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Window

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem rk_filV_succ (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem rk_filV_anti : Antitone (fun a : ℤ => FilV PD (LL := LL) (V := V) a) := by
  exact antitone_int_of_succ_le fun a => rk_filV_succ PD a

theorem rk_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', Submodule.add_mem _ (rk_filV_anti PD (min_le_left a a') ha)
      (rk_filV_anti PD (min_le_right a a') ha')⟩

theorem rk_filV_fd (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset (V ⊗[Qp] BdR), Submodule.span LL (s : Set (V ⊗[Qp] BdR)) = U :=
    (Submodule.fg_iff_finiteDimensional U).2 inferInstance
  have hex : ∀ x ∈ s, ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := fun x _ => rk_filV_exh PD x
  choose! f hf using hex
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne f, ?_⟩
    rw [← hs, Submodule.span_le]
    intro x hx
    exact rk_filV_anti PD (Finset.inf'_le f hx) (hf x hx)
  · refine ⟨0, ?_⟩
    rw [← hs, Finset.not_nonempty_iff_eq_empty.1 hne]
    simp

theorem rk_filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : V ⊗[Qp] BdR ≃ₗ[Qp] (Module.Free.ChooseBasisIndex Qp V →₀ BdR),
      ∀ (v : V) (y : BdR) (i), e (v ⊗ₜ y) i = (Module.Free.chooseBasis Qp V).repr v i • y := by
    first
    | exact ⟨TensorProduct.equivFinsuppOfBasisLeft (Module.Free.chooseBasis Qp V), fun v y i =>
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _⟩
    | exact ⟨TensorProduct.equivFinsuppOfBasisLeft (Module.Free.chooseBasis Qp V), fun v y i => by
        simp [TensorProduct.equivFinsuppOfBasisLeft]⟩
    | exact ⟨(TensorProduct.congr (Module.Free.chooseBasis Qp V).repr (LinearEquiv.refl Qp BdR)).trans
        (TensorProduct.finsuppScalarLeft _ _ _), fun v y i => by simp⟩
    | exact ⟨(TensorProduct.congr (Module.Free.chooseBasis Qp V).repr (LinearEquiv.refl Qp BdR)).trans
        TensorProduct.finsuppScalarLeft, fun v y i => by simp⟩
  have hmem : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, he]
      exact Submodule.smul_of_tower_mem _ _ w.2
    | add y z hy hz =>
      simp only [map_add, Finsupp.add_apply]
      exact Submodule.add_mem _ hy hz
  have h0 : e x = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hmem a x (hx a) i
  exact (LinearEquiv.map_eq_zero_iff e).1 h0

variable (ρ : Representation LL G V)

theorem rk_fildR_anti (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) := by
  exact fun a b hab => inf_le_inf_left _ (rk_filV_anti PD hab)

theorem rk_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := rk_filV_fd PD (DdRE PD ρ τ)
  exact ⟨lo, fun a ha => inf_eq_left.2 (hlo.trans (rk_filV_anti PD ha))⟩

theorem rk_fildR_hi (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ := by
  classical
  haveI hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℤ, ∀ a, finrank LL ↥(FildR PD ρ τ a0) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    have hS : (Set.range fun a : ℤ => finrank LL ↥(FildR PD ρ τ a)).Nonempty := ⟨_, 0, rfl⟩
    obtain ⟨a0, ha0⟩ := Nat.sInf_mem hS
    have ha0' : finrank LL ↥(FildR PD ρ τ a0) =
        sInf (Set.range fun a : ℤ => finrank LL ↥(FildR PD ρ τ a)) := ha0
    exact ⟨a0, fun a => by rw [ha0']; exact Nat.sInf_le ⟨a, rfl⟩⟩
  have hle : ∀ a, a0 ≤ a → finrank LL ↥(FildR PD ρ τ a) ≤ finrank LL ↥(FildR PD ρ τ a0) := by
    intro a ha
    first
    | exact Submodule.finrank_le_finrank_of_le (rk_fildR_anti PD ρ τ ha)
    | exact Submodule.finrank_mono (rk_fildR_anti PD ρ τ ha)
  have heq : ∀ a, a0 ≤ a → FildR PD ρ τ a = FildR PD ρ τ a0 := fun a ha =>
    Submodule.eq_of_le_of_finrank_eq (rk_fildR_anti PD ρ τ ha) (le_antisymm (hle a ha) (ha0 a))
  have hbot : FildR PD ρ τ a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine rk_filV_sep PD (LL := LL) (V := V) x fun b => ?_
    rcases le_total a0 b with hb | hb
    · rw [← heq b hb] at hx
      exact (Submodule.mem_inf.1 hx).2
    · exact rk_filV_anti PD hb (Submodule.mem_inf.1 hx).2
  exact ⟨a0, fun a ha => (heq a ha).trans hbot⟩

theorem rk_multV_of_not_jump (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  push_neg at h
  unfold multV
  rw [h, sub_self]

theorem rk_sum_multV (τ : K →ₐ[Qp] LL) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ m) : ℤ) - finrank LL ↥(FildR PD ρ τ k) := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ n hn ih =>
    have hI : Finset.Ico m (n + 1) = insert n (Finset.Ico m n) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    unfold multV
    ring

end Fil

end Formalism.MainNotions.N.Pv.LocalLengthBound
