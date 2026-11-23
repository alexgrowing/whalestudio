import Formalism.WeaklyAdmissibleFiltrations.Statement

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

theorem tele (f : ℤ → ℤ) (m : ℤ) (d : ℕ) :
    ∑ a ∈ Finset.Ico m (m + d), (f a - f (a + 1)) = f m - f (m + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hI : Finset.Ico m (m + ((d + 1 : ℕ) : ℤ)) = insert (m + d) (Finset.Ico m (m + d)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    push_cast
    ring

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fr_filV_succ (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul v b =>
    exact LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add s t hs ht =>
    rw [map_add]
    exact add_mem hs ht

theorem fr_filV_anti : Antitone (fun a : ℤ => FilV PD (LL := LL) (V := V) a) := antitone_int_of_succ_le fun a => fr_filV_succ PD a

theorem fr_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', add_mem (fr_filV_anti PD (min_le_left a a') ha)
      (fr_filV_anti PD (min_le_right a a') ha')⟩

theorem fr_filV_fd (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  classical
  have hfin : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a : ℤ, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s hy ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := fr_filV_exh PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact fr_filV_anti PD (min_le_right a b) hb
      · exact fr_filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional U).2 inferInstance
  obtain ⟨a, ha⟩ := hfin s
  exact ⟨a, hs ▸ Submodule.span_le.2 fun x hx => ha x hx⟩

theorem fr_filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let bV := Module.Basis.ofVectorSpace Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hmem : ∀ a (y : V ⊗[Qp] BdR), y ∈ FilV PD (LL := LL) (V := V) a → ∀ i, e y i ∈ PD.Fil a := by
    intro a y hy i
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.1 hy
    clear hy
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
      exact Submodule.smul_of_tower_mem _ _ b.2
    | add s t hs ht =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact add_mem hs ht
  have hz : e x = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hmem a x (hx a) i
  exact e.injective (hz.trans (map_zero e).symm)

variable (ρ : Representation LL G V)

theorem fr_fildR_anti (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) := fun a b hab => inf_le_inf_left _ (fr_filV_anti PD hab)

theorem fr_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := fr_filV_fd PD (LL := LL) (V := V) (DdRE PD ρ τ)
  refine ⟨lo, fun a ha => ?_⟩
  unfold FildR
  exact inf_eq_left.2 (hlo.trans (fr_filV_anti PD ha))

theorem fr_fildR_hi (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ := by
  classical
  have hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL ↥(FildR PD ρ τ a) = n := ⟨_, 0, rfl⟩
  obtain ⟨a0, ha0⟩ := Nat.find_spec hex
  have hmin : ∀ a, finrank LL ↥(FildR PD ρ τ a0) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    intro a
    rw [ha0]
    exact Nat.find_min' hex ⟨a, rfl⟩
  haveI := hfd a0
  have hstab : ∀ a, a0 ≤ a → FildR PD ρ τ a = FildR PD ρ τ a0 := fun a ha =>
    Submodule.eq_of_le_of_finrank_le (fr_fildR_anti PD ρ τ ha) (hmin a)
  have hbot : FildR PD ρ τ a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply fr_filV_sep PD (LL := LL) x
    intro b
    rcases le_total a0 b with h | h
    · rw [← hstab b h] at hx
      exact hx.2
    · exact fr_filV_anti PD h hx.2
  exact ⟨a0, fun a ha => by rw [hstab a ha, hbot]⟩

theorem fr_multV_of_not_jump (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem fr_sum_multV (τ : K →ₐ[Qp] LL) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ m) : ℤ) - finrank LL ↥(FildR PD ρ τ k) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = m + d := ⟨(k - m).toNat, by omega⟩
  exact tele (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) m d

end Fil

end Formalism.MainNotions.N.Ln34.UniversalFiltration
