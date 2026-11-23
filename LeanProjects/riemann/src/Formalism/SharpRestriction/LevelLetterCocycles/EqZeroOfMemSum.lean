import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Comp

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_of_mem {τ : K →ₐ[Qp] LL} {y : V ⊗[Qp] BdR} (hy : y ∈ DdRE PD ρ τ) (c : K) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y = τ c • y := by
  have h := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hy).2 c
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact h

theorem eq_zero_of_mem_sum (τ : K →ₐ[Qp] LL) :
    ∀ (s : Finset (K →ₐ[Qp] LL)), τ ∉ s → ∀ y ∈ DdRE PD ρ τ,
      y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' → y = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ y _ hy
    simpa using hy
  | insert a s ha ih =>
    intro hτ y hyτ hy
    have haτ : a ≠ τ := fun h => hτ (h ▸ Finset.mem_insert_self a s)
    have hτs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
    obtain ⟨c, hc⟩ : ∃ c : K, τ c ≠ a c := by
      by_contra h
      push_neg at h
      exact haτ (AlgHom.ext fun c => (h c).symm)

    let φ : Module.End LL (V ⊗[Qp] BdR) :=
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c - a c • LinearMap.id
    have hφ : ∀ τ', ∀ x ∈ DdRE PD ρ τ', φ x = (τ' c - a c) • x := by
      intro τ' x hx
      simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        mulVdR_of_mem PD ρ hx c, sub_smul]
    have hW : ∀ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ', φ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      intro x hx
      have hle : (⨆ τ' ∈ s, DdRE PD ρ τ') ≤ (⨆ τ' ∈ s, DdRE PD ρ τ').comap φ := by
        refine iSup₂_le fun τ' hτ' => fun z hz => ?_
        rw [Submodule.mem_comap, hφ τ' z hz]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' hτ') hz)
      exact hle hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hy
    obtain ⟨ya, hya, z, hz, hyz⟩ := hy
    have h1 : φ y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      rw [← hyz, map_add, hφ a ya hya, sub_self, zero_smul, zero_add]
      exact hW z hz
    rw [hφ τ y hyτ] at h1
    have h2 := ih hτs _ (Submodule.smul_mem _ _ hyτ) h1
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)

theorem mem_of_mem_filC (τ : K →ₐ[Qp] LL) (F : Submodule LL (V ⊗[Qp] BdR)) (hF : F ≤ DdRE PD ρ τ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdRE PD ρ τ)
    (h : x ∈ F ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') : x ∈ F := by
  classical
  obtain ⟨f, hf, z, hz, hfz⟩ := Submodule.mem_sup.mp h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hz
  have hle : (⨆ τ' ∈ s, ⨆ (_ : τ' ≠ τ), DdRE PD ρ τ') ≤ ⨆ τ' ∈ s.filter (· ≠ τ), DdRE PD ρ τ' := by
    refine iSup₂_le fun τ' hτ' => iSup_le fun hne => ?_
    exact le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' (Finset.mem_filter.mpr ⟨hτ', hne⟩)
  have hzτ : z ∈ DdRE PD ρ τ := by
    have e : z = x - f := by rw [← hfz]; abel
    rw [e]
    exact Submodule.sub_mem _ hx (hF hf)
  have hz0 := eq_zero_of_mem_sum PD ρ τ (s.filter (· ≠ τ)) (by simp) z hzτ (hle hs)
  rw [← hfz, hz0, add_zero]
  exact hf

theorem fildR_eq_bot (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] (b : ℤ)
    (hj : JumpsInV PD ρ τ (Set.Iic (-b))) : ∀ a : ℤ, -b < a → FildR PD ρ τ a = ⊥ := by
  intro a ha
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (PD := PD) (ρ := ρ) τ
  have hstep : ∀ c : ℤ, -b < c → FildR PD ρ τ c = FildR PD ρ τ (c + 1) := by
    intro c hc
    by_contra h
    have h2 := hj c (fun h' => h h'.symm)
    exact absurd (Set.mem_Iic.1 h2) (not_le.2 hc)
  have hk : ∀ k : ℕ, FildR PD ρ τ a = FildR PD ρ τ (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hstep (a + k) (by omega)]
      congr 1
      push_cast
      ring
  rw [hk (hi - a).toNat]
  exact hhi _ (by omega)

end Comp

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge
