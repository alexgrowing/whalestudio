import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fix_X_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, n (F0.e a) = F0.e a) :
    ∀ x ∈ F0.X, n x = x := by
  have hle : F0.X ≤ LinearMap.eqLocus (n : (VS D).V →ₗ[D.host.E] (VS D).V) LinearMap.id := by
    show Submodule.span _ (Set.range F0.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simpa [LinearMap.mem_eqLocus] using he a
  intro x hx
  simpa [LinearMap.mem_eqLocus] using hle hx

theorem Xa_le_X {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (k : ℕ) : F0.Xa k ≤ F0.X := by
  show Submodule.span _ _ ≤ Submodule.span _ _
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem mem_orth_iff {D : Formalism.BasicNotions.D7} (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_map_of {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hi : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y)
    (he : ∀ a, n (F0.e a) = F0.e a) (y : (VS D).V) :
    y ∈ orth (VS D) F0.X ↔ n y ∈ orth (VS D) F0.X := by
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro H x hx
    rw [← fix_X_of F0 n he x hx, hi]
    exact H x hx
  · intro H x hx
    rw [← hi, fix_X_of F0 n he x hx]
    exact H x hx

theorem gmap_mem {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {y : (VS D).V} (hy : y ∈ Λ) :
    n y ∈ Λ := by
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem gmap_surj {D : Formalism.BasicNotions.D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {x : (VS D).V} (hx : x ∈ Λ) :
    ∃ y ∈ Λ, n y = x := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem refl_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ := by
  refine ⟨⟨⟨fun x y => rfl, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩, fun a => rfl, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · simp
  · simp

theorem symm_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ) :
    n.symm ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hi, hΛ⟩, -, horth⟩, he, hz⟩ := hn
  have hi' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hi
  have hfix : ∀ x ∈ F0.X, n.symm x = x := fun x hx =>
    n.symm_apply_eq.2 (fix_X_of F0 n he x hx).symm
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · rw [← hi' (n.symm x) (n.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ n hΛ hy
      show n.symm (n w) ∈ Λ
      rw [LinearEquiv.symm_apply_apply]
      exact hw
    · intro hx
      exact ⟨n x, gmap_mem Λ n hΛ hx, n.symm_apply_apply x⟩
  · rw [hfix x (Xa_le_X F0 (j + 1) hx), sub_self]
    exact Submodule.zero_mem _
  · have hy : n.symm x ∈ orth (VS D) F0.X := by
      rw [orth_map_of F0 n hi' he, LinearEquiv.apply_symm_apply]
      exact hx
    have e := horth (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at e
    have e' : n.symm x - x = -(x - n.symm x) := by abel
    rw [e']
    exact Submodule.neg_mem _ e
  · exact n.symm_apply_eq.2 (he a).symm
  · exact n.symm_apply_eq.2 hz.symm

theorem trans_mem_unipotentIntegral {D : Formalism.BasicNotions.D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ N0 F0 Λ)
    (hm : m ∈ N0 F0 Λ) : n.trans m ∈ N0 F0 Λ := by
  obtain ⟨⟨⟨hin, hΛn⟩, -, horthn⟩, hen, hzn⟩ := hn
  obtain ⟨⟨⟨him, hΛm⟩, -, horthm⟩, hem, hzm⟩ := hm
  have hin' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hin
  have him' : ∀ x y, (VS D).hT (m x) (m y) = (VS D).hT x y := him
  refine ⟨⟨⟨fun x y => ?_, ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩, fun a => ?_, ?_⟩
  · show (VS D).hT (m (n x)) (m (n y)) = (VS D).hT x y
    rw [him', hin']
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact gmap_mem Λ m hΛm (gmap_mem Λ n hΛn hy)
    · intro hx
      obtain ⟨w, hw, rfl⟩ := gmap_surj Λ m hΛm hx
      obtain ⟨v, hv, rfl⟩ := gmap_surj Λ n hΛn hw
      exact ⟨v, hv, rfl⟩
  · have hX := Xa_le_X F0 (j + 1) hx
    show m (n x) - x ∈ _
    rw [fix_X_of F0 n hen x hX, fix_X_of F0 m hem x hX, sub_self]
    exact Submodule.zero_mem _
  · have h1 := horthn x hx
    have h2 := horthm (n x) ((orth_map_of F0 n hin' hen x).1 hx)
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      show m (n x) - x = _
      abel
    rw [e]
    exact Submodule.add_mem _ h2 h1
  · show m (n (F0.e a)) = F0.e a
    rw [hen, hem]
  · show m (n F0.z) = F0.z
    rw [hzn, hzm]

theorem unipotent_integral_isGroup : UnipotentIntegralIsGroup := by
  intro D T F0 Λ
  exact ⟨refl_mem_unipotentIntegral F0 Λ, fun n hn => symm_mem_unipotentIntegral F0 Λ n hn,
    fun n hn m hm => trans_mem_unipotentIntegral F0 Λ n m hn hm⟩

end PI.UnitaryGroupMassFormula.CntFormula
