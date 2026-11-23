import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

namespace GlobalTheory.CompFin

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ' r) :
    castFrame h (castFrame h.symm x) = x := rfl

theorem castFrame_mem_GG (X : Data E r) {Ψ : Finset (E →+* ℂ)} (h : X.Ψ = Ψ) (x : Frame X.Ψ r) :
    castFrame h x ∈ GG Ψ X.Gm X.p0 ↔ x ∈ X.dom := by
  subst h
  rfl

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem castFrame_mem_dom (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  have := castFrame_mem_GG (M.comp c).toData (M.comp_Ψ c) x
  rw [M.comp_Gm c, M.comp_basePoint c] at this
  exact this

def toComp (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] ((M.comp c).dom → ℂ) where
  toFun v x := v c ⟨castFrame (M.comp_Ψ c) x.1, (castFrame_mem_dom M c x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cusp_le_comap (ka : Wt M.Ψ r) (c : C) :
    M.cusp ka ≤ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) ''
      (M.comp c).SS (castWt (M.comp_Ψ c) ka))).comap (toComp M c) := by
  unfold TwoLevels.cusp
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact Submodule.subset_span ⟨_, hF c, rfl⟩

theorem toComp_inj (v w : C → M.dom → ℂ) (h : ∀ c, toComp M c v = toComp M c w) : v = w := by
  funext c y
  have hy : castFrame (M.comp_Ψ c).symm y.1 ∈ (M.comp c).dom :=
    (castFrame_mem_dom M c _).1 (by rw [castFrame_castFrame]; exact y.2)
  have := congrFun (h c) ⟨_, hy⟩
  exact this

end

end GlobalTheory.CompFin

open GlobalTheory.CompFin in

theorem GlobalTheory.cusp_finite_of_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ M ka hfin
  let S : (c : C) → Submodule ℂ ((M.comp c).dom → ℂ) := fun c => Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ =>
    fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka))
  have : ∀ c, Module.Finite ℂ (S c) := hfin
  let Φ : M.cusp ka →ₗ[ℂ] (∀ c, S c) := LinearMap.pi fun c =>
    ((toComp M c).domRestrict (M.cusp ka)).codRestrict (S c) fun v => cusp_le_comap M ka c v.2
  have hΦ : Function.Injective Φ := by
    intro v w hvw
    apply Subtype.ext
    apply toComp_inj M
    intro c
    have := congrArg Subtype.val (congrFun hvw c)
    exact this
  exact Module.Finite.of_injective Φ hΦ
