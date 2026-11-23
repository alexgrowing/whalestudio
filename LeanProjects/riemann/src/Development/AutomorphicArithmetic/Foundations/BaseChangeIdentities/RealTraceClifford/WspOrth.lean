import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem wsp_orth {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hF : UF F) {μ ν : Wt n} (h : μ ≠ ν) {x y : V}
    (hx : x ∈ wsp F μ) (hy : y ∈ wsp F ν) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 h
  have h1 := hF.unit a a x y
  have hx' : F a a x = (μ a : ℂ) • x := hx a
  have hy' : F a a y = (ν a : ℂ) • y := hy a
  rw [hx', hy', inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
  have h3 : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun e => ha (Complex.ofReal_injective e)
  exact (mul_eq_zero.1 h2).resolve_left h3

theorem UpperTheory.RealTr.wtDec :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∃ s : Finset (Wt n), (∀ μ ∉ s, wsp F μ ⊓ S = ⊥) ∧ (⨆ μ ∈ s, wsp F μ ⊓ S) = S ∧ iSupIndep fun μ => wsp F μ ⊓ S := by
  intro n V _ _ F hF S hSfin hS
  have hind : iSupIndep fun μ => wsp F μ ⊓ S := by
    refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
    show (wsp F μ ⊓ S) ⟂ (wsp F ν ⊓ S)
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    exact wsp_orth hF hne hx.1 hy.1
  let T : Fin n → Module.End ℂ S := fun a => (F a a).restrict (fun x hx => hS a a x hx)
  have hT : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hF.unit a a x y
  have hcomm : Pairwise fun a b => Commute (T a) (T b) := by
    intro a b hab
    have h0 : F a a * F b b = F b b * F a a := by
      have := hF.gl a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at this
      exact this
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show F a a (F b b (x : V)) = F b b (F a a (x : V))
    exact LinearMap.congr_fun h0 (x : V)
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hcomm
  have hkey : ∀ χ : Fin n → ℂ, ∀ v : S, v ∈ (⨅ i, Module.End.eigenspace (T i) (χ i)) →
      (v : V) ∈ wsp F (fun i => (χ i).re) ⊓ S := by
    intro χ v hv
    refine ⟨?_, v.2⟩
    show ∀ i, F i i (v : V) = (((χ i).re : ℝ) : ℂ) • (v : V)
    intro i
    have hvi : T i v = χ i • v := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
    by_cases h0 : v = 0
    · subst h0
      simp
    · have hre : (((χ i).re : ℝ) : ℂ) = χ i := by
        have hs := hT i v v
        rw [hvi, inner_smul_left, inner_smul_right] at hs
        have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr h0
        exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ hvv hs)
      rw [hre]
      exact congrArg Subtype.val hvi
  have hspan : S ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
    have hle : Submodule.map S.subtype (⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i))
        ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
      rw [Submodule.map_iSup]
      refine iSup_le fun χ => ?_
      rintro _ ⟨v, hv, rfl⟩
      exact le_iSup (fun μ : Wt n => wsp F μ ⊓ S) (fun i => (χ i).re) (hkey χ v hv)
    rw [htop, Submodule.map_top, Submodule.range_subtype] at hle
    exact hle
  have hfin : Set.Finite {μ : Wt n | wsp F μ ⊓ S ≠ ⊥} := by
    let W' : Wt n → Submodule ℂ S := fun μ => (wsp F μ).comap S.subtype
    have hind' : iSupIndep W' := by
      refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
      show W' μ ⟂ W' ν
      rw [Submodule.isOrtho_iff_inner_eq]
      intro x hx y hy
      rw [Submodule.coe_inner]
      exact wsp_orth hF hne hx hy
    haveI := hind'.fintypeNeBotOfFiniteDimensional
    refine (Set.finite_range (fun i : {μ // W' μ ≠ ⊥} => (i : Wt n))).subset ?_
    intro μ hμ
    refine ⟨⟨μ, fun h => hμ ?_⟩, rfl⟩
    rw [inf_comm, ← Submodule.map_comap_subtype]
    change Submodule.map S.subtype (W' μ) = ⊥
    rw [h, Submodule.map_bot]
  refine ⟨hfin.toFinset, ?_, ?_, hind⟩
  · intro μ hμ
    by_contra h
    exact hμ (hfin.mem_toFinset.mpr h)
  · apply le_antisymm
    · exact iSup₂_le fun μ _ => inf_le_right
    · refine hspan.trans (iSup_le fun μ => ?_)
      by_cases h : wsp F μ ⊓ S = ⊥
      · rw [h]
        exact bot_le
      · exact le_iSup₂_of_le μ (hfin.mem_toFinset.mpr h) le_rfl
