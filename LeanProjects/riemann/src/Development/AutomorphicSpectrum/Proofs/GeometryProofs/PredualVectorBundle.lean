import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) : Module.Basis (Fin r) Ω V :=
  B.dualBasis.map (Module.evalEquiv Ω V).symm

theorem apply_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (i j : Fin r) :
    B i (preDualBasis B j) = if i = j then 1 else 0 := by
  have h : ∀ x : Module.Dual Ω (Module.Dual Ω V), B i ((Module.evalEquiv Ω V).symm x) = x (B i) := by
    intro x
    obtain ⟨y, rfl⟩ := (Module.evalEquiv Ω V).surjective x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [preDualBasis, Module.Basis.map_apply, h, Module.Basis.dualBasis_apply_self]

theorem sum_apply_smul_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (v : V) :
    ∑ i, B i v • preDualBasis B i = v := by
  have hc : ∀ i, (preDualBasis B).coord i = B i := by
    intro i
    refine (preDualBasis B).ext (fun j => ?_)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, apply_preDualBasis, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  conv_rhs => rw [← (preDualBasis B).sum_repr v]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Module.Basis.coord_apply, hc]

theorem Lat.predualIn_isFrameAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {L : Lat ξ (Module.Dual Ω Li)} {V : Submodule Ω Li} [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) {q : Cpt ξ}
    (h : (L.map V.dualRestrict) q = Submodule.span (regAt ξ q) (Set.range B)) :
    (L.predualIn V).IsFrameAt (fun j => (preDualBasis B j : Li)) q := by
  have hB : ∀ i, ∃ w ∈ L q, V.dualRestrict w = B i := by
    intro i
    have hi : B i ∈ (L.map V.dualRestrict) q := by
      rw [h]
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨w, hw, hwe⟩ := (Submodule.mem_map).mp hi
    exact ⟨w, hw, hwe⟩
  have hw : ∀ w ∈ L q, ∀ j, w (preDualBasis B j : Li) ∈ regAt ξ q := by
    intro w hwL j
    have hm : V.dualRestrict w ∈ (L.map V.dualRestrict) q := Submodule.mem_map_of_mem hwL
    rw [h] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
    have hj : (∑ i, c i • B i) (preDualBasis B j) = w (preDualBasis B j : Li) := by
      rw [hc]
      rfl
    have hj' : (∑ i, c i • B i) (preDualBasis B j) = (c j : Ω) := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, apply_preDualBasis]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, Subring.smul_def, smul_eq_mul, _root_.mul_one]
      · intro b _ hb
        rw [if_neg hb, smul_zero]
      · intro hj0
        exact absurd (Finset.mem_univ j) hj0
    rw [← hj, hj']
    exact (c j).2
  refine ⟨(preDualBasis B).linearIndependent.map' V.subtype (Submodule.ker_subtype V), ?_⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvw⟩ := hv
    have hcoef : ∀ i, B i ⟨v, hvV⟩ ∈ regAt ξ q := by
      intro i
      obtain ⟨w, hwL, hwe⟩ := hB i
      rw [← hwe, Submodule.dualRestrict_apply]
      exact hvw w hwL
    have hv' : v = ∑ i, B i ⟨v, hvV⟩ • (preDualBasis B i : Li) := by
      have hs := congrArg Subtype.val (sum_apply_smul_preDualBasis B ⟨v, hvV⟩)
      rw [Submodule.coe_sum] at hs
      simpa only [Submodule.coe_smul] using hs.symm
    rw [hv']
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have he : B i ⟨v, hvV⟩ • (preDualBasis B i : Li) =
        (⟨B i ⟨v, hvV⟩, hcoef i⟩ : regAt ξ q) • (preDualBasis B i : Li) := rfl
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (preDualBasis B j : Li) ∈ V ∧ ∀ w ∈ L q, w (preDualBasis B j : Li) ∈ regAt ξ q
    exact ⟨(preDualBasis B j).2, fun w hwL => hw w hwL j⟩

theorem Lat.predualIn_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li]
    [Module Ω Li] (L : Lat ξ (Module.Dual Ω Li)) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li)
    [FiniteDimensional Ω V],
    (L.map V.dualRestrict).IsVBOn T r ⊤ → (L.predualIn V).IsVBOn T r V := by
  intro X Ω _ ξ Li _ _ L T r V _ hL p hp
  obtain ⟨U, hpU, b, hbspan, hfr⟩ := hL p hp
  have hli : LinearIndependent Ω b := (hfr p hp hpU).1
  refine ⟨U, hpU, fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li), ?_, ?_⟩
  · have he : (fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li)) =
        V.subtype ∘ preDualBasis (Module.Basis.mk hli hbspan.ge) := rfl
    rw [he, Set.range_comp, Submodule.span_image, (preDualBasis (Module.Basis.mk hli hbspan.ge)).span_eq,
      Submodule.map_subtype_top]
  · intro q hq hqU
    apply Lat.predualIn_isFrameAt (Module.Basis.mk hli hbspan.ge)
    rw [(hfr q hq hqU).2, Module.Basis.coe_mk]

end GlobalTheory.CompanionTheory.Ar
