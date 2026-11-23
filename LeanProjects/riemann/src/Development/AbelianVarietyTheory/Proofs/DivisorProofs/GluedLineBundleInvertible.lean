import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.IsLBProof

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_inj {X : Scheme.{0}} [IsIntegral X] (P : X.Opens) (hP : (P : Set X).Nonempty) (V : X.Opens) :
    Function.Injective (res (inf_le_left : V ⊓ P ≤ V)) := by
  by_cases hV : (V : Set X).Nonempty
  · have hne : ((V ⊓ P : X.Opens) : Set X).Nonempty := by
      obtain ⟨z, _, hz⟩ := (PreirreducibleSpace.isPreirreducible_univ (X := X)) _ _ V.isOpen P.isOpen
        (by simpa using hV) (by simpa using hP)
      exact ⟨z, hz⟩
    haveI : Nonempty (V ⊓ P : X.Opens) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    intro a b hab
    have hi := map_injective_of_isIntegral X (homOfLE (inf_le_left : V ⊓ P ≤ V))
    ext
    apply hi
    have := congrArg (fun w : Γ(X, V ⊓ P)ˣ => (w : Γ(X, V ⊓ P))) hab
    simpa [res] using this
  · have hb : V = ⊥ := by
      ext z; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hz; exact hV ⟨z, hz⟩
    subst hb
    intro a b _
    exact Subsingleton.elim a b

theorem ratio_res {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
    (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (u : Γ(X, Uc h x ⊓ Uc h y)ˣ) (hu : RatioProp h x y u)
    (W : X.Opens) (hW : W ≤ Uc h x ⊓ Uc h y ⊓ Xp X p) :
    res (hW.trans inf_le_left) u *
      res (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h y) =
    res (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (Cx h x) := by
  have := congrArg (res hW) hu.1
  rwa [map_mul, res_res', res_res', res_res'] at this

end GlobalTheory.UnitGlue.IsLBProof

namespace GlobalTheory.UnitGlue

open GlobalTheory.UnitGlue.IsLBProof in

theorem glueLB_isLB : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), IsIntegral X → (Xw : Set X).Nonempty → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (∀ x y : X, ∃ u, RatioProp h x y u) → (glueLB h).IsLB := by
  intro p _ X Xw K h hI hw hle hex
  have hP : ((Xp X p : X.Opens) : Set X).Nonempty := hw.mono hle
  have hR : ∀ x y, RatioProp h x y (gU h x y) := fun x y => by
    unfold gU; rw [dif_pos (hex x y)]; exact (hex x y).choose_spec
  refine ⟨?_, fun (i : X) => ?_, fun (i j k : X) => ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨x, ?_⟩
    obtain ⟨y, hy⟩ := (c_spec h x).2.1
    show x ∈ ((cξ h x ''ᵁ ⊤ : X.Opens) : Set X)
    exact ⟨y, trivial, hy⟩
  · show res (le_inf le_rfl le_rfl : Uc h i ≤ Uc h i ⊓ Uc h i) (gU h i i) = 1
    apply res_inj (Xp X p) hP (Uc h i)
    rw [res_res', map_one]
    have hW : Uc h i ⊓ Xp X p ≤ Uc h i ⊓ Uc h i ⊓ Xp X p := le_inf (le_inf inf_le_left inf_le_left) inf_le_right
    have h1 := ratio_res h i i _ (hR i i) _ hW
    have h2 : res (hW.trans inf_le_left) (gU h i i) = 1 := by
      have h3 := h1
      rw [mul_eq_right] at h3
      exact h3
    exact h2
  · show res (inf_le_left : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h j) (gU h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h j ⊓ Uc h k) (gU h j k) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h k) (gU h i k)
    apply res_inj (Xp X p) hP _
    rw [map_mul, res_res', res_res', res_res']
    have hT : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h j ⊓ Xp X p :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT2 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h j ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hT3 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hij := ratio_res h i j _ (hR i j) _ hT
    have hjk := ratio_res h j k _ (hR j k) _ hT2
    have hik := ratio_res h i k _ (hR i k) _ hT3
    apply mul_right_cancel (b := res (hT2.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h k))
    rw [_root_.mul_assoc, hjk, hij, hik]

end GlobalTheory.UnitGlue
