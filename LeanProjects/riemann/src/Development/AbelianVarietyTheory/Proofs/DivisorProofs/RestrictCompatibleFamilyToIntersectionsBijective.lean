import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.CechPoset

section Bij

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem sec_res_self (s : X ⟶ Sp R) {U : X.Opens} (h : U ≤ U) (c : Sec s U) : Sec.res s h c = c :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_id (op U))

theorem ker_res (s : X ⟶ Sp R) (g : LinearMap.ker (d0 (OAff s))) {U V : X.affineOpens}
    (h : V.1 ≤ U.1) : g.1 (op V) = Sec.res s h (g.1 (op U)) := by
  have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (op U)) (op V))
    (homOfLE (show V ≤ U from h)).op
  rw [amitsur_d0_apply] at this
  exact sub_eq_zero.1 this

variable {κ : Type} [LinearOrder κ]

theorem kerF_res (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (g : LinearMap.ker (d0 (covF s D hD))) {I J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) {U : X.Opens} (hU : U ≤ ⨅ k ∈ J, D k) (hU' : U ≤ ⨅ k ∈ I, D k) :
    Sec.res s hU' (g.1 (ne I hI)) = Sec.res s hU (g.1 (ne J hJ)) := by
  have e := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (ne I hI)) (ne J hJ))
    (homOf (a := ne I hI) (b := ne J hJ) h)
  rw [amitsur_d0_apply] at e
  have e' : g.1 (ne J hJ) = Sec.res s (show (⨅ k ∈ J, D k) ≤ ⨅ k ∈ I, D k from
      biInf_mono fun _ hk ↦ h hk) (g.1 (ne I hI)) := sub_eq_zero.1 e
  rw [e']
  exact Sec.res_res s _ hU _

end Bij

theorem restrictCompatibleFamilyToIntersections_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type}
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  intro hcov
  have hle1 : ∀ i : κ, D i ≤ ⨅ k ∈ ({i} : Finset κ), D k := fun i ↦
    le_iInf₂ fun k hk ↦ by rw [Finset.mem_singleton.1 hk]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ i : κ, g.1 (op (cov D hD (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))) = 0 :=
      fun i ↦ congrFun (congrArg Subtype.val hg) (ne {i} (Finset.singleton_nonempty i))
    apply Subtype.ext
    funext V
    show g.1 V = 0
    let Idx := {p : X.affineOpens × κ // p.1.1 ≤ V.unop.1 ⊓ D p.2}
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Idx ↦ j.1.1.1) V.unop.1
      (fun j ↦ homOfLE (j.2.trans inf_le_left)) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, D i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      obtain ⟨W, hWB, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ V.unop.1 ⊓ D i from ⟨hx, hi⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hWB⟩, i), hWle⟩, hxW⟩
    · intro j
      have hW : j.1.1.1 ≤ V.unop.1 := j.2.trans inf_le_left
      have hWi : j.1.1.1 ≤ (cov D hD (OrderDual.toDual ⟨{j.1.2}, Finset.singleton_nonempty _⟩)).1 :=
        (j.2.trans inf_le_right).trans (hle1 j.1.2)
      have e1 := ker_res s g (U := V.unop) (V := j.1.1) hW
      have e2 := ker_res s g (V := j.1.1) hWi
      rw [h0, map_zero] at e2
      show Sec.res s hW (g.1 V) = Sec.res s hW 0
      rw [map_zero, ← e1, e2]
  · intro g'
    let sf : ∀ i : κ, Sec s (D i) := fun i ↦ Sec.res s (hle1 i) (g'.1 (ne {i} (Finset.singleton_nonempty i)))
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 D sf := by
      intro i j
      show Sec.res s inf_le_left (sf i) = Sec.res s inf_le_right (sf j)
      have hij : D i ⊓ D j ≤ ⨅ k ∈ ({i, j} : Finset κ), D k := le_iInf₂ fun k hk ↦ by
        obtain hk | hk := Finset.mem_insert.1 hk
        · rw [hk]; exact inf_le_left
        · rw [Finset.mem_singleton.1 hk]; exact inf_le_right
      exact (Sec.res_res s (hle1 i) inf_le_left _).symm.trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_left.trans (hle1 i))).trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty j) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_right.trans (hle1 j))).symm.trans
        (Sec.res_res s (hle1 j) inf_le_right _)))
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' D ⊤ (fun i ↦ homOfLE le_top) hcov.symm.le sf hcomp
    let g : LinearMap.ker (d0 (OAff s)) := ⟨fun V ↦ Sec.res s le_top (G : Γ(X, ⊤)), by
      rw [LinearMap.mem_ker]
      funext U U' φ
      rw [amitsur_d0_apply]
      show Sec.res s le_top (G : Γ(X, ⊤)) - Sec.res s _ (Sec.res s le_top (G : Γ(X, ⊤))) = 0
      exact sub_eq_zero.2 (Sec.res_res s _ _ _)⟩
    refine ⟨g, Subtype.ext (funext fun I ↦ ?_)⟩
    show Sec.res s le_top (G : Γ(X, ⊤)) = g'.1 I
    have hm := mn_mem I
    have hi : (cov D hD I.unop).1 ≤ D (mn I) := iInf₂_le (mn I) hm
    have hGi : Sec.res s (le_top : D (mn I) ≤ ⊤) (G : Γ(X, ⊤)) = sf (mn I) := hG (mn I)
    refine (Sec.res_res s le_top hi _).trans ?_
    rw [hGi]
    exact (Sec.res_res s (hle1 (mn I)) hi _).symm.trans
      ((kerF_res s D hD g' (Finset.singleton_nonempty (mn I)) (sub_nonempty I)
        (Finset.singleton_subset_iff.2 hm) le_rfl _).trans (sec_res_self s _ _))

end GlobalTheory.CechPoset
