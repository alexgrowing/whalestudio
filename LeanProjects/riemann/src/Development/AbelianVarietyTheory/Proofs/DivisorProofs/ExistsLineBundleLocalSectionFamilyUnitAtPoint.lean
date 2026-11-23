import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.SemiLoc

variable {X : Scheme.{0}}

theorem exists_pow_mul_eq_zero_of_germ {V : X.Opens} (hV : IsAffineOpen V) (h s : Γ(X, V))
    (H : ∀ z (hz : z ∈ V), z ∈ X.basicOpen h → (X.presheaf.germ V z hz).hom s = 0) :
    ∃ m : ℕ, h ^ m * s = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hV
  apply TopCat.Presheaf.section_ext X.sheaf
  intro z hz
  simp only [TopCat.Presheaf.restrictOpen, map_zero]
  erw [TopCat.Presheaf.germ_res_apply]
  exact (H z (X.basicOpen_le h hz) hz).trans (map_zero _).symm

theorem exists_germ_eq_pow_mul {V O : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hO : X.basicOpen h ≤ O) (r : Γ(X, O)) :
    ∃ (n : ℕ) (y : Γ(X, V)), ∀ z (hz : z ∈ X.basicOpen h),
      (X.presheaf.germ V z (X.basicOpen_le h hz)).hom y =
        (X.presheaf.germ V z (X.basicOpen_le h hz)).hom h ^ n *
          (X.presheaf.germ O z (hO hz)).hom r := by
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV h
    ((X.presheaf.map (homOfLE hO).op).hom r)
  refine ⟨n, y, fun z hz => ?_⟩
  have := congrArg (X.presheaf.germ (X.basicOpen h) z hz).hom hy
  simp only [TopCat.Presheaf.restrictOpen, map_mul, map_pow] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem germ_cocycle {L : LB X} (hL : L.IsLB) (a b c : L.ι) (z : X) (ha : z ∈ L.U a)
    (hb : z ∈ L.U b) (hc : z ∈ L.U c) :
    (X.presheaf.germ (L.U a ⊓ L.U b) z ⟨ha, hb⟩).hom (L.g a b).val *
      (X.presheaf.germ (L.U b ⊓ L.U c) z ⟨hb, hc⟩).hom (L.g b c).val =
    (X.presheaf.germ (L.U a ⊓ L.U c) z ⟨ha, hc⟩).hom (L.g a c).val := by
  have := congrArg (fun u : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ =>
    (X.presheaf.germ (L.U a ⊓ L.U b ⊓ L.U c) z ⟨⟨ha, hb⟩, hc⟩).hom u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul, res, Units.coe_map] at this
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  exact this

end GlobalTheory.Pinch.SemiLoc

namespace GlobalTheory.Pinch.SemiLoc

theorem exists_secFam_isUnit_germ : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ (J : Type) [Fintype J] (f : J → Γ(X, W)) (k : J → L.ι) (hk : ∀ j, X.basicOpen (f j) ≤ L.U (k j)) (x : X), x ∈ W → ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
  intro X L hL W hW J _ f k hk x hxW
  classical
  obtain ⟨k0, hk0⟩ : ∃ k0, x ∈ L.U k0 := by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le (V := L.U k0) ⟨x, hk0⟩ hxW
  have hDW : ∀ j, X.basicOpen (f j) ≤ W := fun j => X.basicOpen_le (f j)
  let hj : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom h
  have hbj : ∀ j, X.basicOpen (hj j) = X.basicOpen (f j) ⊓ X.basicOpen h :=
    fun j => X.basicOpen_res h _
  have hgj : ∀ j z (hz : z ∈ X.basicOpen (f j)),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (hj j) =
        (X.presheaf.germ W z (hDW j hz)).hom h :=
    fun j z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hO : ∀ j, X.basicOpen (hj j) ≤ L.U (k j) ⊓ L.U k0 := fun j => by
    rw [hbj]; exact inf_le_inf (hk j) hhU
  choose n y hy using fun j =>
    exists_germ_eq_pow_mul (hW.basicOpen (f j)) (hj j) (hO j) (L.g (k j) k0).val
  let N := Finset.univ.sup n
  let e : ∀ j, Γ(X, X.basicOpen (f j)) := fun j => hj j ^ (N - n j) * y j
  have he : ∀ j z (hz : z ∈ X.basicOpen (f j)) (hzh : z ∈ X.basicOpen h),
      (X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) =
        (X.presheaf.germ W z (hDW j hz)).hom h ^ N *
          (X.presheaf.germ (L.U (k j) ⊓ L.U k0) z ⟨hk j hz, hhU hzh⟩).hom (L.g (k j) k0).val := by
    intro j z hz hzh
    have hz' : z ∈ X.basicOpen (hj j) := by rw [hbj]; exact ⟨hz, hzh⟩
    have h1 := hy j z hz'
    simp only [e, map_mul, map_pow]
    rw [h1]; simp only [hgj]; rw [← _root_.mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ j))]
  have hdef : ∀ j j', ∃ m : ℕ, ∀ z (hz : z ∈ X.basicOpen (f j)) (hz' : z ∈ X.basicOpen (f j')),
      (X.presheaf.germ W z (hDW j hz)).hom h ^ m *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
    intro j j'
    obtain ⟨V, hVdef⟩ : ∃ V, V = X.basicOpen (f j * f j') := ⟨_, rfl⟩
    have hVeq : V = X.basicOpen (f j) ⊓ X.basicOpen (f j') := hVdef.trans (X.basicOpen_mul _ _)
    have hVa : IsAffineOpen V := hVdef ▸ hW.basicOpen (f j * f j')
    have hV1 : V ≤ X.basicOpen (f j) := hVeq ▸ inf_le_left
    have hV2 : V ≤ X.basicOpen (f j') := hVeq ▸ inf_le_right
    have hVg : V ≤ L.U (k j) ⊓ L.U (k j') := le_inf (hV1.trans (hk j)) (hV2.trans (hk j'))
    have hVW : V ≤ W := hV1.trans (hDW j)
    let d : Γ(X, V) := (X.presheaf.map (homOfLE hV1).op).hom (e j) -
      (X.presheaf.map (homOfLE hVg).op).hom (L.g (k j) (k j')).val *
        (X.presheaf.map (homOfLE hV2).op).hom (e j')
    let hV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom h
    have hbV : X.basicOpen hV = V ⊓ X.basicOpen h := X.basicOpen_res h _
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_germ hVa hV d (by
      intro z hz hzb
      rw [hbV] at hzb
      simp only [d, map_sub, map_mul]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        TopCat.Presheaf.germ_res_apply]
      rw [he j z (hV1 hz) hzb.2, he j' z (hV2 hz) hzb.2,
        ← germ_cocycle hL (k j) (k j') k0 z (hk j (hV1 hz)) (hk j' (hV2 hz)) (hhU hzb.2)]
      ring)
    refine ⟨m, fun z hz hz' => ?_⟩
    have hzV : z ∈ V := by rw [hVeq]; exact ⟨hz, hz'⟩
    have := congrArg (X.presheaf.germ V z hzV).hom hm
    simp only [d, hV, map_mul, map_pow, map_sub, map_zero] at this
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
    exact this
  choose m hm using hdef
  let M := Finset.univ.sup (fun p : J × J => m p.1 p.2)
  refine ⟨fun j => hj j ^ M * e j, ?_, ?_⟩
  · intro j j' z hz hz'
    have hle : m j j' ≤ M := Finset.le_sup (f := fun p : J × J => m p.1 p.2) (Finset.mem_univ (j, j'))
    have h0 := hm j j' z hz hz'
    simp only [map_mul, map_pow]
    simp only [hgj]
    have h2 : (X.presheaf.germ W z (hDW j hz)).hom h ^ M *
        ((X.presheaf.germ (X.basicOpen (f j)) z hz).hom (e j) -
          (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hk j hz, hk j' hz'⟩).hom
              (L.g (k j) (k j')).val *
            (X.presheaf.germ (X.basicOpen (f j')) z hz').hom (e j')) = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc, h0, mul_zero]
    linear_combination h2
  · intro j hx
    have hu : IsUnit ((X.presheaf.germ W x (hDW j hx)).hom h) := (X.mem_basicOpen h x _).1 hxh
    simp only [map_mul, map_pow]
    simp only [hgj]; rw [he j x hx hxh]
    exact (hu.pow _).mul ((hu.pow _).mul ((L.g (k j) k0).isUnit.map _))

end GlobalTheory.Pinch.SemiLoc
