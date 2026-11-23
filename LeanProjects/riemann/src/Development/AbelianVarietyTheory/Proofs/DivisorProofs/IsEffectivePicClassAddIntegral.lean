import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic TopologicalSpace

theorem res_res_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem mul_compat {X : Scheme.{0}} {A₁ A₂ B₁ B₂ : X.Opens} (s₁ : Γ(X, A₁)) (s₂ : Γ(X, A₂))
    (t₁ : Γ(X, B₁)) (t₂ : Γ(X, B₂)) (gA : Γ(X, A₁ ⊓ A₂)ˣ) (gB : Γ(X, B₁ ⊓ B₂)ˣ)
    (hs : (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ A₂ ≤ A₁)).op).hom s₁ =
      (gA : Γ(X, A₁ ⊓ A₂)) * (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ A₂ ≤ A₂)).op).hom s₂)
    (ht : (X.presheaf.map (homOfLE (inf_le_left : B₁ ⊓ B₂ ≤ B₁)).op).hom t₁ =
      (gB : Γ(X, B₁ ⊓ B₂)) * (X.presheaf.map (homOfLE (inf_le_right : B₁ ⊓ B₂ ≤ B₂)).op).hom t₂) :
    (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ B₁)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ≤ A₁)).op).hom s₁ *
          (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ≤ B₁)).op).hom t₁) =
      ((res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂) gA *
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂) gB : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))ˣ) : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))) *
      (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₂ ⊓ B₂)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₂ ⊓ B₂ ≤ A₂)).op).hom s₂ *
          (X.presheaf.map (homOfLE (inf_le_right : A₂ ⊓ B₂ ≤ B₂)).op).hom t₂) := by
  have hσ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂)).op).hom hs
  have hτ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂)).op).hom ht
  rw [res_res_apply, map_mul, res_res_apply] at hσ hτ
  simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, res_res_apply]
  rw [hσ, hτ]
  ring

def tensSec {X : Scheme.{0}} {A B : LB X} (σ : LB.Sec A) (τ : LB.Sec B) : LB.Sec (tens A B) where
  f p := (X.presheaf.map (homOfLE (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1)).op).hom (σ.f p.1) *
    (X.presheaf.map (homOfLE (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2)).op).hom (τ.f p.2)
  compat p q := mul_compat _ _ _ _ _ _ (σ.compat p.1 q.1) (τ.compat p.2 q.2)

theorem germ_sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {N : LB X} (σ : LB.Sec N) {j : N.ι}
    (hj : σ.f j ≠ 0) (i : N.ι) (y : X) (hy : y ∈ N.U i) : X.presheaf.germ (N.U i) y hy (σ.f i) ≠ 0 := by
  intro h0
  have hi0 : σ.f i = 0 := germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  apply hj
  by_cases hne : (N.U j : Set X).Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen ⟨y, hy⟩ ⟨z, hz⟩
    apply germ_injective_of_isIntegral X w hwj
    rw [map_zero]
    have hw : w ∈ N.U i ⊓ N.U j := ⟨hwi, hwj⟩
    have e := congrArg (X.presheaf.germ (N.U i ⊓ N.U j) w hw) (σ.compat i j)
    rw [X.presheaf.germ_res_apply, hi0, map_zero, map_mul, X.presheaf.germ_res_apply] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (((N.g i j).isUnit.map (X.presheaf.germ (N.U i ⊓ N.U j) w hw).hom).ne_zero)
    · exact h
  · have hT : N.U j = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    haveI : Subsingleton Γ(X, N.U j) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact Subsingleton.elim _ _

theorem eff_add {X : Scheme.{0}} [IsIntegral X] (a b : Pic X) (ha : Eff a) (hb : Eff b) : Eff (a + b) := by
  obtain ⟨A, hA, rfl, σ, j, hσ⟩ := ha
  obtain ⟨B, hB, rfl, τ, k, hτ⟩ := hb
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  have hyA : y ∈ ⨆ i, A.U i := hA.cover ▸ trivial
  have hyB : y ∈ ⨆ i, B.U i := hB.cover ▸ trivial
  obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hyA
  obtain ⟨q, hq⟩ := Opens.mem_iSup.1 hyB
  refine ⟨tens A B, isLB_tens hA hB, cls_tens hA hB _, tensSec σ τ, (p, q), ?_⟩
  have hy : y ∈ A.U p ⊓ B.U q := ⟨hp, hq⟩
  intro h0
  have h0' : (X.presheaf.map (homOfLE (inf_le_left : A.U p ⊓ B.U q ≤ A.U p)).op).hom (σ.f p) *
      (X.presheaf.map (homOfLE (inf_le_right : A.U p ⊓ B.U q ≤ B.U q)).op).hom (τ.f q) = 0 := h0
  have e' := congrArg (X.presheaf.germ (A.U p ⊓ B.U q) y hy) h0'
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, map_zero] at e'
  rcases mul_eq_zero.mp e' with h | h
  · exact germ_sec_ne_zero σ hσ p y hp h
  · exact germ_sec_ne_zero τ hτ q y hq h

end GlobalTheory.EffBound
