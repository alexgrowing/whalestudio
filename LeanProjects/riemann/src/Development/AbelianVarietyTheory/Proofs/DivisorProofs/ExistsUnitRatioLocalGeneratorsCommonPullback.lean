import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (g h w b a : G) :
    g * b * (g * h⁻¹ * w * (h * a))⁻¹ = b * (w * a)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem comm_aux₂ {G : Type*} [CommGroup G] (w b a : G) : b = w * (b * (w * a)⁻¹ * a) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem locGen_gm {Y T : Scheme.{0}} {L : LB Y} {V : Y.Opens} {a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ} (h : LocGen L V a)
    (f : T ⟶ Y) (t : T) (k k' : L.ι) (hv : f t ∈ V) (hk : f t ∈ L.U k) (hk' : f t ∈ L.U k') :
    gm f t (V ⊓ L.U k) (a k) = gm f t (L.U k ⊓ L.U k') (L.g k k') * gm f t (V ⊓ L.U k') (a k') := by
  have e : res (inf_le_left : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k) (a k) =
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ L.U k ⊓ L.U k') (L.g k k') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k') (a k') := by
    apply unit_ext
    intro y hy
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    exact h y k k' hy.1.1 hy.1.2 hy.2
  have hm : f t ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hv, hk⟩, hk'⟩
  have := congrArg (gm f t (V ⊓ L.U k ⊓ L.U k')) e
  rwa [map_mul, gm_res _ _ _ hm, gm_res _ _ _ hm, gm_res _ _ _ hm] at this

theorem iso_gm {X' Z Z' : Scheme.{0}} {i' : Z' ⟶ X'} {p' : Z' ⟶ Z} {L' : LB X'} {N : LB Z}
    {w : LB.Iso (L'.pull i') (N.pull p')} (hw : w.IsGen) (x : Z') (k k' : L'.ι) (l l' : N.ι)
    (hk : i' x ∈ L'.U k) (hk' : i' x ∈ L'.U k') (hl : p' x ∈ N.U l) (hl' : p' x ∈ N.U l') :
    gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) =
      gm p' x (N.U l ⊓ N.U l') (N.g l l') * (gm i' x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k')) (w.s (fun _ ↦ l', fun _ ↦ k')) := by
  have hp : x ∈ (N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k) := ⟨mem_pull.2 hl, mem_pull.2 hk⟩
  have hq : x ∈ (N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k') := ⟨mem_pull.2 hl', mem_pull.2 hk'⟩
  have e := (isGen_iff_germ w).1 hw x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have d := gm_div' (N.pull p') (L'.pull i') (𝟙 Z') x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have g1 := gm_pull_g N p' (𝟙 Z') x (fun _ ↦ l) (fun _ ↦ l') hp.1 hq.1
  have g2 := gm_pull_g L' i' (𝟙 Z') x (fun _ ↦ k) (fun _ ↦ k') hp.2 hq.2
  rw [Category.id_comp] at g1 g2
  rw [d, g1, g2] at e
  exact e

theorem exists_ratio_unit : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  intro X' Z Z' i' p' L' N hL' hN w hw V' V a b ha hb O hO hO'
  let W : L'.ι × N.ι → Z'.Opens := fun q ↦ O ⊓ (i' ⁻¹ᵁ (V' ⊓ L'.U q.1) ⊓ p' ⁻¹ᵁ (V ⊓ N.U q.2))
  have hW : ∀ q, W q ≤ O := fun q ↦ inf_le_left
  have hWw : ∀ q, W q ≤ (N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1) := fun q x hx ↦
    ⟨mem_pull.2 hx.2.2.2, mem_pull.2 hx.2.1.2⟩
  have hWb : ∀ q, W q ≤ p' ⁻¹ᵁ (V ⊓ N.U q.2) := fun q x hx ↦ hx.2.2
  have hWa : ∀ q, W q ≤ i' ⁻¹ᵁ (V' ⊓ L'.U q.1) := fun q x hx ↦ hx.2.1
  let u : ∀ q, Γ(Z', W q)ˣ := fun q ↦ res (hWb q) (pullU p' _ (b q.2)) *
    (res (hWw q) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) * res (hWa q) (pullU i' _ (a q.1)))⁻¹
  have gu : ∀ q, ∀ x ∈ W q, gm (𝟙 Z') x (W q) (u q) = gm p' x _ (b q.2) *
      (gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1)) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) *
        gm i' x _ (a q.1))⁻¹ := by
    intro q x hx
    simp only [u, map_mul, map_inv]
    rw [gm_rp₁ p' x _ _ (hWb q) hx, gm_rp₁ i' x _ _ (hWa q) hx]
    exact congrArg (fun t ↦ _ * (t * _)⁻¹) (gm_res (𝟙 Z') x (hWw q) hx _)
  have cover : O ≤ iSup W := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_chart hL' (i' x)
    obtain ⟨l, hl⟩ := exists_chart hN (p' x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(k, l), hx, ⟨hO hx, hk⟩, ⟨hO' hx, hl⟩⟩
  obtain ⟨s, hs⟩ := glue_unit O W hW cover u (by
    rintro ⟨k, l⟩ ⟨k', l'⟩ x hx
    rw [gu _ x hx.1, gu _ x hx.2]
    have hx1 := hx.1
    have hx2 := hx.2
    rw [locGen_gm hb p' x l l' hx1.2.2.1 hx1.2.2.2 hx2.2.2.2, locGen_gm ha i' x k k' hx1.2.1.1 hx1.2.1.2 hx2.2.1.2,
      iso_gm hw x k k' l l' hx1.2.1.2 hx2.2.1.2 hx1.2.2.2 hx2.2.2.2]
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _)
  refine ⟨s, fun z k l hz hk hl ↦ ?_⟩
  have hzW : z ∈ W (k, l) := ⟨hz, ⟨hO hz, hk⟩, ⟨hO' hz, hl⟩⟩
  have e := gu (k, l) z hzW
  rw [← hs (k, l), gm_res _ z _ hzW] at e
  rw [e]
  exact comm_aux₂ _ _ _

end GlobalTheory.Pinch
