import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo.QCompPf

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N N₀ c : ℕ} {X X' X₁ X₂ : Scheme.{0}} {s : X ⟶ Sp R'}
  {s' : X' ⟶ Sp R'} {s₁ : X₁ ⟶ Sp R} {s₂ : X₂ ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'}
  {u₁ : Obj b N₀ s₁} {u₂ : Obj b N₀ s₂} {f : X ⟶ X₁} {g : X₁ ⟶ X₂} {e : X' ⟶ X}

private def after (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g) : QMap o u₂ (f ≫ g) c where
  φ := n.φ ≫ m.φ
  φ₂ := n.φ₂ ≫ m.φ₂
  cart := n.cart.comp m.cart
  sq := MapComp.isSquare_comp n.sq m.sq
  act x := by
    have h₁ := n.act x
    have h₂ := m.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (n.pol).trans o.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
    (MapComp.lbIso_pull_comp m.pol n.φ₂ rfl)
  eta y := by
    have h₁ := n.eta y
    have h₂ := m.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private def before (m : GObjMap o' o e) (n : QMap o u₁ f c) : QMap o' u₁ (e ≫ f) c where
  φ := m.φ ≫ n.φ
  φ₂ := m.φ₂ ≫ n.φ₂
  cart := m.cart.comp n.cart
  sq := MapComp.isSquare_comp m.sq n.sq
  act x := by
    have h₁ := m.act x
    have h₂ := n.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (m.pol).trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u₁.isLB _)
    (MapComp.lbIso_pull_comp n.pol m.φ₂ rfl)
  eta y := by
    have h₁ := m.eta (c • y)
    have h₂ := n.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private theorem factor (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g) :
    ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ := by
  have hw : n'.φ ≫ u₂.A.hom = (o.A.hom ≫ f) ≫ g := by
    rw [n'.cart.1.w, Category.assoc]
  let ℓ : o.A.left ⟶ u₁.A.left := m.cart.1.lift n'.φ (o.A.hom ≫ f) hw
  have hℓφ : ℓ ≫ m.φ = n'.φ := m.cart.1.lift_fst _ _ _
  have hℓs : ℓ ≫ u₁.A.hom = o.A.hom ≫ f := m.cart.1.lift_snd _ _ _
  obtain ⟨ℓ₂, hsq⟩ := MapComp.exists_isSquare (G := u₁.A) (G' := o.A) hℓs
  have hsq₂ : ℓ₂ ≫ m.φ₂ = n'.φ₂ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hsq m.sq)
    rw [hℓφ]
    exact n'.sq
  refine ⟨⟨ℓ, ℓ₂, ?_, hsq, ?_, ?_, ?_⟩, hℓφ.symm⟩
  · exact IsGrpPullback.cancel m.cart (IsGrpPullback.congr n'.cart rfl hℓφ.symm) hℓs
  · intro x
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, m.act x, ← Category.assoc, hℓφ]
      exact n'.act x
    · rw [Category.assoc, Category.assoc, hℓs, Over.w, hℓs, ← Category.assoc, Over.w]
  · exact LBIso.trans o.isLB (pull_isLB u₂.isLB _) (pull_isLB u₁.isLB _) n'.pol
      (MapComp.lbIso_pull_comp m.pol ℓ₂ hsq₂.symm).symm
  · intro y
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, n'.eta y, m.eta y, Category.assoc]
    · rw [Category.assoc, Category.assoc, hℓs, ← Category.assoc, Over.w]
      simp [Over.w]

private theorem bridge [IsIso f] (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c) :
    ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ := by
  haveI hiso : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  have hinvw : inv n.φ ≫ o.A.hom = u₁.A.hom ≫ inv f := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, n.cart.1.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : IsGrpPullback u₁.A o.A (inv f) (inv n.φ) :=
    IsGrpPullback.cancel n.cart
      (IsGrpPullback.congr (GlobalTheory.EndLoc.isGrpPullback_id u₁.A) (by simp) (by simp)) hinvw
  have hcart : IsGrpPullback u₁.A u₂.A g (inv n.φ ≫ n'.φ) :=
    IsGrpPullback.congr (IsGrpPullback.comp hinv n'.cart) (by simp) rfl
  obtain ⟨ψ₂, hψ⟩ := MapComp.exists_isSquare (G := o.A) (G' := u₁.A) hinvw
  have hid : Geo.Tor.IsSquare (𝟙 u₁.A.left) (𝟙 (u₁.A ⊗ u₁.A).left) := by
    constructor <;> simp
  have hψn : ψ₂ ≫ n.φ₂ = 𝟙 _ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hψ n.sq)
    rw [IsIso.inv_hom_id]
    exact hid
  refine ⟨⟨inv n.φ ≫ n'.φ, ψ₂ ≫ n'.φ₂, hcart, MapComp.isSquare_comp hψ n'.sq, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : Over.Hom.left (u₁.act.act x) ≫ inv n.φ = inv n.φ ≫ Over.Hom.left (o.act.act x) := by
      rw [IsIso.comp_inv_eq, Category.assoc, n.act x, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hx, Category.assoc, n'.act x, Category.assoc]
  · exact LBIso.trans u₁.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
      (GlobalTheory.SiegLower.lbIso_pull_id u₁.isLB)
      (LBIso.trans (pull_isLB u₁.isLB _) (pull_isLB o.isLB _) (pull_isLB u₂.isLB _)
        (MapComp.lbIso_pull_comp n.pol ψ₂ hψn.symm).symm
        (MapComp.lbIso_pull_comp n'.pol ψ₂ rfl))
  · intro y
    have hy : Over.Hom.left (u₁.eta y) = inv f ≫ Over.Hom.left (o.eta (c • y)) ≫ n.φ := by
      rw [n.eta y, IsIso.inv_hom_id_assoc]
    rw [hy]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, n'.eta y, IsIso.inv_hom_id_assoc]
  · simp

end UpperTheory.Gal.Int.Geo.QCompPf

open UpperTheory.Gal.Int.Geo.QCompPf in
theorem UpperTheory.quotient_map_comp : QComp := by
  intro q _ D R R' _ _ _ b gb N N₀ c X X₁ X₂ s s₁ s₂ o u₁ u₂ f g
  refine ⟨fun n m => ⟨after n m, rfl⟩, fun n' m => factor n' m, fun hf n n' => bridge n n', ?_⟩
  intro X' s' o' e m n
  exact ⟨before m n, rfl⟩
