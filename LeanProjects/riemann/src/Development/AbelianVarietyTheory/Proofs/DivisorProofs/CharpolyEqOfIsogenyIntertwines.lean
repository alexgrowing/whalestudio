import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem intCast_comp_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    (show A ⟶ A from ((n : End A))) ≫ u = n • u := by
  have h : ((n : End A)) = n • (𝟙 A : End A) := by
    rw [← zsmul_one]; rfl
  change (((n : End A)) : A ⟶ A) ≫ u = n • u
  rw [h, Preadditive.zsmul_comp, Category.id_comp]

theorem comp_intCast_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    u ≫ (show B ⟶ B from ((n : End B))) = n • u := by
  have h : ((n : End B)) = n • (𝟙 B : End B) := by
    rw [← zsmul_one]; rfl
  change u ≫ (((n : End B)) : B ⟶ B) = n • u
  rw [h, Preadditive.comp_zsmul, Category.comp_id]

theorem charpoly_eq_of_isogeny_intertwines : ∀ (K : Type) [Field K] (A B : AbVar K) (u : A ⟶ B) (f : End A) (g : End B), IsIsogeny u → (show A ⟶ A from f) ≫ u = u ≫ (show B ⟶ B from g) → charpoly f = charpoly g := by
  intro K _ A B u f g hu hfg
  obtain ⟨hdim, -, hpos, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B u hu
  have key : ∀ n : ℤ, deg (A := A) (B := A) ((n : End A) - f) = deg (A := B) (B := B) ((n : End B) - g) := by
    intro n
    have hc : (show A ⟶ A from ((n : End A) - f)) ≫ u = u ≫ (show B ⟶ B from ((n : End B) - g)) := by
      change (((n : End A)) - f : A ⟶ A) ≫ u = u ≫ (((n : End B)) - g : B ⟶ B)
      rw [Preadditive.sub_comp, Preadditive.comp_sub, intCast_comp_cpisog, comp_intCast_cpisog]
      exact congrArg (n • u - ·) hfg
    have h1 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A A B (show A ⟶ A from ((n : End A) - f)) u rfl hdim).2
    have h2 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A B B u (show B ⟶ B from ((n : End B) - g)) hdim rfl).2
    rw [hc, h2, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have hg : IsCharpoly g (charpoly f) := ⟨hm, by rw [hd, hdim], fun n => by rw [hev n, key n]⟩
  exact (GlobalTheory.T.abelianVarietyEndCharpoly_spec K B g).2 _ hg

end GlobalTheory.AV.AbVar
