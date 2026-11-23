import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem harrisTaylor_heckeMap_comp_forgetLevel_general {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ) (hk : k.Coprime p) (hN3 : 3 ≤ N) (hNp : N.Coprime p)
    (hgg' : ∀ x, g (g' x) = k • x) (hg'g : ∀ x, g' (g x) = k • x) (hcc : c * c' = k ^ 2)
    (hc : (N * k * k).Coprime p)
    {S S₁ S₂ : Scheme.{0}} (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R)
    (u : Obj b N s) (u₁ : Obj b (N * k) s₁) (u₂ : Obj b (N * k * k) s₂) (π : S₁ ⟶ S) (π₁ : S₂ ⟶ S₁)
    (h₁ : π₁ ≫ s₁ = s₂)
    (o₂ : Obj b N s₁) (ψ₂ : u₁.A ⟶ o₂.A) (hH₂ : IsHecke g c k N u₁ o₂ ψ₂) (m₂ : ObjMap o₂ u π)
    (o₁ : Obj b (N * k) s₂) (ψ₁ : u₂.A ⟶ o₁.A) (hH₁ : IsHecke g' c' k (N * k) u₂ o₁ ψ₁)
    (m₁ : ObjMap o₁ u₁ π₁) :
    Nonempty (ObjMap (u₂.forget N ⟨k * k, by ring⟩ hc) u (π₁ ≫ π)) := by
  subst h₁
  obtain ⟨o₂', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ S₂ s₁ π₁ o₂
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base p D R b g c k N hk hN3 hNp S₁ S₂ s₁ π₁ u₁ o₂ ψ₂ o₁ o₂' hH₂ m₁ m
  obtain ⟨n⟩ := GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level p D R b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc S₂ (π₁ ≫ s₁) u₂ o₁ o₂'
    ψ₁ ψ' hH₁ hψ'
  obtain ⟨n₁⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n m
  obtain ⟨n₂⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n₁ m₂
  rw [Category.id_comp] at n₂
  exact ⟨n₂⟩

theorem heckeMap_comp_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  intro p _ D R _ b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F F₁ F₂ π π₁ hπ hπ₁
  obtain ⟨-, o₂, ψ₂, hH₂, ⟨m₂⟩⟩ := hπ
  obtain ⟨h₁, o₁, ψ₁, hH₁, ⟨m₁⟩⟩ := hπ₁
  exact harrisTaylor_heckeMap_comp_forgetLevel_general g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F.s F₁.s F₂.s F.univ F₁.univ F₂.univ π π₁ h₁
    o₂ ψ₂ hH₂ m₂ o₁ ψ₁ hH₁ m₁

end GlobalTheory.UPel.HT.Hecke
