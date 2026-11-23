import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundaryStatement

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

open Classical in

theorem coboundary_on_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hdir T e p v he z hz
  have cov : ∀ (t : C') (u : T ⟶ G.obj t), IsUnit (mp F u e) →
      CovBy F (fun S ↦ ∃ (t' : C') (_ : t ⟶ t'), Nonempty (p ⟶ t') ∧ Nonempty (G.obj t' ⟶ S))
        (G.obj t) := by
    intro t u hu
    obtain ⟨w⟩ := he _ u hu
    obtain ⟨n, b, hb, h⟩ := hdir t p (G.obj t) (𝟙 _) w
    refine ⟨n, b, hb, fun i S' u' hi ↦ ?_⟩
    obtain ⟨t₃, ⟨a⟩, h2, h3⟩ := h i S' u' hi
    exact ⟨t₃, a, h2, h3⟩
  have up : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), Nonempty (p ⟶ t') → Nonempty (p ⟶ t'') :=
    fun _ _ _ _ b ⟨α⟩ ↦ ⟨α ≫ b⟩
  exact coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t) (fun u a ↦ u ≫ G.map a)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun t u ↦ IsUnit (mp F u e))
    (fun t _ ↦ Nonempty (p ⟶ t)) (fun _ _ _ a h ↦ isUnit_comp (G.map a) h)
    (fun t u hu ↦ sep_of_covBy F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c)
    (fun t t' _ a ↦ if h : Nonempty (p ⟶ t) then z p t t' v h.some a else 0)
    (fun t t' t'' u a b hp ↦ by
      have hp' := up t t t' (𝟙 t) a hp
      simp only [dif_pos hp, dif_pos hp']
      have k := hz p t t' t'' v hp.some a b
      rw [Subsingleton.elim (v ≫ G.map hp.some) u,
        Subsingleton.elim (hp.some ≫ a) hp'.some] at k
      change mp F (G.map b) (z p t t' v hp.some a) - z p t t'' v hp.some (a ≫ b) +
        z p t' t'' v hp'.some b = z t t' t'' u a b
      linear_combination k)

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
