import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isTj_of_objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsTj r w j o₀ o₀' ψ₀ → IsTj r w j o o' ψ := by
  intro p _ D R _ b N r w j Y₀ Y i σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ hψ hfac h k _ _ _ x
  have hpu : IsUnit ((p : ℕ) : Γ(Sp k, ⊤)) := by
    have hk : IsUnit ((p : ℕ) : k) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀⟩ := hfac (Sp k) x hpu
  obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk x) x₀ hx₀
  obtain ⟨e', he', -⟩ := m'.exists_ptEquiv (Over.mk x) x₀ hx₀
  have hcomp : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = e' (g₀ ≫ ψ₀) := fun g₀ => by
    ext
    rw [Over.comp_left, he, he', Over.comp_left, Category.assoc, hψ, Category.assoc]
  have hker : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = 1 ↔ g₀ ≫ ψ₀ = 1 := fun g₀ => by
    rw [hcomp]; exact map_eq_one_iff _ e'.injective
  have hact : ∀ (g₀ : Over.mk x₀ ⟶ o₀.A) (c : D.O), e g₀ ≫ o.act.act c = e (g₀ ≫ o₀.act.act c) := fun g₀ c => by
    ext
    rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (g₀ : Over.mk x₀ ⟶ o₀.A), KilledBy o v (e g₀) ↔ KilledBy o₀ v g₀ :=
    fun v g₀ => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
  obtain ⟨h1, h2⟩ := h k x₀
  refine ⟨fun g hg hu => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := e.surjective g
    rw [hkill]
    rw [hker] at hg
    obtain ⟨n, hn⟩ := hu
    exact h1 g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
  · rw [← h2]
    exact Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
      change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
      rw [hker, hkill]).symm)

end GlobalTheory.UPel.HT.ES
