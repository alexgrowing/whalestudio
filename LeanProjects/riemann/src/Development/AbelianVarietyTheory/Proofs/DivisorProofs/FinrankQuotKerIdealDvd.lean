import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

variable {k : Type} [Field k] {A B : AbVar k}

def KerPow (f : A ⟶ B) (c : ℕ) (H : Type) [CommRing H] [Algebra k H] (i : ptOver k H ⟶ A.X) : Prop :=
  (i ≫ f.hom = 1 ∧ i ^ c = 1) ∧
    ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → x ^ c = 1 →
      ∃! φ : H →ₐ[k] R, spMap φ.toRingHom ≫ i.left = x.left

theorem finrank_eq_of_kerPow {f : A ⟶ B} {c c' : ℕ} {H H' : Type} [CommRing H] [Algebra k H] [CommRing H']
    [Algebra k H'] {i : ptOver k H ⟶ A.X} {i' : ptOver k H' ⟶ A.X} (h : KerPow f c H i) (h' : KerPow f c' H' i')
    (e : ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → (x ^ c = 1 ↔ x ^ c' = 1)) :
    Module.finrank k H = Module.finrank k H' := by
  obtain ⟨φ, hφ, -⟩ := h.2 H' i' h'.1.1 ((e H' i' h'.1.1).2 h'.1.2)
  obtain ⟨ψ, hψ, -⟩ := h'.2 H i h.1.1 ((e H i h.1.1).1 h.1.2)
  have h1 : ψ.comp φ = AlgHom.id k H := by
    obtain ⟨χ, -, hχ⟩ := h.2 H i h.1.1 h.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((ψ : H' →+* H).comp (φ : H →+* H')) ≫ i.left = i.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (ψ : H' →+* H) ≫ ·) hφ).trans hψ
    · change spMap (RingHom.id H) ≫ i.left = i.left
      rw [Cris.spMap_id, Category.id_comp]
  have h2 : φ.comp ψ = AlgHom.id k H' := by
    obtain ⟨χ, -, hχ⟩ := h'.2 H' i' h'.1.1 h'.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((φ : H →+* H').comp (ψ : H' →+* H)) ≫ i'.left = i'.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (φ : H →+* H') ≫ ·) hψ).trans hφ
    · change spMap (RingHom.id H') ≫ i'.left = i'.left
      rw [Cris.spMap_id, Category.id_comp]
  exact (AlgEquiv.ofAlgHom φ ψ h2 h1).toLinearEquiv.finrank_eq

theorem pow_eq_one_of_comp {f : A ⟶ B} {g : B ⟶ A} {N : ℕ} (h : f ≫ g = N • 𝟙 A) {T : Over (Sp k)}
    (x : T ⟶ A.X) (hx : x ≫ f.hom = 1) : x ^ N = 1 := by
  have e := congrArg (fun u : A ⟶ A => x ≫ u.hom) h
  simp only [comp_hom, nsmul_hom, id_hom] at e
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
  exact e.symm

section Tower

variable {p : ℕ} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B) (n : ℕ)

def kerPt : ptOver k (G.A n ⧸ kerIdeal ((t.map t' f.hom).app n)) ⟶ A.X :=
  spOver (Ideal.Quotient.mkₐ k (kerIdeal ((t.map t' f.hom).app n))) ≫ t.y n

theorem comp_eq_one_iff {R : Type} [CommRing R] [Algebra k R] (φ : G.A n →ₐ[k] R) :
    (spOver φ ≫ t.y n) ≫ f.hom = 1 ↔ kerIdeal ((t.map t' f.hom).app n) ≤ RingHom.ker φ := by
  rw [kerIdeal_le_ker_iff _ φ, Category.assoc, ← t.map_y t' f.hom n, ← Category.assoc, spOver_comp,
    t'.eq_one_iff]
  rfl

theorem kerPow_kerPt : KerPow f (p ^ n) _ (kerPt t t' f n) := by
  set I := kerIdeal ((t.map t' f.hom).app n)
  refine ⟨⟨(comp_eq_one_iff t t' f n _).2 ?_, (t.exists_iff n _).1 ⟨_, rfl⟩⟩, ?_⟩
  · exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  · intro R _ _ x hx hp
    obtain ⟨φ, hφ⟩ := t.surj n R x hp
    have hI : I ≤ RingHom.ker φ := (comp_eq_one_iff t t' f n φ).1 (hφ ▸ hx)
    refine ⟨Ideal.Quotient.liftₐ I φ (fun a ha => hI ha), ?_, fun ψ hψ => ?_⟩
    · change (spOver (Ideal.Quotient.liftₐ I φ (fun a ha => hI ha)) ≫ kerPt t t' f n).left = x.left
      rw [kerPt, ← Category.assoc, spOver_comp]
      exact congrArg Over.Hom.left ((congrArg (spOver · ≫ t.y n) (AlgHom.ext fun a => rfl)).trans hφ)
    · have h1 : spOver (ψ.comp (Ideal.Quotient.mkₐ k I)) ≫ t.y n = x := by
        rw [← spOver_comp, Category.assoc]
        exact Over.OverMorphism.ext hψ
      have h2 := t.inj n R _ _ (h1.trans hφ.symm)
      exact Ideal.Quotient.algHom_ext k (h2.trans (AlgHom.ext fun a => rfl))

end Tower

theorem finrank_quot_kerIdeal_dvd {p : ℕ} {G H : PDivGroup p k} (φ : G ⟶ H) (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (φ.app n)) ∣ p ^ (n * G.height) := by
  have h := finrank_eq_ker_mul_range k (G.A n) (H.A n) (φ.app n)
  have h2 : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    have h3 := G.fibreDim_eq n ⟨⊥, Ideal.isPrime_bot⟩
    rw [fibreDim, Module.finrank_baseChange] at h3
    exact h3
  exact ⟨_, h2 ▸ h⟩

end GlobalTheory.AV.KerPart
