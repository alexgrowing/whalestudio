import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsEmptyOfEffCartierBot

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace SncBlowup

def IsSncCentre {X : Scheme.{0}} (E : Closeds X) (Z : X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support, ∃ (U : X.affineOpens) (hx : x ∈ U.1) (n : ℕ) (z : Fin n → Γ(X, U.1)) (J J' : Finset (Fin n)),
    FinalTheorems.Rsp (X.presheaf.stalk x) n (fun i => X.presheaf.germ U.1 x hx (z i)) ∧
      (Scheme.IdealSheafData.vanishingIdeal E).ideal U = Ideal.span {∏ j ∈ J, z j} ∧
      Z.ideal U = Ideal.span (z '' (J' : Set (Fin n)))

def totalTransform {X X' : Scheme.{0}} (π : X' ⟶ X) (Z : X.IdealSheafData) (E : Closeds X) : Closeds X' :=
  (E ⊔ Z.support).preimage π.continuous

inductive IsSncBlowupSeq {S X : Scheme.{0}} (g : X ⟶ S) (E : Closeds X) :
    ∀ {X' : Scheme.{0}}, (X' ⟶ X) → Closeds X' → Prop

  | id : IsSncBlowupSeq g E (𝟙 X) E

  | step {X₁ X₂ : Scheme.{0}} {s : X₁ ⟶ X} {E₁ : Closeds X₁} (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁) :
      IsSncBlowupSeq g E s E₁ → Smooth (s ≫ g) → Smooth (Z.subschemeι ≫ s ≫ g) → IsSncCentre E₁ Z →
      FinalTheorems.Blowup π Z → IsSncBlowupSeq g E (π ≫ s) (totalTransform π Z E₁)

theorem IsSncBlowupSeq.isSmoothBlowupSeq {S X X' : Scheme.{0}} {g : X ⟶ S} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') : IsSmoothBlowupSeq g Set.univ s := by
  induction h with
  | id => exact IsSmoothBlowupSeq.id
  | step Z π _ _ hZ _ hB ih => exact IsSmoothBlowupSeq.step Z π ih hZ (Set.subset_univ _) hB

section Line

open GlobalTheory.Principalise GlobalTheory.Principalise.Model

variable (k : Type) [Field k]

abbrev coord : Γ(Sp (Polynomial k), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial k))).commRingCatIsoToRingEquiv.symm Polynomial.X

instance smooth_line : Smooth (spMap (Polynomial.C : k →+* Polynomial k)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth k (Polynomial k))

end Line

end SncBlowup

open SncBlowup

def PrincipalisationCharZero : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
    SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
    ∀ (I : X.IdealSheafData) (E : Closeds X),
      (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
      (∀ x ∈ E, FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal E) x) →
      ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
        IsSncBlowupSeq g E s E' ∧ Smooth (s ≫ g) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
        IsIso (s ∣_ I.support.compl)

namespace SncBlowup

theorem not_subset_of_dense_compl {X : Type*} [TopologicalSpace X] [NoetherianSpace X] {T : Set X}
    (hT : Dense Tᶜ) : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T := fun C hC h => by
  obtain ⟨o, ho, hne, hoC⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨x, hx, hxT⟩ := hT.inter_open_nonempty o ho hne
  exact hxT (h (hoC hx))

theorem not_subset_of_ne_bot {X : Scheme.{0}} [IsIntegral X] {I : X.IdealSheafData} (hI : I ≠ ⊥) :
    ∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X) := by
  intro C hC hsub
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC
  subst hC
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [TopologicalSpace.Closeds.coe_top, Set.mem_univ, iff_true]
  exact hsub (Set.mem_univ x)

end SncBlowup

end GlobalTheory.CompanionTheory.Hypotheses₂
