import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

def LocStd (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (e + d)) φ ∧
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension e) ((Ideal.Quotient.mk I).comp φ)

def Std (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  φ.IsStandardSmoothOfRelativeDimension (e + d) ∧ ((Ideal.Quotient.mk I).comp φ).IsStandardSmoothOfRelativeDimension e

def IsCoord {e d : ℕ} {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
    (y : Fin e → A) : Prop :=
  (MvPolynomial.eval₂Hom φ (Sum.elim x y)).Etale ∧ I = Ideal.span (Set.range x)

def LeafLoc : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧
    ∃ (R : Type) (_ : CommRing R) (φ : R →+* Γ(P.X, V.1)), LocStd P.e d φ (P.ι.ker.ideal V)

def LeafShrink : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  LocStd e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    Std e d ((algebraMap A A').comp φ) (I.map (algebraMap A A'))

def LeafRank : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (I p : Ideal A) [p.IsPrime], I ≤ p →
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) = d

def LeafPick : Prop := ∀ (d : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] (p : Ideal A)
  [p.IsPrime], Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) = d →
  ∃ (x : Fin d → M) (f : A), f ∉ p ∧ ∀ m : M, f • m ∈ Submodule.span A (Set.range x)

def LeafSpan : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  (I p : Ideal A), p.IsPrime → I ≤ p → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  ∀ (x : Fin d → A) (f : A), (∀ j, x j ∈ I) → f ∉ p → (∀ a ∈ I, f * a ∈ Ideal.span (Set.range x)) →
  ∃ (y : Fin e → A) (g : A), g ∉ p ∧ ∀ ω : Ω[A⁄R],
    g • ω ∈ Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))

def LeafEt : Prop := ∀ (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A),
  Fintype.card ι = n → Algebra.IsStandardSmoothOfRelativeDimension n R A →
  Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤ →
  (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale

def LeafCoord : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  Std e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    ∃ (x : Fin d → A') (y : Fin e → A'), IsCoord ((algebraMap A A').comp φ) (I.map (algebraMap A A')) x y

def LeafSec : Prop := ∀ (A T : Type) [CommRing A] [CommRing T] (φ : A →+* T) (I : Ideal A) (μ : T →+* A ⧸ I), φ.Etale →
  μ.comp φ = Ideal.Quotient.mk I → ∃ t : T, μ t = 1 ∧ ∀ s : T, μ s = 0 → t * s ∈ I.map φ

def LeafPoly : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y →
  (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ))
    (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))).Etale

def LeafNbhd : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y → Chart d A I

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) : φ.Etale := by
  algebraize [φ]
  exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)

theorem chart_top (d : ℕ) (A : Type) [CommRing A] : Chart d A ⊤ := by
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  refine ⟨A ⧸ (⊤ : Ideal A), inferInstance, Ideal.Quotient.mk ⊤, MvPolynomial.constantCoeff,
    ⟨etale_of_subsingleton _, ?_⟩, etale_of_subsingleton _, Subsingleton.elim _ _, fun a => ?_⟩
  · have := (Ideal.Quotient.mk_surjective (I := (⊤ : Ideal A).map (Ideal.Quotient.mk (⊤ : Ideal A)))).subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · rw [Subsingleton.elim (_ - _) 0]; exact zero_mem _

theorem mem_basicOpen_of_notMem {X : Scheme.{0}} (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen f := by
  have h : V.2.primeIdealOf ⟨x, hx⟩ ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [V.2.fromSpec_preimage_basicOpen]; exact hf
  have h2 : V.2.fromSpec (V.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h
  rwa [V.2.fromSpec_primeIdealOf] at h2

theorem shrink {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V' : X.affineOpens) (_ : Algebra Γ(X, V.1) Γ(X, V'.1)), x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ IsLocalization.Away f Γ(X, V'.1) ∧
      I.ideal V' = (I.ideal V).map (algebraMap Γ(X, V.1) Γ(X, V'.1)) :=
  ⟨X.affineBasicOpen f, (inferInstance : Algebra Γ(X, V.1) Γ(X, X.basicOpen f)), mem_basicOpen_of_notMem V x hx f hf,
    X.basicOpen_le f, V.2.isLocalization_basicOpen f, (I.map_ideal_basicOpen V f).symm⟩

theorem off_case (d : ℕ) {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1)
    (h : ¬ I.ideal V ≤ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ V' : X.affineOpens, x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ (I.ideal V').FG ∧ Chart d Γ(X, V'.1) (I.ideal V') := by
  obtain ⟨f, hfI, hf⟩ := SetLike.not_le_iff_exists.mp h
  obtain ⟨V', _, hx', hle, _, hI⟩ := shrink I V x hx f hf
  have ht : I.ideal V' = ⊤ := by
    rw [hI]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI) (IsLocalization.Away.algebraMap_isUnit f)
  refine ⟨V', hx', hle, ?_, ?_⟩
  · rw [ht]; exact Ideal.fg_top _
  · rw [ht]; exact chart_top d _

theorem goal_of (hL : LeafLoc) (hS : LeafShrink) (hC : LeafCoord) (hN : LeafNbhd) : LeafChart := by
  intro d P x W hx
  obtain ⟨V, hxV, hVW, R, _, φ, hφ⟩ := hL d P x W hx
  by_cases h : P.ι.ker.ideal V ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V x hxV h
    exact ⟨V', a, b.trans hVW, c⟩
  obtain ⟨f, hf, H⟩ := hS P.e d R _ φ _ _ (V.2.primeIdealOf ⟨x, hxV⟩).isPrime h hφ
  obtain ⟨V₁, _, hx₁, hle₁, _, hI₁⟩ := shrink P.ι.ker V x hxV f hf
  have H₁ := H Γ(P.X, V₁.1)
  rw [← hI₁] at H₁
  by_cases h₁ : P.ι.ker.ideal V₁ ≤ (V₁.2.primeIdealOf ⟨x, hx₁⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V₁ x hx₁ h₁
    exact ⟨V', a, b.trans (hle₁.trans hVW), c⟩
  obtain ⟨g, hg, G⟩ := hC P.e d R _ _ _ _ (V₁.2.primeIdealOf ⟨x, hx₁⟩).isPrime h₁ H₁
  obtain ⟨V₂, _, hx₂, hle₂, _, hI₂⟩ := shrink P.ι.ker V₁ x hx₁ g hg
  obtain ⟨u, v, G₂⟩ := G Γ(P.X, V₂.1)
  rw [← hI₂] at G₂
  refine ⟨V₂, hx₂, hle₂.trans (hle₁.trans hVW), ?_, hN P.e d R _ _ _ u v G₂⟩
  rw [G₂.2]
  exact Submodule.fg_span (Set.finite_range u)

end LateralTheory.CohomologicalPurity.ChartCut
