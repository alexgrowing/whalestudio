import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientOfExactMiddleIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PropertyDescendsFiniteLengthToIrreducibleSubquotStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesInjectiveAndExactnessStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdSubquot

theorem subquot_dichotomy : ∀ (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q] (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A) (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ), τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ → IsSubquotient τ α ∨ IsSubquotient τ κ := GlobalTheory.T.isSubquotient_of_exact_middle_irreducible

theorem exists_irreducible_of_pred : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := GlobalTheory.T.property_descends_finiteLength_to_irreducible_subquotient

theorem parIndMap_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := GlobalTheory.T.parabolicInduction_preserves_injective_and_exactness

def extMapLeft {G H A B W : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup W] [Module ℂ W] {α : Representation ℂ G A} {β : Representation ℂ G B}
    (i : α.IntertwiningMap β) (ρ : Representation ℂ H W) :
    (extTensor α ρ).IntertwiningMap (extTensor β ρ) where
  toLinearMap := i.toLinearMap.rTensor W
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

def extMapRight {G H A B X : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) {α : Representation ℂ H A} {β : Representation ℂ H B}
    (i : α.IntertwiningMap β) :
    (extTensor ρ α).IntertwiningMap (extTensor ρ β) where
  toLinearMap := i.toLinearMap.lTensor X
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

theorem prod₂_exact_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A B W : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] (α : Representation ℂ (GL (Fin r) k) A) (β : Representation ℂ (GL (Fin r) k) B) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ α ρ₂).IntertwiningMap (prod₂ β ρ₂), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin r) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ β ρ₂).IntertwiningMap (prod₂ γ ρ₂), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t A B W _ _ _ _ _ _ α β ρ₂ i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapLeft i ρ₂) s) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapLeft i ρ₂) s) hi'
  refine ⟨parIndMap _ (compMap (extMapLeft i ρ₂) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapLeft q ρ₂) s), hex _ _ (compMap (extMapLeft q ρ₂) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.rTensor W) (q.toLinearMap.rTensor W) := by
    refine rTensor_exact W ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem prod₂_exact_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (X A B : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρ₁ : Representation ℂ (GL (Fin r) k) X) (α : Representation ℂ (GL (Fin t) k) A) (β : Representation ℂ (GL (Fin t) k) B) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ ρ₁ α).IntertwiningMap (prod₂ ρ₁ β), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin t) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ ρ₁ β).IntertwiningMap (prod₂ ρ₁ γ), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t X A B _ _ _ _ _ _ ρ₁ α β i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapRight ρ₁ i) s) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapRight ρ₁ i) s) hi'
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ i) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ q) s), hex _ _ (compMap (extMapRight ρ₁ q) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.lTensor X) (q.toLinearMap.lTensor X) := by
    refine lTensor_exact X ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem nontrivial_of_prod₂ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ₁ : Representation ℂ (GL (Fin r) k) X) (σ₂ : Representation ℂ (GL (Fin t) k) Y)
    (h : IsSubquotient π.π (prod₂ σ₁ σ₂)) : Nontrivial X ∧ Nontrivial Y := by
  obtain ⟨S, f, hf⟩ := h
  have := nontrivial_of_irreducible π.irr
  obtain ⟨w, hw⟩ := exists_ne (0 : π.V)
  obtain ⟨φ, rfl⟩ := hf w
  by_contra hc
  rw [not_and_or, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton] at hc
  have hsub : Subsingleton (TensorProduct ℂ X Y) := by
    rcases hc with hc | hc
    · haveI := hc; infer_instance
    · haveI := hc; infer_instance
  apply hw
  have h0 : φ = 0 := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext g
    exact Subsingleton.elim _ _
  rw [h0, map_zero]

theorem step_left {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₁ : HasFiniteLength ρ₁) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin r) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₁ ∧ IsSubquotient π.π (prod₂ σ ρ₂) := by
  refine exists_irreducible_of_pred (GL (Fin r) k) V ρ₁
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ σ ρ₂)) hf₁ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_left k r t Y Y' W σ σ' ρ₂ f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π σ ρ₂ h).1
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_left k r t B.toSubmodule A.toSubmodule W B.toRepresentation
      A.toRepresentation ρ₂ i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem step_right {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₂ : HasFiniteLength ρ₂) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin t) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₂ ∧ IsSubquotient π.π (prod₂ ρ₁ σ) := by
  refine exists_irreducible_of_pred (GL (Fin t) k) W ρ₂
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ ρ₁ σ)) hf₂ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_right k r t V Y Y' ρ₁ σ σ' f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π ρ₁ σ h).2
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_right k r t V B.toSubmodule A.toSubmodule ρ₁ B.toRepresentation
      A.toRepresentation i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem irreducible_subquotient_prod₂ : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (π : Irr k (r + t)), IsSmooth ρ₁ → IsSmooth ρ₂ → HasFiniteLength ρ₁ → HasFiniteLength ρ₂ → IsSubquotient π.π (prod₂ ρ₁ ρ₂) → ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSubquotient π₁.π ρ₁ ∧ IsSubquotient π₂.π ρ₂ ∧ IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro _hBZ k _ _ _ _ r t V W _ _ _ _ ρ₁ ρ₂ π h₁ h₂ hf₁ hf₂ hπ
  obtain ⟨Y₁, _, _, σ₁, hσ₁, hsq₁, hP₁⟩ := step_left π ρ₁ ρ₂ hf₁ hπ
  obtain ⟨Y₂, _, _, σ₂, hσ₂, hsq₂, hP₂⟩ := step_right π σ₁ ρ₂ hf₂ hP₁
  exact ⟨{ V := Y₁, π := σ₁, smooth := hsq₁.isSmooth h₁, irr := hσ₁ },
    { V := Y₂, π := σ₂, smooth := hsq₂.isSmooth h₂, irr := hσ₂ }, hsq₁, hsq₂, hP₂⟩

end GlobalTheory.ProdSubquot
