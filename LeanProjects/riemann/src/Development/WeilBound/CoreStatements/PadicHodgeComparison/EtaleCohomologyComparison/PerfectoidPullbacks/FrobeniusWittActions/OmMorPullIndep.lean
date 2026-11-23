import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.IterG

theorem omMor_pull_indep {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (mm : GlobalTheory.LogCris.Mor L L' σ)
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} (σ₀ σ₁ : Λ →+* Λ) (h₀ : ∀ a, σ (c a) = c' (σ₀ a))
    (h₁ : ∀ a, σ (c a) = c' (σ₁ a)) (j : ℕ) (x : CH.H (B.OM L c) j) :
    (B.omMor (c := c) (c' := c') mm σ₀ h₀).pull j x = (B.omMor (c := c) (c' := c') mm σ₁ h₁).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem pull_id {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (x : CH.H F n) :
    (CH.Mor.id F).pull n x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

def PtN (P : F.ptK κ ⟶ F.ptK κ) : ℕ → (F.ptK κ ⟶ F.ptK κ)
  | 0 => 𝟙 _
  | N + 1 => PtN P N ≫ P

theorem dpPow {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb) (N : ℕ) : IsDPMorphism b.γ b.γ (φb ^ N) := by
  induction N with
  | zero => exact (DPMorphism.id _).isDPMorphism
  | succ N ih =>
    rw [pow_succ]
    exact IsDPMorphism.comp _ ih dφ

theorem strN {φb : b.R →+* b.R} (P : F.ptK κ ⟶ F.ptK κ)
    (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r))) (N : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R) :
    ((PtN P N).app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ ((φb ^ N) r)) := by
  induction N generalizing r with
  | zero => rfl
  | succ N ih =>
    change (P.app B₀ ((PtN P N).app B₀ y)).1.1 (Ideal.Quotient.mk _ r) = _
    rw [str, ih, pow_succ, RingHom.mul_def, RingHom.comp_apply]

theorem hcN {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {φb : b.R →+* b.R} {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a))
    (N : ℕ) (a : Λ) : (φb ^ N) (c a) = c ((σ₀ ^ N) a) := by
  induction N generalizing a with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, pow_succ, RingHom.mul_def, RingHom.mul_def, RingHom.comp_apply, RingHom.comp_apply, hc, ih]

variable (ht) in

def morN {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb)
    (P : F.ptK κ ⟶ F.ptK κ) (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a)) (N : ℕ) :
    CH.Mor (B.OM (F.cr b ht κ) c) (B.OM (F.cr b ht κ) c) (σ₀ ^ N) :=
  B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (φb ^ N) rfl (dpPow dφ N) (PtN P N) (strN P str N))
    (σ₀ ^ N) (hcN hc N)

variable (ht) in

def mor1 {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb)
    (P : F.ptK κ ⟶ F.ptK κ) (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a)) : CH.Mor (B.OM (F.cr b ht κ) c) (B.OM (F.cr b ht κ) c) σ₀ :=
  B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) φb rfl dφ P str) σ₀ hc

theorem iter_pull {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb)
    (P : F.ptK κ ⟶ F.ptK κ) (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a)) (j N : ℕ) (x : CH.H (B.OM (F.cr b ht κ) c) j) :
    (⇑((mor1 ht c dφ P str hc).pull j))^[N] x =
      (morN ht c dφ P str hc N).pull j x := by
  induction N generalizing x with
  | zero =>
    have h0 : ∀ a, (φb ^ 0) (c a) = c (RingHom.id Λ a) := fun _ => rfl
    refine Eq.symm ((omMor_pull_indep _ _ (RingHom.id _) _ h0 j x).trans ?_)
    refine (cr_pull_eq (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (φb ^ 0) rfl (dpPow dφ 0) (PtN P 0)
        (strN P str 0)) (RingHom.id _) h0) (CH.Mor.id _)
      (fun T => crHom (RingHom.id _) (fun _ => rfl) (DPMorphism.id _).isDPMorphism fun h => pt_id _ h _)
      (fun _ _ => rfl) (fun _ _ => rfl) j x).trans ?_
    exact pull_id _ j x
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih]
    have : RingHomCompTriple σ₀ (σ₀ ^ N) (σ₀ ^ (N + 1)) := ⟨by rw [pow_succ, RingHom.mul_def]⟩
    refine (pull_pull (σ₀ ^ (N + 1)) (mor1 ht c dφ P str hc) (morN ht c dφ P str hc N) j x).trans ?_
    exact cr_pull_eq ((mor1 ht c dφ P str hc).comp (σ'' := σ₀ ^ (N + 1)) (morN ht c dφ P str hc N))
      (morN ht c dφ P str hc (N + 1))
      (fun T => crHom (RingHom.id _) (fun r => congrArg T.i (by rw [pow_succ, RingHom.mul_def, RingHom.comp_apply]))
        (DPMorphism.id _).isDPMorphism fun h => pt_id _ h _)
      (fun _ _ => rfl) (fun _ _ => rfl) j x

theorem comp_eq {κ₁ κ₂ : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)
    (ptA : F.ptK κ₂ ⟶ F.ptK κ₁) (dA : IsDPMorphism b.γ b.γ (RingHom.id b.R))
    (strA : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) (r : b.R),
      (ptA.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (RingHom.id b.R r)))
    (hA : ∀ a, RingHom.id b.R (c a) = c (RingHom.id Λ a))
    {σb : b.R →+* b.R} (dσ : IsDPMorphism b.γ b.γ σb) (ptB : F.ptK κ₁ ⟶ F.ptK κ₂)
    (strB : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₁).obj B₀) (r : b.R),
      (ptB.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (σb r)))
    (P : F.ptK κ₂ ⟶ F.ptK κ₂) (strP : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (σb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, σb (c a) = c (σ₀ a))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀), (ptB.app B₀ (ptA.app B₀ y)).1.2 = (P.app B₀ y).1.2)
    (j : ℕ) (x : CH.H (B.OM (F.cr b ht κ₂) c) j) :
    (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₁) (κ' := κ₂) (RingHom.id b.R) rfl dA ptA strA)
        (RingHom.id Λ) hA).pull j
      ((B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₂) (κ' := κ₁) σb rfl dσ ptB strB) σ₀ hc).pull j x) =
    (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₂) (κ' := κ₂) σb rfl dσ P strP) σ₀ hc).pull j x := by
  refine (pull_pull σ₀ (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₂) (κ' := κ₁) σb rfl dσ ptB strB) σ₀ hc) (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₁) (κ' := κ₂) (RingHom.id b.R) rfl dA ptA strA) (RingHom.id Λ) hA) j x).trans ?_
  exact cr_pull_eq ((B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₂) (κ' := κ₁) σb rfl dσ ptB strB) σ₀ hc).comp (σ'' := σ₀) (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₁) (κ' := κ₂) (RingHom.id b.R) rfl dA ptA strA) (RingHom.id Λ) hA)) (B.omMor (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (κ := κ₂) (κ' := κ₂) σb rfl dσ P strP) σ₀ hc)
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (DPMorphism.id _).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ T.y))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

end CrystallineSemistableComparison.IterG
