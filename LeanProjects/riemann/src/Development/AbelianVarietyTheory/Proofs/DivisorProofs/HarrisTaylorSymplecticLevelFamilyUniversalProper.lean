import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

def omegaMod {h : ℕ} (M : ℕ) (x y : Fin h ⊕ Fin h → ZMod M) : ZMod M :=
  ∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

def sympSimGrp (h M : ℕ) :
    Subgroup ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) where
  carrier := {g | ∃ m : (ZMod M)ˣ, ∀ x y, omegaMod M (g x) (g y) = m * omegaMod M x y}
  one_mem' := ⟨1, fun x y => by simp⟩
  mul_mem' := by
    rintro g g' ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m * m', fun x y => ?_⟩
    change omegaMod M (g (g' x)) (g (g' y)) = _
    rw [hm, hm', Units.val_mul, _root_.mul_assoc]
  inv_mem' := by
    rintro g ⟨m, hm⟩
    refine ⟨m⁻¹, fun x y => ?_⟩
    have hg := hm (g⁻¹ x) (g⁻¹ y)
    have e : ∀ z, g (g⁻¹ z) = z := fun z => by
      change (g * g⁻¹) z = z
      rw [mul_inv_cancel]; rfl
    rw [e, e] at hg
    rw [hg, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

instance sympSimGrp_finite (h M : ℕ) [NeZero M] : Finite (sympSimGrp h M) := by
  haveI : Finite ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) :=
    Finite.of_injective (fun g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M) =>
      (g : (Fin h ⊕ Fin h → ZMod M) → (Fin h ⊕ Fin h → ZMod M))) DFunLike.coe_injective
  infer_instance

def reduceMod {h : ℕ} (M : ℕ) (a : Fin h ⊕ Fin h → ℤ) : Fin h ⊕ Fin h → ZMod M := fun i => (a i : ZMod M)

def liftMod {h : ℕ} {M : ℕ} (x : Fin h ⊕ Fin h → ZMod M) : Fin h ⊕ Fin h → ℤ := fun i => ((x i).val : ℤ)

theorem reduceMod_liftMod {h M : ℕ} [NeZero M] (x : Fin h ⊕ Fin h → ZMod M) : reduceMod M (liftMod x) = x := by
  funext i
  simp [reduceMod, liftMod]

def sympTwist {h M : ℕ} {T : Type*} (g : sympSimGrp h M) (l : (Fin h ⊕ Fin h → ℤ) → T) :
    (Fin h ⊕ Fin h → ℤ) → T :=
  fun a => l (liftMod ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M a)))

def IsMultOf {h M : ℕ} (g : sympSimGrp h M) (n : ℕ) : Prop :=
  ∀ x y, omegaMod M ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x)
    ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y) = n * omegaMod M x y

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HarrisTaylorSymplecticLevelFamilyUniversalProperty (b : Base D R) (N h M : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
    (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
    ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

def SympActs {b : Base D R} {N h M : ℕ} {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (ρ : sympSimGrp h M → (X ⟶ X)) : Prop :=
  ∀ a, ρ a ≫ s = s ∧
    (∃ (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n ∧ σ (zetaAway M) = zetaAway M ^ n ∧
      ρ a ≫ s₁ = s₁ ≫ spMap σ) ∧
    ∃ m : ObjMap u u (ρ a), ∀ x, (sympTwist a lev x).left ≫ m.φ = ρ a ≫ (lev x).left

end GlobalTheory.UPel.HT
