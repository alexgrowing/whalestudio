import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep CategoryTheory
open scoped Matrix

namespace UpperTheory.V.Af.CohB

section Hom

def totCoh {Γ : Type} [Group Γ] (A : Rep.{0} ℂ Γ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology A q)

def Bdd (Γ : Type) [Group Γ] : Prop := ∃ c : ℕ, ∀ A : Rep.{0} ℂ Γ, totCoh A ≤ c * Module.rank ℂ A

def funRep {Γ : Type} [Group Γ] (X : Type) [MulAction Γ X] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ Γ (X → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f (γ⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

@[simp] theorem funRep_apply {Γ : Type} [Group Γ] (X : Type) [MulAction Γ X] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (γ : Γ) (f : X → Fin d → ℂ) (x : X) : funRep X ξ γ f x = ξ γ *ᵥ f (γ⁻¹ • x) := rfl

variable {Γ X Y I : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y]

def fib (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y) : SubMulAction ↥(MulAction.stabilizer Γ y) X where
  carrier := {x | p x = y}
  smul_mem' s x hx := by
    change p ((s : Γ) • x) = y
    rw [hp, show p x = y from hx]
    exact s.2

def part (c : X → I) (hc : ∀ (γ : Γ) x, c (γ • x) = c x) (i : I) : SubMulAction Γ X where
  carrier := {x | c x = i}
  smul_mem' γ x hx := by
    change c (γ • x) = i
    rw [hc]
    exact hx

abbrev fibRep (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y) {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥(MulAction.stabilizer Γ y) (↥(fib p hp y) → Fin d → ℂ) :=
  funRep ↥(fib p hp y) (ξ.comp (MulAction.stabilizer Γ y).subtype)

def toCo (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y) {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    (X → Fin d → ℂ) →ₗ[ℂ] ↥(Representation.coindV (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ)) where
  toFun f := ⟨fun g x => funRep X ξ g f x.1, fun s g => funext fun x => by
    change ξ ((s : Γ) * g) *ᵥ f (((s : Γ) * g)⁻¹ • x.1) = ξ (s : Γ) *ᵥ (ξ g *ᵥ f (g⁻¹ • ((s : Γ)⁻¹ • x.1)))
    rw [map_mul, mul_inv_rev, mul_smul, Matrix.mulVec_mulVec]⟩
  map_add' f f' := Subtype.ext (funext fun g => funext fun x => by simp [Matrix.mulVec_add])
  map_smul' c f := Subtype.ext (funext fun g => funext fun x => by simp [Matrix.mulVec_smul])

theorem toCo_apply (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y) {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (f : X → Fin d → ℂ) (g : Γ) (x : ↥(fib p hp y)) : (toCo p hp y ξ f).1 g x = ξ g *ᵥ f (g⁻¹ • x.1) := rfl

end Hom

def RankHomology : Prop :=
  ∀ (C : CochainComplex (ModuleCat.{0} ℂ) ℕ) (q : ℕ), Module.rank ℂ (C.homology q) ≤ Module.rank ℂ (C.X q)

def RankCohFree : Prop :=
  ∀ (Γ : Type) [Group Γ] (P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ)) (q r : ℕ),
    Nonempty (P.complex.X q ≅ Rep.free ℂ Γ (Fin r)) → ∀ A : Rep.{0} ℂ Γ,
      Module.rank ℂ (groupCohomology A q) ≤ r * Module.rank ℂ A

def BddOfFL : Prop := ∀ (Γ : Type) [Group Γ], UpperTheory.V.Published.IsFL Γ → Bdd Γ

def BddEquiv : Prop := ∀ (Γ Γ' : Type) [Group Γ] [Group Γ'], Nonempty (Γ ≃* Γ') → Bdd Γ → Bdd Γ'

def SumBound : Prop :=
  ∀ (Γ I : Type) [Group Γ] [Fintype I] (A : Rep.{0} ℂ Γ) (B : I → Rep.{0} ℂ Γ) (π : ∀ i, A ⟶ B i) (ι : ∀ i, B i ⟶ A),
    ∑ i, π i ≫ ι i = 𝟙 A → ∀ q : ℕ, Module.rank ℂ (groupCohomology A q) ≤ ∑ i, Module.rank ℂ (groupCohomology (B i) q)

def PartSplit : Prop :=
  ∀ (Γ X I : Type) [Group Γ] [MulAction Γ X] [Fintype I] (c : X → I) (hc : ∀ (γ : Γ) x, c (γ • x) = c x)
    (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ),
    ∃ (π : ∀ i, Rep.of (funRep X ξ) ⟶ Rep.of (funRep ↥(part c hc i) ξ))
      (ι : ∀ i, Rep.of (funRep ↥(part c hc i) ξ) ⟶ Rep.of (funRep X ξ)), ∑ i, π i ≫ ι i = 𝟙 _

def PartBound : Prop :=
  ∀ (Γ X I : Type) [Group Γ] [MulAction Γ X] [Fintype I] (c : X → I) (hc : ∀ (γ : Γ) x, c (γ • x) = c x)
    (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ),
    totCoh (Rep.of (funRep X ξ)) ≤ ∑ i, totCoh (Rep.of (funRep ↥(part c hc i) ξ))

def ToCoInj : Prop :=
  ∀ (Γ X Y : Type) [Group Γ] [MulAction Γ X] [MulAction Γ Y] (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y),
    (∀ x, ∃ g : Γ, g • p x = y) → ∀ (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ), Function.Injective (toCo p hp y ξ)

def ToCoSurj : Prop :=
  ∀ (Γ X Y : Type) [Group Γ] [MulAction Γ X] [MulAction Γ Y] (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y),
    (∀ x, ∃ g : Γ, g • p x = y) → ∀ (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ), Function.Surjective (toCo p hp y ξ)

def ShapiroFun : Prop :=
  ∀ (Γ X Y : Type) [Group Γ] [MulAction Γ X] [MulAction Γ Y] (p : X → Y) (hp : ∀ (γ : Γ) x, p (γ • x) = γ • p x) (y : Y),
    (∀ x, ∃ g : Γ, g • p x = y) → ∀ (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ),
      totCoh (Rep.of (funRep X ξ)) = totCoh (Rep.of (fibRep p hp y ξ))

def OrbBound : Prop :=
  ∀ (Γ Y : Type) [Group Γ] [MulAction Γ Y] (y : Y), Bdd ↥(MulAction.stabilizer Γ y) → ∃ c : ℕ,
    ∀ (X : Type) [MulAction Γ X] (p : X → Y), (∀ (γ : Γ) x, p (γ • x) = γ • p x) → (∀ x, ∃ g : Γ, g • p x = y) →
      ∀ D : ℕ, Cardinal.mk {x // p x = y} ≤ D → ∀ (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (funRep X ξ)) ≤ (c * D * d : ℕ)

def AbsBound : Prop :=
  ∀ (Γ Y : Type) [Group Γ] [MulAction Γ Y], (∃ T : Finset Y, ∀ y : Y, ∃ g : Γ, g • y ∈ T) →
    (∀ y : Y, Bdd ↥(MulAction.stabilizer Γ y)) → ∃ c : ℕ,
    ∀ (X : Type) [MulAction Γ X] (p : X → Y), (∀ (γ : Γ) x, p (γ • x) = γ • p x) →
      ∀ D : ℕ, (∀ y, Cardinal.mk {x // p x = y} ≤ D) → ∀ (d : ℕ) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (funRep X ξ)) ≤ (c * D * d : ℕ)

def FibCard : Prop :=
  ∀ (G : Type) [Group G] (U U' : Subgroup G) (h : U ≤ U'), U.relIndex U' ≠ 0 → ∀ y : G ⧸ U',
    Cardinal.mk {x : G ⧸ U // Subgroup.quotientMapOfLE h x = y} = (U.relIndex U' : ℕ)

def FinOrbAbs : Prop :=
  ∀ (G H : Type) [Group G] [Group H] (ι : H →* G) (Γ : Subgroup H) (U K : Subgroup G), Γ.FiniteIndex → U.relIndex K ≠ 0 →
    (∃ T : Finset G, ∀ g, ∃ h : H, ∃ t ∈ T, ∃ k ∈ K, g = ι h * t * k) →
    ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ u ∈ U, g = ι γ * t * u

def MinkRing : Prop :=
  ∀ (A : Type) [CommRing A] (n : ℕ), (∀ a : A, 3 * a = 0 → a = 0) → ∀ (r : ℕ), r.Prime →
    ∀ u : Matrix (Fin n) (Fin n) A, u ^ r = 1 → (∀ i j, (3 : A) ∣ (u - 1) i j) → ∀ (k : ℕ) i j, (3 : A) ^ k ∣ (u - 1) i j

section Arith

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

abbrev ratAf : GL (Fin n) F →* GL (Fin n) (Af F) := Matrix.GeneralLinearGroup.map (algebraMap F (Af F))

variable {F n} in

def arith (g : GL (Fin n) (Af F)) (U : Subgroup (GL (Fin n) (Af F))) : Subgroup (GL (Fin n) F) :=
  (U.comap (MulAut.conj g⁻¹).toMonoidHom).comap (ratAf F n)

variable {F n} in
theorem mem_arith {g : GL (Fin n) (Af F)} {U : Subgroup (GL (Fin n) (Af F))} {γ : GL (Fin n) F} :
    γ ∈ arith g U ↔ g⁻¹ * ratAf F n γ * g ∈ U := by
  simp [arith]

end Arith

def CardOhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 1 ≤ N → Finite (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) ∧
    Nat.card (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) ≤ N ^ Module.finrank ℚ F

def KLevIdx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ), 1 ≤ N → (KLev F n N).relIndex (KLev F n 1) ≠ 0 ∧
    (KLev F n N).relIndex (KLev F n 1) ≤ N ^ (Module.finrank ℚ F * (n * n))

def FinDC : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ T : Finset (GL (Fin n) (Af F)),
    ∀ g, ∃ h : GL (Fin n) F, ∃ t ∈ T, ∃ k ∈ KLev F n 1, g = ratAf F n h * t * k

def VanishThree : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ w : HeightOneSpectrum (𝓞 F),
    ∀ y : Af F, (∀ k : ℕ, ∃ z ∈ Ohat F, y = 3 ^ k * z) → pLoc F w y = 0

def KThreeLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ w : HeightOneSpectrum (𝓞 F), ∀ u ∈ KLev F n 3, ∀ r : ℕ, r.Prime → u ^ r = 1 →
    Matrix.GeneralLinearGroup.map (n := Fin n) (pLoc F w) u = 1

def TorsFree : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (g : GL (Fin n) (Af F)), ∀ γ ∈ arith g (KLev F n 3), IsOfFinOrder γ → γ = 1

def ArithOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), (KLev F n 1).comap (ratAf F n) =
    (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)).range

def ArithComm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Γ.FiniteIndex →
    ∀ (g : GL (Fin n) (Af F)) (U : Subgroup (GL (Fin n) (Af F))), IsOpen (U : Set (GL (Fin n) (Af F))) →
      IsCompact (U : Set (GL (Fin n) (Af F))) →
      Subgroup.Commensurable (Γ ⊓ arith g U) ((KLev F n 1).comap (ratAf F n))

end UpperTheory.V.Af.CohB
