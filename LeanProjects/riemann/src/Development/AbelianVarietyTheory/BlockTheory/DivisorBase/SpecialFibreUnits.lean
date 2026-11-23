import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

def lbPow {Z : Scheme.{0}} (D : LB Z) (M : ℕ) : LB Z where
  ι := D.ι
  U := D.U
  g := fun i j => D.g i j ^ M

def constUnit {A : Type} [CommRing A] {T : Scheme.{0}} (p : T ⟶ Spec (.of A)) (a : Aˣ) :
    Γ(T, ⊤)ˣ :=
  Units.map p.appTop.hom.toMonoidHom
    (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom a)

section Fibres

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))

def specialι : specialFibre f ⟶ Z := pullback.fst _ _

def reducedSpecialFibre : Scheme.{0} := (specialFibre f).nilradical.subscheme

def reducedSpecialι : reducedSpecialFibre f ⟶ Z :=
  (specialFibre f).nilradical.subschemeι ≫ specialι f

def genericFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))

def genericι : genericFibre f ⟶ Z := pullback.fst _ _

def genericStr : genericFibre f ⟶ Spec (.of (FractionRing O)) := pullback.snd _ _

def unifUnit (ϖ : O) (hϖ : Irreducible ϖ) : (FractionRing O)ˣ :=
  Units.mk0 (algebraMap O (FractionRing O) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero)

def Hyp (D : LB Z) : Prop :=
  IsIntegral Z ∧ (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧
    ConnectedSpace (specialFibre f) ∧ D.IsLB ∧
    ∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen

def PowEq (ϖ : O) (hϖ : Irreducible ϖ) (D : LB Z) (sig : (D.pull (genericι f)).Gen)
    (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen) : Prop :=
  ∀ j : PUnit → D.ι,
    sig.s j ^ M =
      res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ)) ^ n *
        res (LB.wchart_le D (fun _ : PUnit => genericι f) j PUnit.unit)
          (pullU (genericι f) (D.U (j PUnit.unit)) (gen.s (j PUnit.unit)))

def IsCoord {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (sig : (D.pull (genericι f)).Gen) (ybar : Spec (.of R) ⟶ Z)
    (y : Spec (.of C) ⟶ genericFibre f) (e : (D.pull ybar).Gen) (c : Cˣ) : Prop :=
  ∀ (j : PUnit → D.ι) (W : (Spec (.of C)).Opens)
    (h₁ : W ≤ y ⁻¹ᵁ (D.pull (genericι f)).U j)
    (h₂ : W ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ (D.pull ybar).U j),
    res h₁ (pullU y _ (sig.s j)) =
      res le_top (constUnit (𝟙 (Spec (.of C))) c) *
        res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _ (e.s j))

def ValConst (ϖ : O) (D : LB Z) (sig : (D.pull (genericι f)).Gen) (M : ℕ) (n : ℤ) : Prop :=
  ∀ (R C Γ₀ : Type) [CommRing R] [Field C] [Algebra R C] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation C Γ₀), v.Integers R →
    ∀ (φ : O →+* R), Function.Injective φ → IsLocalHom φ →
    ∀ (ybar : Spec (.of R) ⟶ Z), ybar ≫ f = Spec.map (CommRingCat.ofHom φ) →
    ∀ (y : Spec (.of C) ⟶ genericFibre f),
      y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar →
      (∃ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen ∧ IsCoord f D sig ybar y e c) ∧
      ∀ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen → IsCoord f D sig ybar y e c →
        v (c : C) ^ M = v (algebraMap R C (φ ϖ)) ^ n

end Fibres

def PropZ : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ (M : ℕ) (n : ℤ), 1 ≤ M ∧
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n

def PropZSlope : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ ρ : ℚ, ∀ (M : ℕ) (n : ℤ), 1 ≤ M → (n : ℚ) = M * ρ →
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n

theorem PropZSlope.propZ (h : PropZSlope) : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨ρ, hρ⟩ := h O ϖ hϖ Z f D hD sig hs
  refine ⟨ρ.den, ρ.num, ρ.den_pos, hρ _ _ ρ.den_pos ?_⟩
  rw [mul_comm]
  exact (Rat.mul_den_eq_num ρ).symm

def trivLB (Z : Scheme.{0}) : LB Z where
  ι := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem linComb_g_one {Y Z : Scheme.{0}} (D : LB Z) (h1 : ∀ a b, D.g a b = 1) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (i j : K → D.ι) :
    (LB.LinComb D φ ε).g i j = 1 := by
  have key : ∀ (W : Y.Opens) (k : K) (hh : W ≤ φ k ⁻¹ᵁ (D.U (i k) ⊓ D.U (j k))),
      res hh (pullU (φ k) _ (D.g (i k) (j k))) ^ (ε k) = 1 := by
    intro W k hh
    rw [h1, map_one, map_one, one_zpow]
  exact @Finset.prod_eq_one K (Γ(Y, D.wchart φ i ⊓ D.wchart φ j)ˣ) _ _ _ (fun k _ => key _ k _)

theorem normal_stalk (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (z : PrimeSpectrum A) : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk z) :=
  isIntegrallyClosed_of_isLocalization _ z.asIdeal.primeCompl
    z.asIdeal.primeCompl_le_nonZeroDivisors

theorem hyp_spec (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Hyp (𝟙 (Spec (.of O))) (trivLB _) := by
  refine ⟨inferInstance, fun z => ?_, inferInstance, inferInstance, ?_, ⟨?_, ?_, ?_⟩,
    ⟨⟨fun _ => 1⟩, ?_⟩⟩
  · exact normal_stalk O z
  · have : ConnectedSpace (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) := inferInstance
    let e := pullback.snd (𝟙 (Spec (.of O))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    exact (Scheme.homeoOfIso (asIso e)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso e)).symm.continuous
  · simp [trivLB]
  · intro i; exact map_one _
  · intro i j k
    change res _ 1 * res _ 1 = res _ 1
    simp
  · intro i j
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (linComb_g_one (trivLB _) (fun _ _ => rfl) _ _ i j) (map_one _)).trans (one_mul _)

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
