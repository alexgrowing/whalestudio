import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam GlobalTheory.AbLaw GlobalTheory.Biadditive

namespace GlobalTheory.IsogenyBitriv

theorem triv_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {G : Type} [Monoid G] (F : G → (Y ⟶ X))
    (h₁ : Triv (L.pull (F 1)))
    (hm : ∀ x x', Triv (LB.LinComb L (K := Fin 3) ![F (x * x'), F x, F x'] ![1, -1, -1])) (x : G) (n : ℕ) :
    Triv (LB.LinComb L (K := Fin 2) ![F (x ^ n), F x] ![1, -(n : ℤ)]) := by
  induction n with
  | zero =>
    refine triv_of_formal hL h₁ fun U _ k => ?_
    simp [Fin.prod_univ_two]
  | succ n ih =>
    refine triv_of_formal hL (triv_mul (hm (x ^ n) x) ih) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_sum_type, pow_succ, zpow_add, mul_comm,
      mul_left_comm, _root_.mul_assoc]
    exact Additive.ofMul.injective (by simp only [ofMul_mul, ofMul_inv]; abel)

theorem triv_of_triv_pull_isogeny :
    ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro S _ A B _ _ _ _ ψ M N n hA hB hM hamp hN hψ hfin het hsurj _ hn hker h₁ h₂ h₃
  have hG : Out.GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨mA, -, -, sA⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have := hA.proper
  have := hB.smooth
  obtain ⟨ψ', hψ', e, -⟩ := GlobalTheory.HkFactor.exists_unique_factor S A B A ψ ((𝟙 A) ^ n) hA hB inferInstance hψ
    hfin het hsurj mA (fun k _ _ t x hx => by rw [MonObj.comp_pow, Category.comp_id]; exact hker k t x hx)
  have e' : ψ' ≫ ψ = (𝟙 B) ^ n := by
    have : Epi ψ.left := Flat.epi_of_flat_of_surjective ψ.left
    have : Epi ψ := Over.epi_of_epi_left ψ
    rw [← cancel_epi ψ, ← Category.assoc, e, MonObj.pow_comp, MonObj.comp_pow, Category.comp_id,
      Category.id_comp]
  have a₁ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift 1 y).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ B), Triv (N.pull (lift y 1).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have key : ∀ {T : Over S} (a : T ⟶ A) (y : T ⟶ B), Triv (N.pull (lift ((a ≫ ψ) ^ n) y).left) := by
    intro T a y
    have bi := biadditive_of_triv_axes hG S B M hB hM hamp N hN h₁ h₂ T
    have p₁ := triv_pow hN (fun x : T ⟶ B => (lift x y).left) (a₁ y) (fun x x' => (bi x x' y).1) (a ≫ ψ) n
    have p₂ := triv_pow hN (fun x : T ⟶ B => (lift (a ≫ ψ) x).left) (a₂ _)
      (fun x x' => (bi x x' (a ≫ ψ)).2) y n
    have p₃ : Triv (N.pull (lift (a ≫ ψ) (y ^ n)).left) := by
      have := triv_pull_comp h₃ (lift a (y ≫ ψ')).left
      rwa [← Over.comp_left, lift_map, Category.assoc, e', MonObj.comp_pow, Category.comp_id] at this
    refine triv_of_formal hN (triv_mul (triv_mul p₁ (triv_inv p₂)) p₃) fun U _ k => ?_
    simp [Fin.prod_univ_two, Fintype.prod_sum_type, _root_.mul_assoc]
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have hp : IsPullback (snd B B).left (fst B B).left B.hom B.hom :=
    (IsPullback.of_hasPullback B.hom B.hom).flip
  refine GlobalTheory.seesaw_reduced_of_dense hG S B M hB hM hamp B.left (B ⊗ B).left B.hom (snd B B).left
    (fst B B).left N hp hN ?_ (lift (𝟙 B) (1 : B ⟶ B)).left ?_ h₂
  · intro p
    refine subset_closure ?_
    have : Surjective ((𝟙 A ^ n) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
    obtain ⟨a, ha⟩ := ((𝟙 A ^ n) ≫ ψ).left.surjective p
    have hr : Set.range (A.left.fromSpecResidueField a) = {a} := Scheme.range_fromSpecResidueField _
    obtain ⟨z, hz⟩ := hr.ge rfl
    let j := A.left.fromSpecResidueField a
    let g := j ≫ ((𝟙 A ^ n) ≫ ψ).left
    refine ⟨A.left.residueField a, inferInstance, g, _, _, _, ⟨z, ?_⟩,
      IsPullback.of_hasPullback (fst B B).left g, ?_⟩
    · exact (congrArg (fun w => ((𝟙 A ^ n) ≫ ψ).left w) hz).trans ha
    · let ρ := pullback.fst (fst B B).left g
      let T : Over S := Over.mk (ρ ≫ (B ⊗ B).hom)
      let r : T ⟶ B ⊗ B := Over.homMk ρ rfl
      let b : T ⟶ A := Over.homMk (pullback.snd (fst B B).left g ≫ j) (by
        have c := congrArg (· ≫ B.hom) (pullback.condition (f := (fst B B).left) (g := g))
        simp only [g, Category.assoc, Over.w] at c
        exact (Category.assoc _ _ _).trans c.symm)
      have hr : r ≫ fst B B = (b ≫ ψ) ^ n := by
        have : (b ≫ ψ) ^ n = b ≫ (𝟙 A ^ n) ≫ ψ := by
          rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
        rw [this]
        apply Over.OverMorphism.ext
        exact pullback.condition.trans (Category.assoc _ _ _).symm
      have := key b (r ≫ snd B B)
      rw [← hr, lift_comp_fst_snd] at this
      exact this
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory.IsogenyBitriv
