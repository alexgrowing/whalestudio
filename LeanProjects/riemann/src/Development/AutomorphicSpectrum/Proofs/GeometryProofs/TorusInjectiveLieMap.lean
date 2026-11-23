import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletionStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsClosed

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem exists_transport (u : splitTorus S X ⟶ G) {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (e : a = a')
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk a' ⟶ splitTorus S X, (∀ χ, charVal t' χ = charVal t χ) ∧ (t' ≫ u = 1 → t ≫ u = 1) := by
  subst e
  exact ⟨t, fun _ => rfl, id⟩

theorem killsOver_comp (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B B' : Type} [CommRing B] [CommRing B']
    (b : Sp B ⟶ S) (c : B →+* B') (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  have e : spMap g ≫ spMap c ≫ b = spMap (g.comp c) ≫ b := by
    rw [← Category.assoc, spMap_comp_eq]
  obtain ⟨t', h1, h2⟩ := exists_transport u e t
  exact h2 (h A (g.comp c) t' fun y hy => by rw [h1]; exact ht y hy)

theorem killsOver_pow (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) {R : Type} [CommRing R]
    [IsLocalRing R] (b : Sp R ⟶ S) (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) (n : ℕ) :
    KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b) := by
  induction n with
  | zero =>
    let c : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha))
    have hc : c.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext x; rfl
    have key := killsOver_comp u Y _ c h
    rw [← Category.assoc, spMap_comp_eq, hc] at key
    exact key
  | succ n ih =>
    have hJ : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≠ ⊤ := by
      intro e
      have h1 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R :=
        Ideal.pow_le_self (by omega)
      rw [e] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h1)
    haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 hJ
    haveI : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _)
    have hI : I ^ 2 = ⊥ := by
      simp only [I]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ _ I hI ?_
    let c : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)) →+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
    have hc : c.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _) := by
      ext x; rfl
    have key := killsOver_comp u Y _ c ih
    rw [← Category.assoc, spMap_comp_eq, hc, ← spMap_comp_eq, Category.assoc] at key
    exact key

theorem diff_injective_mod_pi : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro R K _ _ _ _ _ _ S b G _ _ X _ _ u _ hK M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient S G X u (IsLocalRing.ResidueField R)
    (spMap (IsLocalRing.residue R) ≫ b) M hM δ hne hδ
  have hR := GlobalTheory.T.killsOver_of_adic_completion S G X u ψ.ker R b (killsOver_pow u ψ.ker b hk)
  have hKk := killsOver_comp u ψ.ker b (algebraMap R K) hR
  haveI := Fact.mk hl
  obtain ⟨-, -, h1, -, hex, -⟩ := GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra K (ZMod l))
    (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ spMap (algebraMap R K) ≫ b)
  let w : Multiplicative X →* AddMonoidAlgebra K (ZMod l) :=
    (AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)
  obtain ⟨t, ht⟩ := hex w
  have hu : t ≫ u = 1 := hKk _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t fun y hy => by
    rw [ht]
    have hy0 : ψ y = 0 := hy
    simp [w, hy0, AddMonoidAlgebra.one_def]
  have ht1 := hK _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t hu
  obtain ⟨χ, hχ⟩ := hψ 1
  have key := ht χ
  rw [ht1, h1] at key
  simp only [w, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, hχ] at key
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_left_inj one_ne_zero] at key
  exact zero_ne_one key

end GlobalTheory.CompanionTheory.Ar.TsClosed
