import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionOfProperFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpread

theorem eq_one_of_point (O : Type) [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (n : ℕ) (hn : IsUnit (n : O)) (s : 𝟙_ (Over (Sp O)) ⟶ A)
    (hs : s ^ n = 1) (k : Type) [Field k] (x : Sp k ⟶ Sp O) (hx : toUnit (Over.mk x) ≫ s = 1) :
    s = 1 := by
  haveI := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing O
  have hn' : IsUnit (n : Γ(Sp O, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
    simpa using this
  obtain ⟨⟨-, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion (hG := hA) A hn'
  haveI := hA.proper
  haveI : IsSeparated ((mulN A n).left ≫ A.hom) := by
    rw [Over.w (mulN A n)]; infer_instance
  haveI : IsSeparated (mulN A n).left := IsSeparated.of_comp _ A.hom
  have hab : s ≫ mulN A n = (1 : 𝟙_ (Over (Sp O)) ⟶ A) ≫ mulN A n := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, hs, one_pow]
  have hj : toUnit (Over.mk x) ≫ s = toUnit (Over.mk x) ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A) := by
    rw [hx, MonObj.comp_one]
  exact Over.OverMorphism.ext (GlobalTheory.eq_of_connected_of_unramified_of_point (T := Sp O) (mulN A n).left
    (congrArg (·.left) hab) x (congrArg (·.left) hj))

end GlobalTheory.LevelSpread

namespace GlobalTheory.LevelSpread

theorem card_of_basis {I G : Type} [Fintype I] [Group G] {n : ℕ} (hn : n ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ n = 1)
    (ker : ∀ a, f a = 1 ↔ ∃ b, a = n • b) (onto : ∀ u : G, u ^ n = 1 → ∃ a, f a = u) :
    Nat.card {u : G // u ^ n = 1} = n ^ Fintype.card I := by
  haveI : NeZero n := ⟨hn⟩
  let F : (I → ZMod n) → {u : G // u ^ n = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hS : Function.Surjective F := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := onto u hu
    refine ⟨fun i => (a i : ZMod n), Subtype.ext ?_⟩
    show f (fun i => ((a i : ZMod n).val : ℤ)) = f a
    have hd : ∃ b, (fun i => ((a i : ZMod n).val : ℤ)) - a = n • b := by
      have : ∀ i, (n : ℤ) ∣ ((a i : ZMod n).val : ℤ) - a i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, sub_self]
      choose b hb using this
      exact ⟨b, funext fun i => by simpa using hb i⟩
    have e := add ((fun i => ((a i : ZMod n).val : ℤ)) - a) a
    rw [sub_add_cancel, (ker _).2 hd, _root_.one_mul] at e
    exact e
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hS⟩), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card]

theorem basis_at_every_point : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (g n : ℕ), IsUnit (n : O) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A)), (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ n = 1) → ∀ (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (x₀ : Sp k₀ ⟶ Sp O), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = n • b)) → (∀ u : Over.mk x₀ ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp O), (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ u : Over.mk x ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) := by
  intro O _ _ _ A _ _ hA g n hn lev add tors k₀ _ _ x₀ ker₀ onto₀ k _ _ x
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := O) (by simpa using hn)
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have pw : ∀ (b : Fin g ⊕ Fin g → ℤ) (m : ℕ), lev (m • b) = lev b ^ m := fun b m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, lev0]
    | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
  have hunit : ∀ (F : Type) [Field F] (p : Sp F ⟶ Sp O), (n : F) ≠ 0 := fun F _ p => by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    have := (hn.map φ.hom).ne_zero
    simpa using this
  have ker : ∀ a, toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b := fun a => by
    refine ⟨fun h => (ker₀ a).1 ?_, ?_⟩
    · rw [GlobalTheory.LevelSpread.eq_one_of_point O A hA n hn (lev a) (tors a) k x h, MonObj.comp_one]
    · rintro ⟨b, rfl⟩
      rw [pw, tors, MonObj.comp_one]
  refine ⟨ker, fun u hu => ?_⟩
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim O A hA
  have hsa := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have c₀ := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k₀ x₀ inferInstance n
    (hunit k₀ x₀)
  have c := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k x inferInstance n
    (hunit k x)
  have b₀ := card_of_basis hn0 (fun a => toUnit (Over.mk x₀) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    ker₀ onto₀
  exact GlobalTheory.SiegelOfPolarised.onto_torsion hn0 (fun a => toUnit (Over.mk x) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    (fun a => (ker a).1) (c.trans (c₀.symm.trans b₀)) u hu

end GlobalTheory.LevelSpread
