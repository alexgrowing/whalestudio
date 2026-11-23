import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSeparableOfSumMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_eq_evaluation_div {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (z : X.residueField x) : ∃ a b : Γ(X, U), z = X.evaluation U x hx a / X.evaluation U x hx b := by
  classical
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have he : ∀ c, X.evaluation U x hx c =
      (X.residue x).hom (algebraMap Γ(X, U) (X.presheaf.stalk x) c) := fun c => rfl
  obtain ⟨s, rfl⟩ : ∃ s, (X.residue x).hom s = z := IsLocalRing.residue_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  change s * algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U)) =
    algebraMap Γ(X, U) (X.presheaf.stalk x) a at hab
  have hb0 : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U))) :=
    IsLocalization.map_units _ b
  have hb := hb0.map (X.residue x).hom
  refine ⟨a, b, ?_⟩
  rw [he, he, eq_div_iff hb.ne_zero, ← map_mul (X.residue x).hom, hab]

theorem isFractionRing_residueField {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : Ideal Γ(X, U)) (hq : ∀ a, a ∈ q ↔ X.evaluation U x hx a = 0) :
    letI := (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
    IsFractionRing (Γ(X, U) ⧸ q) (X.residueField x) := by
  letI : Algebra (Γ(X, U) ⧸ q) (X.residueField x) :=
    (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
  have hmk : ∀ a, algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a) =
      X.evaluation U x hx a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hmk] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq a).2 hc)
  haveI : NoZeroDivisors (Γ(X, U) ⧸ q) :=
    hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    haveI : Nontrivial (Γ(X, U) ⧸ q) :=
      ⟨⟨0, 1, fun h => by simpa using congrArg (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) h⟩⟩
    exact nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨a, b, hz⟩ := exists_eq_evaluation_div hU x hx z
    by_cases hb : X.evaluation U x hx b = 0
    · refine ⟨(0, 1), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 1 =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 0
      rw [hz, hb, div_zero, zero_mul, map_zero]
    · have hb' : Ideal.Quotient.mk q b ≠ 0 := by
        intro h
        apply hb
        rw [← hmk, h, map_zero]
      refine ⟨(Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q b, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q b) =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a)
      rw [hz, hmk, hmk, div_mul_cancel₀ _ hb]
  · intro c d h
    exact ⟨1, by rw [hinj h]⟩

theorem residueFieldMap_finite_separable_of_tame {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (x : X) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (X'.residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable (X'.residueField (π x)) (X.residueField x) := by
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hx : π x ∈ W := hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : Γ) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let ev := X.evaluation (π ⁻¹ᵁ W) x hx
  let q : Ideal Γ(X, π ⁻¹ᵁ W) := RingHom.ker ev.hom
  have : q.IsPrime := RingHom.ker_isPrime _
  have hq : ∀ a, a ∈ q ↔ ev a = 0 := fun a ↦ Iff.rfl
  have hnat (a : Γ(X', W)) : π.residueFieldMap x (X'.evaluation W (π x) hx a) = ev (π.app W a) :=
    Scheme.evaluation_naturality_apply π x hx a
  have hp : ∀ a, a ∈ q.under Γ(X', W) ↔ X'.evaluation W (π x) hx a = 0 := fun a ↦ by
    rw [← map_eq_zero_iff _ (π.residueFieldMap x).hom.injective, hnat]
    rfl
  let := (Ideal.Quotient.lift q ev.hom fun a ha ↦ (hq a).1 ha).toAlgebra
  let := (Ideal.Quotient.lift _ (X'.evaluation W (π x) hx).hom fun a ha ↦ (hp a).1 ha).toAlgebra
  have := isFractionRing_residueField hU x hx q hq
  have := isFractionRing_residueField hW (π x) hx _ hp
  refine TameResidue.residue_finite_separable Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) q _ _ hnat fun hc ↦ ?_
  let Ω := AlgebraicClosure (X.residueField x)
  let jΩ : X.residueField x ⟶ CommRingCat.of Ω := CommRingCat.ofHom (algebraMap (X.residueField x) Ω)
  let y : Sp Ω ⟶ X := Spec.map (ev ≫ jΩ) ≫ hU.fromSpec
  have key (g : Γ) : g⁻¹ ∈ q.inertia Γ ↔ y ≫ (ρ g).hom = y := by
    have e : y ≫ (ρ g).hom = Spec.map ((ρ g).hom.appLE _ _ (hst g) ≫ ev ≫ jΩ) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
    have : Mono jΩ := ConcreteCategory.mono_of_injective _ jΩ.hom.injective
    rw [e, cancel_mono, Spec.map_inj, ← Category.assoc, cancel_mono]
    have e₂ (s) : g⁻¹ • s = (ρ g).hom.appLE _ _ (hst g) s := by
      change (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = _
      simp only [inv_inv]
    refine Iff.trans AddSubgroup.mem_inertia ⟨fun h ↦ ?_, fun h s ↦ ?_⟩
    · ext s
      have := (hq _).1 (h s)
      rw [map_sub, sub_eq_zero, e₂] at this
      exact this
    · refine (hq _).2 ?_
      rw [map_sub, sub_eq_zero, e₂]
      exact congr($h s)
  have hcard : Nat.card {g // y ≫ (ρ g).hom = y} = Nat.card (q.inertia Γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ (key g).symm.trans (inv_mem_iff (H := q.inertia Γ)))
  apply ht Ω y
  rw [hcard]
  have := congrArg jΩ.hom ((hq _).1 hc)
  simpa using this

theorem splitFibres_descend_of_tame_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G.left ⟶ G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → IsGrpPullback G G' π φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro Γ _ _ X X' ρ π G _ G' _ φ hq ht hφ hS x'
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  obtain ⟨_, hπ, hV⟩ := hq
  obtain ⟨x, rfl⟩ := π.surjective x'
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨h₁, h₂⟩ := residueFieldMap_finite_separable_of_tame ρ π hπ
    (fun W _ s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2) ht x
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let : Algebra (X'.residueField (π x)) k :=
    ((algebraMap (X.residueField x) k).comp (π.residueFieldMap x).hom).toAlgebra
  have : IsScalarTower (X'.residueField (π x)) (X.residueField x) k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨k, inferInstance, inferInstance, Module.Finite.trans (X.residueField x) k,
    Algebra.IsSeparable.trans _ (X.residueField x) k, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField (π x)) k)) ≫ X'.fromSpecResidueField (π x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    rfl
  rw [← key]
  generalize Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x = t at hGt
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' π)
  have : IsMonHom ((Over.pullback t).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₃ := isGt_of_iso ((Over.pullback t).mapIso e) hGt
  have : IsMonHom (pullCompIso t π G').symm.hom := inferInstanceAs (IsMonHom (pullCompIso t π G').inv)
  exact isGt_of_iso (pullCompIso t π G').symm h₃

end GlobalTheory
