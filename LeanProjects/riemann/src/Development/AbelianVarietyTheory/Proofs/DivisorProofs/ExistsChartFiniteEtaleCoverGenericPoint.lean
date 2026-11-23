import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section
namespace GlobalTheory.Poinc.Chart

theorem stalkMap_finite_of_chart (K A : Type) [Field K] [CommRing A] {X Y : Scheme.{0}} (q : Y ⟶ X) (j : Sp A ⟶ Y)
    (φ : A →+* K) [IsFinite q] [IsOpenImmersion j] (hφ : ∀ z : K, ∃ a c : A, z = φ a / φ c) (g : Sp K ⟶ X)
    (hg : g = spMap φ ≫ j ≫ q) : (g.stalkMap (genericPoint (Sp K))).hom.Finite := by
  rw [← Category.assoc] at hg
  subst hg
  have hpt : genericPoint (Sp K) = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  rw [hpt]
  have h1 : ((spMap φ ≫ j) ≫ q).stalkMap (closedPoint (CommRingCat.of K)) =
      Scheme.stalkClosedPointTo ((spMap φ ≫ j) ≫ q) ≫ (stalkClosedPointIso (CommRingCat.of K)).inv :=
    (Iso.eq_comp_inv _).2 rfl
  rw [h1]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2) ?_
  rw [Scheme.stalkClosedPointTo_comp]
  set τ := Scheme.stalkClosedPointTo (spMap φ ≫ j) with hτdef
  have h2 : q.stalkMap _ ≫ τ = (X.residue _ ≫ q.residueFieldMap _) ≫ Y.descResidueField τ := by
    rw [Scheme.residue_residueFieldMap, Category.assoc, Scheme.residue_descResidueField]
  have hτ : ∀ a : A, ∃ s, τ.hom s = φ a := by
    intro a
    have h3 : τ = j.stalkMap _ ≫ Scheme.stalkClosedPointTo (spMap φ) := Scheme.stalkClosedPointTo_comp _ _
    have h5 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K)))) ≫
        j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))) ≫ Scheme.stalkClosedPointTo (spMap φ) =
        CommRingCat.ofHom φ := by
      rw [IsIso.inv_hom_id_assoc, Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))))).hom a, ?_⟩
    rw [h3]
    exact congrArg (fun m => m.hom a) h5
  have hsurj : Function.Surjective (Y.descResidueField τ).hom := by
    intro z
    obtain ⟨a, c, rfl⟩ := hφ z
    obtain ⟨s, hs⟩ := hτ a
    obtain ⟨t, ht⟩ := hτ c
    refine ⟨Y.residue _ s / Y.residue _ t, ?_⟩
    rw [map_div₀, ← hs, ← ht]
    rfl
  rw [h2]
  exact (RingHom.Finite.of_surjective _ hsurj).comp ((GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite q _).comp
    (RingHom.Finite.of_surjective _ (Scheme.residue_surjective X _)))

theorem exists_chart : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro n N X Y sX sY q hn hN hsX hsY hq he hs η hη
  obtain ⟨η', hη', rfl⟩ := GlobalTheory.QuotTriple.genericPoints_subset_image (π := q) hη
  have hgen : (sY η').asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY η' := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap sY hb
    have h1 : closure {η'} ⊆ closure ({z'} : Set Y) := hz'.closure_subset
    have h2 : closure ({z'} : Set Y) ⊆ closure {η'} := hη'.2 isIrreducible_singleton.closure h1
    have h3 : η' ⤳ z' := specializes_iff_closure_subset.2 h2
    have : z' = η' := (hz'.antisymm h3).eq
    rw [← this, e]
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η') isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : LocallyOfFiniteType sY := inferInstance
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨η', hηU⟩
  have hP : hU.fromSpec P = η' := hU.fromSpec_primeIdealOf _
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1, hP]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω := ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) = q η'
    rw [hw, hP]
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    refine stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom)
      (fun z => ?_) _ (by rw [← e]; simp only [Category.assoc])
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨a, c, rfl⟩

end GlobalTheory.Poinc.Chart
