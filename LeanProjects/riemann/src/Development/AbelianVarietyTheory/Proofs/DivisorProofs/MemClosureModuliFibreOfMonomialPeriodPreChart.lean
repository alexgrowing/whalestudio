import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFibreRegularLocalRing
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreDense

theorem isPrime_map_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] : (I.map φ).IsPrime := by
  let _ := φ.toAlgebra
  have : Module.Flat A R := hf
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : I.map (algebraMap A R) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans ((Ideal.map_mono hI).trans hm.le)))
  have : Nontrivial (R ⧸ I.map (algebraMap A R)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I.map (algebraMap A R)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  have hmap : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) = maximalIdeal _ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R))) Ideal.Quotient.mk_surjective,
      ← hm, Ideal.map_map, Ideal.map_map]
    rfl
  have : IsLocalHom (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    ((local_hom_TFAE _).out 0 2).2 hmap.le
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap
  have : IsDomain (R ⧸ I.map (algebraMap A R)) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

theorem exists_toStalk (o : Type) [CommRing o] (x : Sp o) : ∃ τ : CommRingCat.of o ⟶ (Sp o).presheaf.stalk x,
    (Sp o).fromSpecStalk x = Spec.map τ ∧ x.asIdeal.map τ.hom = maximalIdeal ((Sp o).presheaf.stalk x) := by
  have := x.isPrime
  let _ : Algebra o ((Spec (CommRingCat.of o)).presheaf.stalk x) := (StructureSheaf.toStalk o x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of o)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk o x
  exact ⟨StructureSheaf.toStalk o x, Spec.fromSpecStalk_eq' (CommRingCat.of o) x,
    IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (CommRingCat.of o)).presheaf.stalk x)⟩

theorem isPrime_fibre {o : Type} [CommRing o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Smooth s] {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hb : ξ ≫ s = spMap b)
    (he : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) : (((maximalIdeal R).comap b).map b).IsPrime := by
  have hreg := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal _ _ s (ξ (closedPoint R))
  have hp := isPrime_map_of_flat _ he.1 he.2.1
    ((maximalIdeal ((Sp o).presheaf.stalk (s (ξ (closedPoint R))))).map (s.stalkMap (ξ (closedPoint R))).hom)
  obtain ⟨τ, hτ, hmax⟩ := exists_toStalk o (s (ξ (closedPoint R)))
  have hc : τ ≫ s.stalkMap (ξ (closedPoint R)) ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    refine Eq.trans ?_ hb
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hτ, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    exact congrArg (· ≫ s) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ)
  have hx : (s (ξ (closedPoint R))).asIdeal = (maximalIdeal R).comap b :=
    congrArg (fun f : Sp R ⟶ Sp o => (f (closedPoint R)).asIdeal) hb
  have hb' : (Scheme.stalkClosedPointTo ξ).hom.comp ((s.stalkMap (ξ (closedPoint R))).hom.comp τ.hom) = b :=
    congrArg (fun q => q.hom) hc
  rwa [← hmax, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hb', hx] at hp

theorem mem_closure_fibre : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  intro o _ ζ g n F S s j _ φ BD d x _ _ h
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨-, -, hb, rfl, he, -⟩, ⟨ht, -, hj⟩, -⟩ := h
  have hq := isPrime_fibre s b ξ hb he
  let q : Sp R := (⟨((maximalIdeal R).comap b).map b, hq⟩ : PrimeSpectrum R)
  have hs : ∀ p : Sp R, s (ξ p) = spMap b p := fun p => congrArg (fun f : Sp R ⟶ Sp o => f p) hb
  have h₁ : ξ q ∈ Set.range j := by
    refine (hj q).2 fun hmem => ?_
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hq)).1 hmem
    have := ht.2 (Pi.single i 1) (Ideal.mem_sup_right (by simpa [Pi.single_apply] using hi)) i
    simp at this
  have h₂ : s (ξ q) = s (ξ (closedPoint R)) := by
    refine (hs q).trans (Eq.trans (PrimeSpectrum.ext (le_antisymm ?_ ?_)) (hs (closedPoint R)).symm)
    · exact Ideal.comap_mono (f := b) (Ideal.map_comap_le (f := b) (K := maximalIdeal R))
    · exact Ideal.le_comap_map (f := b) (I := (maximalIdeal R).comap b)
  have h₃ : ξ q ⤳ ξ (closedPoint R) := (specializes_closedPoint (R := R) q).map ξ.continuous
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_inter h₁ h₂)) (specializes_iff_mem_closure.1 h₃)

end GlobalTheory.FibreDense
