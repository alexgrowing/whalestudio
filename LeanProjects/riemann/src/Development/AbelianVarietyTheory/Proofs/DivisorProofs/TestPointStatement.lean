import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

namespace GlobalTheory.DetHT.TestPt

theorem spm_spm {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] (φ : R →+* S) (ψ : S →+* S') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem exists_chart {X : Scheme.{0}} {K : Type} [Field K] (z : Sp K ⟶ X) :
    ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (φ : R →+* K), IsOpenImmersion ξ ∧ spMap φ ≫ ξ = z := by
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (z q)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hr : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    have : q' = q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU'.fromSpec z hr : Sp K ⟶ Spec Γ(X, U))
  refine ⟨Γ(X, U), inferInstance, hU'.fromSpec, φ.hom, inferInstance, ?_⟩
  have : spMap φ.hom = IsOpenImmersion.lift hU'.fromSpec z hr := hφ
  rw [this]
  exact IsOpenImmersion.lift_fac _ _ _

theorem exists_finite_subfield {R F C : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field F] [CharZero F] [Field C]
    [Algebra F C] {K : Type} [Field K] (k : K →+* C) (hK : ∀ a : K, IsAlgebraic ℤ a) (φ₀ : R →+* K) :
    ∃ L : IntermediateField F C, FiniteDimensional F L ∧ ∀ a, (k.comp φ₀) a ∈ L := by
  have hφ : ∀ a, IsAlgebraic ℤ ((k.comp φ₀) a) := fun a => (hK (φ₀ a)).algHom k.toIntAlgHom
  generalize k.comp φ₀ = φ at hφ ⊢
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  refine ⟨IntermediateField.adjoin F (φ '' (s : Set R)), ?_, fun a => ?_⟩
  · haveI : Finite (φ '' (s : Set R)) := (s.finite_toSet.image φ).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    exact ((hφ a).extendScalars (S := F) (algebraMap ℤ F).injective_int).isIntegral
  · have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B)
    (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

theorem exists_integral_point {A : Type} [CommRing A] [Module.Finite ℤ A] {X : Scheme.{0}} (s : X ⟶ Sp A)
    (hs : IsProper s) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (k : K →+* ℂ_[p]) (hK : ∀ a : K, IsAlgebraic ℤ a)
    (z : Sp K ⟶ X) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO ≫ yT = spMap k ≫ z := by
  obtain ⟨R, _, ξ, φ, hξ, rfl⟩ := exists_chart z
  let f : A →+* R := (Spec.preimage (ξ ≫ s)).hom
  have hf : spMap f = ξ ≫ s := Spec.map_preimage (ξ ≫ s)
  letI : Algebra A R := f.toAlgebra
  haveI : Algebra.FiniteType A R := by
    have h : LocallyOfFiniteType (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let T₀ : CDVR := ⟨ℤ_[p]⟩
  have hT₀ : T₀.FinRes := Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  let g₀ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have hg₀ : ∀ a, g₀ a ∈ 𝓞_ℂ_[p] := fun a => by
    rw [GlobalTheory.CdvrLiftCp.mem_int_iff']
    show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  have hg₀i : Function.Injective g₀ :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  let kO₀ : T₀.V →+* 𝓞_ℂ_[p] := g₀.codRestrict 𝓞_ℂ_[p] hg₀
  let k₀ : T₀.Fr →+* ℂ_[p] := IsFractionRing.lift (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i
  have hk₀ : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO₀ a) = k₀ (algebraMap T₀.V T₀.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i a).symm
  letI : Algebra T₀.Fr ℂ_[p] := k₀.toAlgebra
  haveI : CharZero T₀.Fr := algebraRat.charZero _
  obtain ⟨L, hL, hmem⟩ := exists_finite_subfield (F := T₀.Fr) k hK φ
  let φL : R →+* L := (k.comp φ).codRestrict L hmem
  let kL : L →+* ℂ_[p] := L.val.toRingHom
  have hφL : kL.comp φL = k.comp φ := rfl
  obtain ⟨T', -, -, ψ, kO', hfin, hinj, -, -, hkO', hint⟩ :=
    GlobalTheory.CdvrLiftCp.exists_cdvr_lift p T₀ hT₀ kO₀ k₀ hk₀ L kL (fun a => rfl)
  obtain ⟨β', hβ'⟩ := hint A (φL.comp f) (fun a => by
    rw [← GlobalTheory.CdvrLiftCp.mem_int_iff']
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral 𝓞_ℂ_[p] ((kL.comp (φL.comp f)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom 𝓞_ℂ_[p]) _ (RingHom.ext_int _ _) h1
    exact (PadicComplexInt.integers p).mem_of_integral h2)
  have hring : (ψ.toRingHom.comp φL).comp f = (algebraMap T'.V (FractionRing T'.V)).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  obtain ⟨yT, hyT⟩ := exists_extend s hs (V := T'.V) (spMap (ψ.toRingHom.comp φL) ≫ ξ) (spMap β') (by
    rw [Category.assoc, ← hf, spm_spm, spm_spm, hring])
  refine ⟨T', kO', yT, hfin, hinj, ?_⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' =
      (kL.comp ψ.symm.toRingHom).comp (algebraMap T'.V (FractionRing T'.V)) := RingHom.ext hkO'
  have hid : (kL.comp ψ.symm.toRingHom).comp (ψ.toRingHom.comp φL) = k.comp φ := by
    rw [← hφL]
    ext a
    simp
  rw [← Category.assoc, spm_spm, hrk, ← spm_spm, Category.assoc, ← hyT, ← Category.assoc, spm_spm, hid,
    ← Category.assoc, spm_spm]

end GlobalTheory.DetHT.TestPt

namespace GlobalTheory.DetHT

theorem testPtSt : TestPtSt := by
  intro E _ _ _ H Dw l Xo c Z p _ _ P hP
  obtain ⟨K, _, k, z, hK, hz⟩ := hP
  obtain ⟨T, kO, yT, hT, hkO, h⟩ :=
    TestPt.exists_integral_point Z.s (projProper _ _ _ Z.proj) p k hK (z ≫ Z.j)
  refine ⟨spMap kO ≫ yT, ?_, T, kO, yT, hT, hkO, rfl⟩
  rw [h, hz, Category.assoc]

end GlobalTheory.DetHT

end
