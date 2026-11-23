import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.PackingFacts

def zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    rw [div_add_div _ _ hb0 hb0']
    push_cast
    ring
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩

theorem mem_range_zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zp Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_adjoin_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin o T) : w ∈ Algebra.adjoin o' T := by
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem mem_adjoin_of_int (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin ℤ T) : w ∈ Algebra.adjoin o T :=
  mem_adjoin_of_range_le (o := ℤ) (o' := o) (fun n : ℤ => ⟨((n : ℤ) : o), by rw [map_intCast, eq_intCast]⟩) T hw

theorem isUnit_natCast {A O : Type} [CommRing A] [CommRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  have hbm : (b : A) ∉ m := by
    intro hbm
    have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
    have h1 : (1 : A) ∈ m := by
      rw [← huv]
      simp only [eq_intCast, Int.cast_natCast]
      exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)
  have := IsLocalization.map_units O (⟨(b : A), hbm⟩ : m.primeCompl)
  simpa using this

theorem exists_denom {o A O Ω : Type} [CommRing o] [CommRing A] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra A Ω]
    [Algebra A O] [Algebra O Ω] [IsScalarTower A O Ω] (M : Submonoid A) [IsLocalization M O] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) {w : Ω} (hw : w ∈ Algebra.adjoin O T) :
    ∃ s : M, w * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj M r
    refine ⟨s, ?_⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
    exact hA _
  | add x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x + y) * algebraMap A Ω ((b * b' : M) : A) =
        x * algebraMap A Ω b * algebraMap A Ω b' + y * algebraMap A Ω b' * algebraMap A Ω b := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (mul_mem hx (hA _)) (mul_mem hy (hA _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x * y) * algebraMap A Ω ((b * b' : M) : A) = x * algebraMap A Ω b * (y * algebraMap A Ω b') := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact mul_mem hx hy

theorem isIntegrallyClosed_of_denom {o O Ω : Type} [CommRing o] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra O Ω]
    (B : Subalgebra o Ω) (B' : Subalgebra O Ω) [IsIntegrallyClosed B] (hle : ∀ w ∈ B, w ∈ B')
    (hden : ∀ w ∈ B', ∃ s ∈ B, (∃ t ∈ B', s * t = 1) ∧ w * s ∈ B) : IsIntegrallyClosed B' := by
  let ψ : B →+* B' := (algebraMap B Ω).codRestrict _ fun s => hle _ s.2
  letI : Algebra B B' := ψ.toAlgebra
  let M : Submonoid B := (IsUnit.submonoid B').comap ψ
  haveI hloc : IsLocalization M B' := by
    refine ⟨fun s => s.2, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, ⟨t, ht, e⟩, hws⟩ := hden a a.2
      have hu : IsUnit (ψ ⟨s, hs⟩) := IsUnit.of_mul_eq_one (⟨t, ht⟩ : B') (Subtype.ext e)
      exact ⟨⟨⟨_, hws⟩, ⟨⟨s, hs⟩, hu⟩⟩, Subtype.ext rfl⟩
    · have h' : (r : Ω) = s := congrArg (fun z : B' => (z : Ω)) h
      rw [Subtype.ext h']
  have hM : M ≤ nonZeroDivisors B := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have hu : IsUnit (ψ s) := hs
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
  exact isIntegrallyClosed_of_isLocalization B' M hM

end PositivityTheory.Xgn.PackingFacts

open PositivityTheory.Xgn.PackingFacts in
theorem PositivityTheory.Xgn.torsion_packing_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ c' hc'
  haveI hch : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, -, -, -, hchart⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (zp Ω p) (mem_range_zp Ω p)
  obtain ⟨-, hic, hfr, x₀, hx₀, -⟩ := hchart c' hc'
  obtain ⟨-, -, -, hconst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  have eO := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := O) y c' hc'
  have eo := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := zp Ω p) y c' hc'
  have eZ := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := ℤ) y c' hc'
  have hr : ∀ a : zp Ω p, algebraMap (zp Ω p) Ω a ∈ (algebraMap O Ω).range := by
    intro a
    obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zp Ω p _).1 ⟨a, rfl⟩
    have hu := isUnit_natCast (O := O) m p hpm b hb
    refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
    rw [hab, map_mul, map_intCast, div_eq_mul_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
  have hle : ∀ w ∈ chartRing (zp Ω p) (mseg y) c', w ∈ CR O y c' := by
    intro w hw
    exact eO.ge (mem_adjoin_of_range_le hr _ (eo.le hw))
  have hA : ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin (zp Ω p) (Set.range fun j => mseg y j / mseg y c') := by
    intro a
    have h1 : algebraMap A Ω a ∈ chartRing ℤ (mseg y) c' := hconst c' hc' a
    rw [eZ] at h1
    exact mem_adjoin_of_int _ _ h1
  refine ⟨hch, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.FiniteType O (CR O y c') := by
      refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => mseg y j / mseg y c').toFinset, ?_⟩
      rw [Set.Finite.coe_toFinset]
      exact eO.symm
    exact Algebra.FiniteType.isNoetherianRing O _
  · refine isIntegrallyClosed_of_denom (chartRing (zp Ω p) (mseg y) c') (CR O y c') hle fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_denom m.primeCompl _ hA (eO.le hw)
    have hu := IsLocalization.map_units O s
    refine ⟨algebraMap A Ω s, eo.ge (hA _), ⟨algebraMap O Ω ↑hu.unit⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩, eo.ge hs⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu.mul_val_inv, map_one]
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, h, -, e⟩ := IsFractionRing.div_surjective (A := chartRing (zp Ω p) (mseg y) c') a
    exact ⟨⟨g, hle _ g.2⟩, ⟨h, hle _ h.2⟩, e.symm⟩
  · let ψ : chartRing (zp Ω p) (mseg y) c' →+* CR O y c' :=
      (algebraMap (chartRing (zp Ω p) (mseg y) c') Ω).codRestrict _ fun s => hle _ s.2
    refine ⟨spMap ψ ≫ x₀, ?_⟩
    have e : spMap (algebraMap (CR O y c') Ω) ≫ spMap ψ = spMap ((algebraMap (CR O y c') Ω).comp ψ) :=
      (Spec.map_comp _ _).symm
    rw [← Category.assoc, e]
    exact hx₀
