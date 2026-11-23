import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceDifferentials

theorem main (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] (p : ℕ) [hpp : Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ NumberField.discr E) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (hm : (p : A) ∈ m) (O : Type) [CommRing O] [IsLocalRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (σ : E →+* Ω) :
    (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧
      ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : IsIntegral ℤ (σ (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := A)).1 h1
    exact ⟨algebraMap A O b, by rw [← IsScalarTower.algebraMap_apply, hb]⟩
  · set n : ℕ := (NumberField.discr E).natAbs with hn
    have hx : ((n : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
      rw [hn, ← NumberField.absNorm_differentIdeal E (𝓞 E)]
      exact Ideal.absNorm_mem _
    have hpn : ¬ p ∣ n := fun h => hp (Int.natCast_dvd.2 h)
    have hnm : ((n : ℕ) : A) ∉ m := by
      intro h
      have hc : IsCoprime (p : A) (n : A) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hpp.out).2 hpn)
      obtain ⟨u, v, huv⟩ := hc
      exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one m).2
        (huv ▸ m.add_mem (m.mul_mem_left u hm) (m.mul_mem_left v h)))
    have hu : IsUnit (algebraMap A O (n : A)) :=
      IsLocalization.map_units O (⟨(n : A), hnm⟩ : m.primeCompl)
    obtain ⟨o, ho⟩ := hu.exists_left_inv
    refine ⟨(n : 𝓞 E), hx, o, ?_⟩
    have h2 := congrArg (algebraMap O Ω) ho
    simp only [map_mul, map_natCast, map_one] at h2
    have h3 : σ (((n : ℕ) : 𝓞 E) : E) = (n : Ω) := by simp
    rw [h3, h2]

end PositivityTheory.Xgn.SequenceDifferentials

theorem PositivityTheory.Xgn.sequence_differentials_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hp A _ _ _ m _ hm O _ _ _ _ _ _ _ σ
  exact PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
