import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackGeneratingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfRescaledPsiUnitOnStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitOpen

theorem zpow_mul_toNat {F : Type} [Field F] {x : F} (hx : x ≠ 0) (m : ℤ) :
    x ^ m * x ^ (-m).toNat = x ^ m.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have := Int.toNat_sub_toNat_neg m
  omega

theorem psiUnitOn_basicOpen_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ f : V, (∀ k, ∃ n : ℕ, s k ∣ f ^ n) → ∀ y, PsiUnitOn Q y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv f hf y
  obtain ⟨g, hD, hg, -, -⟩ := hdiv
  have h1 : ∀ χ, PsiUnitOn (mulDeg L.D l.M') χ Set.univ := fun χ => L.gen (l.M' • χ)
  have h2 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ := GlobalTheory.T.psiUnitOn_univ_of_pullback_generating _ _ _ _ _ hD h1 y
  have h3 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) :=
    fun j W hW _ => h2 j W hW (Set.subset_univ _)
  by_cases hf0 : f = 0
  · subst hf0
    refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ 0 0 (by simp) (fun p hp => ?_) h3
    exact ((hp : (0 : V) ∉ (p : PrimeSpectrum V).asIdeal) (Ideal.zero_mem _)).elim
  set m : I → ℤ := fun k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y) with hm
  have hs : ∀ k, s k ≠ 0 := fun k hk => by
    obtain ⟨n, hn⟩ := hf k
    rw [hk, zero_dvd_iff] at hn
    exact hf0 (pow_eq_zero_iff'.1 hn).1
  refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ (∏ k, s k ^ (m k).toNat) (∏ k, s k ^ (-m k).toNat) ?_ (fun p hp => ?_) h3
  · have hy := hg y
    have hgy : ((g y : (FractionRing V)ˣ) : FractionRing V) = (∏ k, algebraMap V (FractionRing V) (s k) ^ m k)⁻¹ := by
      rw [← hy, Units.val_inv_eq_inv_val, inv_inv]
    have hne : ∀ k, algebraMap V (FractionRing V) (s k) ≠ 0 := fun k =>
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
    rw [hgy, map_prod, map_prod, inv_mul_eq_iff_eq_mul₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, zpow_mul_toNat (hne k)]
  · have hp' : f ∉ (p : PrimeSpectrum V).asIdeal := hp
    have hk : ∀ k, s k ∉ (p : PrimeSpectrum V).asIdeal := fun k hk => by
      obtain ⟨n, hn⟩ := hf k
      exact hp' ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem n (Ideal.mem_of_dvd _ hn hk))
    constructor <;>
    · intro hmem
      obtain ⟨k, -, hk'⟩ := ((p : PrimeSpectrum V).isPrime.prod_mem_iff).1 hmem
      exact hk k ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem _ hk')

end GlobalTheory.UnitOpen
