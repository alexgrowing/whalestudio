import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

theorem htW_eq_htDual {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (L : Semi.LB G.left) (n : ℕ) {F : Type} [Field F] [NumberField F] (ρ : 𝓞 F →+* Module.End Ω Li)
    (σ : 𝓞 F →+* Ω) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q)
    (hu : unitAt ξ q (((discr F).natAbs : ℕ) : Ω)) :
    M.htW L n ρ σ (differentIdeal ℤ (𝓞 F)) q = M.htDual L n ρ σ q := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 := he.2 _ (natAbs_discr_mem_different F)
    rw [map_natCast] at h1
    have h2 := Submodule.smul_mem _ (⟨_, hu.2.2⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu.2.2⟩ : regAt ξ q) • (((discr F).natAbs : ℕ) : Ω) • e = e := by
      show (((discr F).natAbs : ℕ) : Ω)⁻¹ • (((discr F).natAbs : ℕ) : Ω) • e = e
      exact inv_smul_smul₀ hu.1 e
    rw [h3] at h2
    exact h2
  · intro e he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact Submodule.smul_mem _ (⟨σ d, hσ d⟩ : regAt ξ q) he

theorem exists_mul_of_isCp {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {κ w : Ω} (hκ : HT.IsCp p κ) (hw : HT.IsCp p w)
    (R : Subring Ω) (hR : w ∈ R) : ∃ u ∈ R, w = u * κ := by
  unfold HT.IsCp at hκ hw
  rw [if_neg h2] at hκ hw
  obtain ⟨z, hz, rfl⟩ := hκ
  obtain ⟨z', hz', rfl⟩ := hw
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  obtain ⟨k, -, hk⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have h1 : z' ∈ R := by simpa using R.add_mem hR R.one_mem
  have h3 : z ∈ R := hj ▸ R.pow_mem h1 j
  refine ⟨∑ i ∈ Finset.range k, z ^ i, R.sum_mem fun i _ => R.pow_mem h3 i, ?_⟩
  rw [geom_sum_mul, hk]

theorem sandwich_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp _ h2 hd κ w hκ hw hS q hq hwq t
  haveI : CharZero Ω := ⟨fun a b h => by
    have h' : 𝔐.cst (a : c.F) = 𝔐.cst (b : c.F) := by rw [map_natCast, map_natCast, h]
    exact Nat.cast_injective (𝔐.cst.injective h')⟩
  have hN : Flat.NormalCpt 𝔐.ξ := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hu : unitAt 𝔐.ξ q (((discr E).natAbs : ℕ) : Ω) := unitAt_natAbs_discr fun r hr hrd => by
    by_contra hn
    have : r = p := GlobalTheory.CompanionTheory.Ar.inFibre_unique hp.out hr hq hn
    exact hd (this ▸ hrd)
  have hHT : 𝔐.HT p t q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb t) q := by
    cases t with
    | inl τ => exact htW_eq_htDual 𝔐.M _ _ 𝔐.ρ _ q (integers_regular hN _ q) hu
    | inr τ => rfl
  obtain ⟨-, -, -, hs⟩ := hS q hq
  obtain ⟨h1, h3⟩ := hs t
  obtain ⟨u, huR, rfl⟩ := exists_mul_of_isCp hp.out h2 hκ hw (regAt 𝔐.ξ q) hwq
  rw [hHT]
  refine ⟨h1, fun e he => ?_⟩
  rw [mul_smul]
  exact Submodule.smul_mem _ (⟨u, huR⟩ : regAt 𝔐.ξ q) (h3 e he)

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt
