import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hY (isGrpPullback_pullback Y (U p).ι)) hK

end GlobalTheory.KTrivSqZero
