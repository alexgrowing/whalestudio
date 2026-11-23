import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven.LocPf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (h : m = n)
    (y : Fin n → (epsR R ⟶ G)) (hy : IsLieBasis y) : IsLieBasis (fun i : Fin m => y (i.cast h)) := by
  subst h
  exact hy

theorem exists_away_subset {A : Type} [CommRing A] [IsDomain A] (U : Set (Sp A)) (hU : IsOpen U)
    (hgen : Set.range (spMap (algebraMap A (FractionRing A))) ⊆ U) :
    ∃ f : A, f ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away f))) ⊆ U := by
  obtain ⟨q⟩ : Nonempty (Sp (FractionRing A)) := inferInstance
  have hp := hgen ⟨q, rfl⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := (spMap (algebraMap A (FractionRing A)) q : PrimeSpectrum A)) hp hU
  refine ⟨r, ?_, ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpr (Ideal.zero_mem _)
  · rw [show Set.range (spMap (algebraMap A (Localization.Away r))) =
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hrU

theorem mem_range_of_traits {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [Algebra.FiniteType ℤ A] (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : V, h b = algebraMap V (FractionRing V) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue A a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ _ hc hfin t ht
    by_cases htf0 : t f = 0
    · cases n with
      | zero => simp
      | succ k => exact absurd (by rw [map_pow, htf0, zero_pow (Nat.succ_ne_zero k)]) ht
    have htf : t f ≠ 0 := htf0
    have hinjV := IsFractionRing.injective V (FractionRing V)
    have hu : IsUnit (((algebraMap V (FractionRing V)).comp t) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := H V hc hfin t htf _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    rw [← e', ← hn, map_pow, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

end GlobalTheory.KeyEven.LocPf

namespace GlobalTheory.KeyEven.LocPf

theorem keyLoc_of_famUnit_keyTrait : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  intro κ hFU hKT A _ _ _ _ _ G _ _ L σ x y hG hsm hopen hsym hpol hunif hy hσ hkey
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper hG hpb.1
  obtain ⟨f, hf0, hfab⟩ := exists_away_subset (abLocus G) hopen hab
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) G L σ x.P.g y x.g_pos hG hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hFU (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : Vˣ, h u = algebraMap V (FractionRing V) w := by
    intro V _ _ _ _ hcomp hfin t ht h hh
    have hrange : Set.range (spMap ((algebraMap V (FractionRing V)).comp t)) ⊆ abLocus G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing V) ((algebraMap V _).comp t) G L σ x.P.g y x.g_pos hG hsm
      hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing V) (algebraMap A _) h G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    obtain ⟨L', σ', y', hiso, hy', hσ', hk'⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing V) t (algebraMap V _) G L σ xV
      (fun i => y (i.cast hgV)) hG (isLieBasis_cast hgV y hy) hσ hkV
    have hne : (spMap t ⁻¹' abLocus G).Nonempty := by
      obtain ⟨q⟩ : Nonempty (Sp (FractionRing V)) := inferInstance
      exact ⟨spMap (algebraMap V _) q, hrange ⟨q, rfl⟩⟩
    obtain ⟨D, A', U, hU⟩ := hunif V hcomp hfin (spMap t) hne
    obtain ⟨w, hw⟩ := hKT V hcomp hfin _ L' σ' xV y' (IsSemiAbelian.pullback _ G hG)
      ⟨D, A', U, LBIso.trans U.LG.isLB (pull_isLB L.isLB _) L'.isLB hU hiso⟩ hy' hσ' hk'
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_traits f hf0 (u : Localization.Away f) (fun V _ _ _ _ hcomp hfin t ht h hh => by
    obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_traits f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ _ hcomp hfin t ht h hh => by
      obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
      refine ⟨((w⁻¹ : Vˣ) : V), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end GlobalTheory.KeyEven.LocPf
