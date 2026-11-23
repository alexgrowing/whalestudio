import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperRelAmpleKTrivOfPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_local {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (t : SAB H (Sp O)) (hprop : IsProper t.G.hom) (hpol : GlobalTheory.LN.PolAt t (Out.jK O)) :
    Out.RelAmple t.G t.PP.L := by
  by_cases hf : _root_.IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := GlobalTheory.PolLocal.exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := GlobalTheory.PolLocal.isIso_spMap _ (GlobalTheory.PolLocal.algebraMap_fractionRing_bijective O hf)
    exact (GlobalTheory.PolLocal.ample_kTriv_of_iso mu hA hK).1
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap V (FractionRing V))) tV
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.PolNormal.polAt_generic_pull ρ hρ mV hpol
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (GlobalTheory.PolLocal.isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := GlobalTheory.PolLocal.pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [GlobalTheory.PolLocal.spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, hA⟩ := GlobalTheory.PolNearAmple.relAmple_near_of_polAt E H O t hprop (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  obtain ⟨m₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  have e : spMap (RingHom.id O) = 𝟙 (Sp O) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact hA O (RingHom.id O) hu t (e ▸ m₀)

theorem relAmple_kTriv_of_generic {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => ?_
    have : q.asIdeal.IsPrime := q.isPrime
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨tO, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap S O)) t
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hA := relAmple_local tO (GlobalTheory.PolLocal.isProper_of_map m hp) (GlobalTheory.PolNormal.polAt_generic_pull _ hi m hg)
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at S q t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB
      ⟨w, hw⟩ hA
  exact ⟨hA, GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic E H S t hp hA hg⟩

theorem isProper_relAmple_kTriv_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab S x t' hx ⟨mx⟩
  have : CharZero R := algebraRat.charZero R
  have hf : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  generalize ∏ i, tt i = f at hf hab hx
  let Rf := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  obtain ⟨tf, ⟨mf⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap R Rf)) t
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 ((hab _).2 (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  obtain ⟨hA, hK⟩ := relAmple_kTriv_of_generic tf hpf hg
  have : IsOpenImmersion (spMap (algebraMap R Rf)) := by
    unfold spMap
    exact IsOpenImmersion.of_isLocalization f
  have hr : Set.range x ⊆ Set.range (spMap (algebraMap R Rf)) := by
    rintro _ ⟨s, rfl⟩
    exact hrange.ge (hx s)
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac mf mx (g := IsOpenImmersion.lift _ x hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  obtain ⟨w, hw, -⟩ := m'.lin
  exact ⟨GlobalTheory.PolLocal.isProper_of_map m' hpf,
    GlobalTheory.AmpleLocalBase.relAmple_baseChange m'.cart.1 tf.PP.isLB t'.PP.isLB ⟨w, hw⟩ hA,
    kTriv_pull m'.cart tf.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.AbLocusPol
