import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.HeightOnePrimePrincipalLocal
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CodimOnePointMinimalPrime
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.OrderAtCodimOneEqOne
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.OrderOffCodimOneEqZero
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PrimeDivCartier

theorem exists_local_generator (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S] (hP : P.IsPrime) (hPp : P ≤ p)
    (hP0 : P ≠ ⊥) (hmin : ∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) :
    ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r :=
  GlobalTheory.T.height_one_prime_principal_local R S p P hP hPp hP0 hmin

theorem primeIdealOf_minimal (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (h1 : Order.coheight z = 1) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ →
      Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
  GlobalTheory.T.codim_one_point_minimal_prime X U hU z hz h1

theorem ord_eq_one (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha0 : a ≠ 0) (ha : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 :=
  GlobalTheory.T.order_at_codim_one_eq_one X U hU z hz a t h1 ha0 ha ht hg

theorem ord_eq_zero (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r)
    (v : X) (hv : v ∈ U) (hvt : v ∈ X.basicOpen t) (hvz : v ≠ z) :
    Scheme.ord (fnOf U (gen_mem hv) a) v = 0 :=
  GlobalTheory.T.order_off_codim_one_eq_zero X U hU z hz a t h1 hg v hv hvt hvz

open Classical in

theorem exists_local_eqn (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (hu : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (z : X)
    (h1 : Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ π : X.functionFieldˣ, ∀ v ∈ U,
      Scheme.ord (π : X.functionField) v = if v = z then 1 else 0 := by
  classical
  by_cases hzx : z ⤳ x
  · obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    have hzU : z ∈ U := hzx.mem_open U.isOpen hxU
    haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI := hu x
    have hPp : (hU.primeIdealOf ⟨z, hzU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
      have h' : (⟨z, hzU⟩ : U) ⤳ ⟨x, hxU⟩ := Topology.IsInducing.subtypeVal.specializes_iff.1 hzx
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (h'.map hU.isoSpec.hom.continuous)
    obtain ⟨hP0, hmin⟩ := primeIdealOf_minimal X U hU z hzU h1
    obtain ⟨a, haP, ha0, t, htp, hg⟩ := exists_local_generator Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
      (hU.primeIdealOf ⟨z, hzU⟩).2 hPp hP0 hmin
    have hf0 : fnOf U (gen_mem hxU) a ≠ 0 := fun h =>
      ha0 (fnOf_injective U (gen_mem hxU) (h.trans (map_zero _).symm))
    refine ⟨U ⊓ X.basicOpen t, ⟨hxU, ?_⟩, Units.mk0 _ hf0, fun v hv => ?_⟩
    · exact (Scheme.mem_basicOpen X t x hxU).2 ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ t).2 htp)
    · simp only [Units.val_mk0]
      split_ifs with hvz
      · subst hvz
        exact ord_eq_one X U hU v hzU a t h1 ha0 haP (fun h => htp (hPp h)) hg
      · exact ord_eq_zero X U hU z hzU a t h1 hg v hv.1 hv.2 hvz
  · refine ⟨⟨(closure {z})ᶜ, isClosed_closure.isOpen_compl⟩, ?_, 1, fun v hv => ?_⟩
    · exact fun h => hzx (specializes_iff_mem_closure.2 h)
    · have hvz : v ≠ z := fun e => hv (e ▸ subset_closure rfl)
      rw [if_neg hvz, Units.val_one]
      exact (unitAt_one v).ord_eq_zero

end GlobalTheory.PrimeDivCartier

open GlobalTheory.PrimeDivCartier in

theorem GlobalTheory.primeDivisor_isCartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ z : X, Order.coheight z = 1 →
      ∃ D : CartierDiv X, D.mult z = 1 ∧ ∀ v, v ≠ z → D.mult v = 0 := by
  intro X _ _ hu z h1
  classical
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => inferInstance, fun x => by
    haveI := hu x; exact UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  choose U hxU π hπ using exists_local_eqn X hu z h1
  have hunit : ∀ x y, y ∈ U x → UnitAt y ((π x : X.functionField) / π y) := by
    intro x y hy
    have h := (GlobalTheory.T.cartier_divisor_mult_characterize X (0 : CartierDiv X)).2.2.2 y (π x / π y) (fun v hv => by
      have hvx : v ∈ U x := hv.mem_open (U x).isOpen hy
      have hvy : v ∈ U y := hv.mem_open (U y).isOpen (hxU y)
      have e := Scheme.ord_mul (X := X) (x := v) (Units.ne_zero (π x / π y)) (Units.ne_zero (π y))
      rw [← Units.val_mul, div_mul_cancel, hπ x v hvx, hπ y v hvy] at e
      rw [(CartierDiv.isEqn_zero v).mult_eq, Units.val_one, (unitAt_one v).ord_eq_zero]
      split_ifs at e <;> omega)
    simpa using (CartierDiv.isEqn_zero y).iff_unitAt.1 h
  let D : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (π y), fun x => ⟨U x, hxU x, π x, fun y hy => germOf_eq_iff.2 (hunit x y hy)⟩⟩
  have hD : ∀ y, D.IsEqn y (π y) := fun y => rfl
  refine ⟨D, ?_, fun v hv => ?_⟩
  · rw [(hD z).mult_eq, hπ z z (hxU z), if_pos rfl]
  · rw [(hD v).mult_eq, hπ v v (hxU v), if_neg hv]
