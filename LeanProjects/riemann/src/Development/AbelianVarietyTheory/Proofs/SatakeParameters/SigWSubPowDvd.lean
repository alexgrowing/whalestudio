import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHomStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrimeStatement

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwU

variable {p : ℕ} [Fact p.Prime]

theorem pow_card_sub_dvd {n : ℕ} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (hirr : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n) (x : W) :
    (p : W) ∣ x ^ (p ^ n) - x := by
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  haveI : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI := Fintype.ofFinite (W ⧸ Ideal.span {(p : W)})
  have h := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {(p : W)}) x)
  rw [← Nat.card_eq_fintype_card, hcard, ← map_pow, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  exact h

theorem sigW_sub_pow_dvd (y : Formalism.L2.G.Pend.WW p) : (p : Formalism.L2.G.Pend.WW p) ∣ Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p := by
  have h0 : WittVector.constantCoeff (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) = 0 := by
    rw [map_sub, map_pow]
    show (WittVector.frobenius y).coeff 0 - y.coeff 0 ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  have hnu : ¬ IsUnit (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) := fun hu => by
    have := hu.map (WittVector.constantCoeff (p := p) (R := Formalism.L2.G.Pend.kb p))
    rw [h0] at this
    exact not_isUnit_zero this
  have hm := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rwa [(WittVector.irreducible p (k := Formalism.L2.G.Pend.kb p)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm

abbrev sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) : G.P.W v →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) (G.P.setting v).frob

theorem sigRes_spec (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (x : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (sigRes G v x) = G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x) :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW_spec _ _ _ x

theorem sigRes_pow (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v) :
    (G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x) = algebraMap (G.P.W v) (G.P.Qq v) ((sigRes G v)^[s] x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ]
    show (G.P.σ v ^ s) (G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x)) = _
    rw [← sigRes_spec, ih, ← Function.iterate_succ_apply]

theorem map_sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (r : G.P.W v →+* Formalism.L2.G.Pend.WW p) (x : G.P.W v) :
    r (sigRes G v x) = Formalism.MainNotions.FormalGroupSystem.sigW p (r x) := by
  have hS := G.P.setting v
  have hq : ∀ x : G.P.W v, (p : G.P.W v) ∣ x ^ (p ^ G.P.n' v) - x := pow_card_sub_dvd hS.p_unif hS.res_card
  have h := GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) hq (r.comp (sigRes G v)) ((Formalism.MainNotions.FormalGroupSystem.sigW p).comp r)
    (fun y => by
      obtain ⟨z, hz⟩ := haveI := hS.frac_alt
        PI.WittUnramWork.sigW_lift (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) hS.frob y
      obtain ⟨c, hc⟩ := sigW_sub_pow_dvd (r y)
      refine ⟨r z - c, ?_⟩
      simp only [RingHom.comp_apply]
      rw [hz, map_add, map_mul, map_pow, map_natCast]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      ring)
  exact congrArg (fun f => f x) h

theorem nonempty_cEmbC : ∀ (p : ℕ) [Fact p.Prime] (G : GAtP p), 0 < G.P.nV → Nonempty (CEmbC G) := by
  intro p _ G hV
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex p G hV
  let φ : ∀ v, G.P.W v →+* ℂ_[p] := fun v => (E.iK.comp (G.P.ι v)).comp (algebraMap (G.P.W v) (G.P.Qq v))
  have hφ1 : ∀ v x, ‖φ v x‖ ≤ 1 := fun v x => by
    show ‖E.iK (G.P.ι v (algebraMap _ _ x))‖ ≤ 1
    rw [(G.P.setting v).ι_comp]
    exact E.int _
  have hφr : ∀ v x, φ v x ∈ (Formalism.L2.G.Pend.wToC p).range := fun v x => by
    have hS := G.P.setting v
    exact GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) (pow_card_sub_dvd hS.p_unif hS.res_card)
      hS.eq_sum_herm_smul_frame_of_inW (φ v) (hφ1 v) x
  let eW : Formalism.L2.G.Pend.WW p ≃+* (Formalism.L2.G.Pend.wToC p).range :=
    RingEquiv.ofBijective (Formalism.L2.G.Pend.wToC p).rangeRestrict
      ⟨fun a b h => Formalism.L2.G.Pend.wToC_injective p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let rd : ∀ v, G.P.W v →+* Formalism.L2.G.Pend.WW p := fun v =>
    eW.symm.toRingHom.comp ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v))
  have hrd : ∀ v x, Formalism.L2.G.Pend.wToC p (rd v x) = φ v x := fun v x => by
    have := congrArg Subtype.val (eW.apply_symm_apply ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v) x))
    exact this
  refine ⟨⟨E, rd, ?_⟩⟩
  intro v s x
  have hit : ∀ y, rd v ((sigRes G v)^[s] y) = (Formalism.MainNotions.FormalGroupSystem.sigW p)^[s] (rd v y) := by
    induction s with
    | zero => intro y; rfl
    | succ s ih => intro y; rw [Function.iterate_succ_apply, ih, map_sigRes, ← Function.iterate_succ_apply]
  rw [sigRes_pow, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hit, hrd]
  rfl

end GlobalTheory.TwU
