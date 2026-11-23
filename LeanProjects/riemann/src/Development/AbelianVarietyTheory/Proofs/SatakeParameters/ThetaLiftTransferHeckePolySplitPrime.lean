import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHeckeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPrimeHecke

open Formalism.L2.Host Formalism.L2.Col

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) :
    χ.locK Q k = χ.val Q := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← hk]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : L)
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * (atFin Q (unif Q))⁻¹) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, h2, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h4 := hu _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem exists_unif {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ ϖ : 𝓞 L, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 ∧ Q.valuation L (ϖ : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, h⟩ := Q.intValuation_exists_uniformizer
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [← Q.intValuation_lt_one_iff_mem, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [← Q.intValuation_le_pow_iff_mem, h, WithZero.exp_le_exp]; norm_num
  · rw [← h]; exact Q.valuation_of_algebraMap ϖ

theorem poly_id (q r t : ℕ) (u v : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (r + t) q (fun k => ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * u⁻¹ ^ k * v ^ j else 0) * a j) =
    (heckePolyOf r q a).comp (C (u⁻¹ * v) * X) * blockPoly (u⁻¹ * (q : ℂ) ^ r) q t := by
  have key := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q r t (fun j => if j ≤ r then a j else 0) u⁻¹ (u⁻¹ * v)
    (fun j hj => if_neg (by omega))
  have h1 : heckePolyOf r q (fun j => if j ≤ r then a j else 0) = heckePolyOf r q a := by
    unfold heckePolyOf
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (show j ≤ r by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1] at key
  rw [← key]
  congr 1
  funext k
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [Nat.lt_succ_iff, and_comm]) fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.1 hj).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add, mul_pow]
  ring

variable {D : D7}

theorem not_isConjPl {P : Pl D.host.E} (h : conjPl P ≠ P) : ¬ Formalism.IndefR.Lev.IsConjPl P P := by
  intro hc
  apply h
  refine HeightOneSpectrum.ext ((conjPl P).isMaximal.eq_of_le P.isPrime.ne_top ?_)
  refine Ideal.map_le_iff_le_comap.2 fun c hcP => ?_
  obtain ⟨c', hc', he⟩ := hc c hcP
  have : Formalism.DivisionValues.cO D.host.E c = c' := RingOfIntegers.ext he.symm
  rw [Ideal.mem_comap, this]
  exact hc'

theorem unrPl_mul_inv {P : Pl D.host.E} {a b : (AE D)ˣ →* Circle} (ha : UnrPl P a) (hb : UnrPl P b) : UnrPl P (a * b⁻¹) := by
  intro e f h x h1 h2 h3
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha e f h x h1 h2 h3, hb e f h x h1 h2 h3, inv_one, mul_one]

theorem consts (μ η ηa q s : ℂ) (hμ : μ ≠ 0) (hη : η ≠ 0) (hs : s ≠ 0) (hq : s * s = q) (he : ηa = η * s⁻¹) (r t : ℕ)
    (hr : Odd r) (ht : Odd t) :
    (μ * η⁻¹ * s ^ r)⁻¹ * (μ * s ^ (r + t)) = ηa * q ^ ((t + 1) / 2) ∧
      (μ * η⁻¹ * s ^ r)⁻¹ * q ^ r = μ⁻¹ * ηa * q ^ ((r + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := ht
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega, show (2 * b + 1 + 1) / 2 = b + 1 by omega, he, ← hq]
  constructor
  · field_simp
    ring
  · field_simp
    ring

set_option maxHeartbeats 1600000 in

theorem transfer_and_heckePoly : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc hS i t P
  obtain ⟨hQ0, hG, -, hF⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hc.lev
  obtain ⟨hgood, hsplit, hq⟩ := hF hc.fam t P P.2
  obtain ⟨hunη, hunμ⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev t _ hgood
  obtain ⟨gramR, c0R, c0L, tie⟩ := hc.fam.tie
  obtain ⟨-, hAr, hAt⟩ := tie.ranks
  have hP0 : (P : Pl0) ∈ A.ok A.μ0 := by
    have h := (tie.ok t P).1 P.2
    rw [tie.ok, hQ0]
    simp only [Finset.coe_empty, Set.union_empty]
    exact ⟨h.1, fun h' => h.2.1 (Or.inl h'), fun Q hQ => h.2.2 Q (Or.inl hQ)⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (not_isConjPl hsplit)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := exists_unif (R.pl P)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hpl : Formalism.L2.JoinChr.IsPlIdem D e (R.pl P) := by
    obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
    exact ⟨h1, ⟨v, ε, h3, Or.inl ⟨h2, h4⟩⟩, h5⟩
  let x : (AE D)ˣ := Formalism.L2.JoinChr.locU hpl.1 (Units.mk0 _ hϖ0)
  have hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) := rfl
  have hx' : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    rw [hx, Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hunμ ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hM⟩ := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ (R.pl P) (hc.thP.ωP i t) hsplit hun1 (unrPl_mul_inv hun1 hunη)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hM' := (hM e ϖ x D.R.t he hϖ1 hϖ2 hx').2 hV
  refine ⟨_, fun k hk => GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hc hS i t _ hgood hfix _ _ (hM' k hk), fun a => ?_⟩

  have hu0 : (R.C.mu0 i).UnrAt (R.pl P) := by
    refine (R.C.isMu0 i).unr _ fun k hk => (hG t _ hgood).1 ?_
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  have huξ : (R.xiH t).UnrAt (R.pl P) := by
    by_contra h
    rcases (hc.lev.Q_ram t _).1 h with h | ⟨PP, h1, h2⟩
    · exact (hgood _ (Or.inr h)).1 rfl
    · exact (hgood _ (Or.inr h1)).2 h2
  have hη : ((R.eta x : Circle) : ℂ) = (R.C.eta.val (R.pl P) : ℂˣ) := by
    rw [hc.lev.eta.2 _ e hpl _ x hx, locK_eq_val _ _ (R.C.isEta.unr _) _ hϖ3]
  have hμ : ((R.toLevCh.mu t ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (A.muVal i t P : D.what₂.LL) := by
    rw [hc.fam.muVal i t P P.2, HChar.val_mul, Units.val_mul, ← locK_eq_val _ _ hu0 (Units.mk0 _ hϖ0) hϖ3,
      ← locK_eq_val _ _ huξ (Units.mk0 _ hϖ0) hϖ3, ← (hc.lev.mu0 i).2 _ e hpl _ x hx, ← (hc.lev.xi t).2 _ e hpl _ x hx,
      ← Circle.coe_mul]
    rfl
  have hN : (0 : ℝ) < (Ideal.absNorm (R.pl P).asIdeal : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hs0 : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hss : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) = (Ideal.absNorm (R.pl P).asIdeal : ℕ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le, Complex.ofReal_natCast]
  have hηa : D.what₂.embLL (A.etaVal P : D.what₂.LL) =
      ((R.eta x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ)⁻¹ := by
    rw [hc.fam.etaVal P hP0, hη, etaAlg, HChar.valTw, Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le,
      Complex.ofReal_natCast]
  have hr : Odd (Wc D i).rank := by
    rw [hW]
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  obtain ⟨c1, c2⟩ := consts _ _ _ _ _ (Circle.coe_ne_zero (R.toLevCh.mu t ((i : ℕ) + 1) x)) (Circle.coe_ne_zero (R.eta x))
    hs0 hss hηa _ _ hr D.R.t_odd
  have hB : ((A.fam.L i t).blockProd P).map D.what₂.embLL =
      blockPoly (D.what₂.embLL (firstValA (A.muVal i t) A.etaVal A.q A.r P)) (A.q P) A.t := by
    rw [← map_blockPoly]
    simp [BlockDat.blockProd, FamIn.fam, liftDat]
  rw [hB, firstValA, map_mul D.what₂.embLL, map_mul D.what₂.embLL, Units.val_inv_eq_inv_val, map_inv₀, map_pow D.what₂.embLL, map_natCast D.what₂.embLL, ← hμ,
    hAr, hAt, hq, ← hW,
    ← c1, ← c2]
  simp only [Lift.chrTh, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [hV]
  exact poly_id _ _ _ _ _ a

end GlobalTheory.ThetaPrimeHecke
