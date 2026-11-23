import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeOIffScaleMulFinitePartMemIdealLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotentStatement

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacInertMove

open GlobalTheory.WeilParts GlobalTheory.IdemSupport GlobalTheory.LocalGlobalChar Filter Topology
open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.VacRead (lsB)

variable {D : D7}

def congrGroup (V : HSp D) (I : NonUnitalSubring (AE D)) : Subgroup (GA D V) where
  carrier := {g | ∀ i j, (mt V g - 1) i j ∈ I ∧ (mt V g⁻¹ - 1) i j ∈ I}
  one_mem' := fun i j => by
    rw [inv_one, mt_one, sub_self, Matrix.zero_apply]
    exact ⟨zero_mem _, zero_mem _⟩
  mul_mem' := by
    have key : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) (AE D), (∀ i j, (M - 1) i j ∈ I) → (∀ i j, (N - 1) i j ∈ I) →
        ∀ i j, (M * N - 1) i j ∈ I := fun M N hM hN i j => by
      have e : M * N - 1 = (M - 1) * (N - 1) + (M - 1) + (N - 1) := by noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => mul_mem (hM i k) (hN k j)) (hM i j)) (hN i j)
    intro a b ha hb i j
    rw [_root_.mul_inv_rev, mt_mul, mt_mul]
    exact ⟨key _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j,
      key _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j⟩
  inv_mem' := fun {a} ha i j => by
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem piece_mem_congrGroup (V : HSp D) (I : NonUnitalSubring (AE D)) {f : AE D} (hf : f * f = f) (hc : cA D f = f)
    (hI : ∀ z ∈ I, f * z ∈ I) {g g₁ : GA D V} (hg : g ∈ congrGroup V I)
    (e : mt V g₁ = f • mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) : g₁ ∈ congrGroup V I := by
  obtain ⟨q, hq⟩ := exists_piece V hf hc g⁻¹
  have hpq : g₁⁻¹ = q := by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, e, hq, mix_mul hf, ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  have key : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j,
      (f • M + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1) i j = f * (M - 1) i j := fun M i j => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  intro i j
  rw [hpq, e, hq, key, key]
  exact ⟨hI _ (hg i j).1, hI _ (hg i j).2⟩

theorem ind_mem_intAf (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : Ainf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F b (ind S))) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  rw [hΦ.int]
  intro Q
  rw [hΦ.base]
  change GlobalTheory.AdeleBaseChange.locMap D.host.F Q (evalV D.host.F _ (ind S)) ∈ _
  rw [ev_ind]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

def inertInt (D : D7) : NonUnitalSubring (AE D) where
  carrier := {z | infPart D z = 0 ∧ finPart D z ∈ intAE D ∧
    ∀ v ε, IsPlaceIdem D v ε → ¬ NonSplitAt D v ε → algebraMap (AF D.host.F) (AE D) ε * z = 0}
  zero_mem' := ⟨RingHom.map_zero _, by rw [RingHom.map_zero]; exact zero_mem _, fun _ _ _ _ => mul_zero _⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [RingHom.map_add, ha.1, hb.1, add_zero], by rw [RingHom.map_add]; exact add_mem ha.2.1 hb.2.1,
    fun v ε h h' => by rw [mul_add, ha.2.2 v ε h h', hb.2.2 v ε h h', add_zero]⟩
  neg_mem' := fun {a} ha => ⟨by rw [RingHom.map_neg, ha.1, neg_zero], by rw [RingHom.map_neg]; exact neg_mem ha.2.1,
    fun v ε h h' => by rw [mul_neg, ha.2.2 v ε h h', neg_zero]⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [RingHom.map_mul, ha.1, zero_mul],
    by rw [RingHom.map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2.1 hb.2.1,
    fun v ε h h' => by rw [← mul_assoc, ha.2.2 v ε h h', zero_mul]⟩

theorem mul_mem_inertInt {f : AE D} (hf : finPart D f ∈ intAE D) : ∀ z ∈ inertInt D, f * z ∈ inertInt D :=
  fun z hz => ⟨by rw [RingHom.map_mul, hz.1, mul_zero], by rw [RingHom.map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D hf hz.2.1,
    fun v ε h h' => by rw [mul_left_comm, hz.2.2 v ε h h', mul_zero]⟩

set_option maxHeartbeats 800000 in

theorem congrGroup_le (V : HSp D) (H : Subgroup (GA D V)) (hH : IsClosed (H : Set (GA D V)))
    (hpl : ∀ v ε, NonSplitAt D v ε → ∀ g ∈ congrGroup V (inertInt D), SuppPl ε V g → g ∈ H) :
    congrGroup V (inertInt D) ≤ H := by
  have h1 : ∀ g : GA D V, (∀ i j, (mt V g - 1) i j = 0) → g ∈ H := fun g hg => by
    have : g = 1 := mt_inj V (by rw [mt_one, ← sub_eq_zero]; exact Matrix.ext hg)
    rw [this]; exact one_mem _
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ g ∈ congrGroup V (inertInt D), SuppPl (eps S) V g → g ∈ H := by
    intro S
    induction S using Finset.cons_induction with
    | empty =>
      intro g hg hs
      refine h1 g fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [(hg i j).1.1, RingHom.map_zero]) ?_
      have h1 : (finPart D).mapMatrix (mt V g) = 1 := congrArg Units.val (mem_GinfC V hs)
      have h2 : (finPart D).mapMatrix (mt V g - 1) = 0 := by
        rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
      rw [RingHom.map_zero]
      exact congrFun (congrFun h2 i) j
    | cons v S hv ih =>
      intro g hK hg
      obtain ⟨h1', h2'⟩ := eps_cons S v hv
      have h1' := congrArg (algebraMap (AF D.host.F) (AE D)) h1'
      have h2' := congrArg (algebraMap (AF D.host.F) (AE D)) h2'
      rw [RingHom.map_mul] at h1' h2'
      rw [RingHom.map_sub, RingHom.map_one] at h2'
      have hi := alg_idem (D := D) (pl_mul_self v)
      obtain ⟨g₁, e₁⟩ := exists_piece V hi (cA_algebraMap _) g
      have s₁ := (suppF_iff V _ g₁).2 (smul_mix hi e₁)
      have k₁ := piece_mem_congrGroup V _ hi (cA_algebraMap _) (mul_mem_inertInt (ind_mem_intAf _ _)) hK e₁
      have h3 : (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v}))) *
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v}))) =
        1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ind {v})) := by linear_combination hi
      obtain ⟨g₂, e₂⟩ := exists_piece V h3 (by rw [RingHom.map_sub, RingHom.map_one, cA_algebraMap]) g
      have s₂ := (suppF_iff V _ g₂).2 (smul_mix h3 e₂)
      rw [sub_sub_cancel] at e₂
      have e : g = g₁ * g₂ := mt_inj V ((mt_mul V g₁ g₂).trans (mix_split hi e₁ e₂)).symm
      have k₂ : g₂ ∈ congrGroup V (inertInt D) := by
        have := mul_mem (inv_mem k₁) hK
        rwa [e, inv_mul_cancel_left] at this
      have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := fun i j => by
        rw [← s₁ i j, ← mul_assoc, h1']
      have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := hg
      have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (AE D) (eps (S.cons v hv))) := by
        have := mul_mem (inv_mem t₁) t
        rwa [e, inv_mul_cancel_left] at this
      have u₂ : SuppPl (eps S) V g₂ := fun i j => by
        rw [← h2', mul_assoc, s₂ i j, t₂ i j]
      have m₁ : g₁ ∈ H := by
        by_cases hn : NonSplitAt D v (pairA D.host.F 0 (ind {v}))
        · exact hpl v _ hn g₁ k₁ s₁
        · exact h1 g₁ fun i j => (s₁ i j).symm.trans ((k₁ i j).1.2.2 v _ (isPlaceIdem v) hn)
      rw [e]
      exact mul_mem m₁ (ih g₂ k₂ u₂)
  intro g hg
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  have a1 : Tendsto (fun S => mt V (p S)) atTop (𝓝 (mt V g)) := (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => mt V (p S)⁻¹) atTop (𝓝 (mt V g⁻¹)) := (tendsto_mix _).congr fun S => by rw [hpq, hq]
  have hlim : Tendsto p atTop (𝓝 g) := tendsto_HA _ _ _ a1 a2
  refine hH.mem_of_tendsto hlim (Eventually.of_forall fun S => hS S _ ?_ ?_)
  · exact piece_mem_congrGroup V _ (alg_idem (eps_mul_self S)) (cA_algebraMap _) (mul_mem_inertInt (ind_mem_intAf _ _)) hg (hp S)
  · exact (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S))

theorem finQ_mem_iff (z : AE D) : finQ D z ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ finPart D z ∈ intAE D := by
  rw [mem_intAE_iff, ← GlobalTheory.BotClassDict.toAfE_int_iff, GlobalTheory.BotClassDict.toAfE_finQ]
  exact Iff.rfl

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := Ideal.absNorm_mem _
  generalize Ideal.absNorm v.asIdeal = n at h0 h1
  induction n using induction_on_primes with
  | zero => exact absurd rfl h0
  | one => exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 (by simp)) v.isPrime.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h1
    exact (v.isPrime.mem_or_mem h1).elim (fun h => ⟨p, hp, h⟩) (ih (right_ne_zero_of_mul h0))

theorem unramAt_of_hasFinPart {χ : (AE D)ˣ →* Circle} {N : ℕ} {c : HeckeU D N} {e : ℤ} (h : HasFinPart χ c e)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hi : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rwa [RingHom.map_mul, (place_comp hΦ hv.1).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at this
  have hy : c.f (Units.map (finQ D).toMonoidHom x) = 1 := by
    refine c.unr _ ⟨(finQ_mem_iff _).2 h1, (finQ_mem_iff _).2 h2⟩ fun q hq hn => ?_
    have e1 : ((Units.map (finQ D).toMonoidHom x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = finQ D ((x : AE D) - 1) := by
      rw [RingHom.map_sub, RingHom.map_one]; rfl
    rw [e1, GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq]
    intro w η hη hw
    have hne : w ≠ v := by
      rintro rfl
      exact hn ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq w ε hv.1 hw).2 hv)
    rw [← hx, ← mul_assoc, place_orth hΦ hη hv.1 hne, zero_mul]
  have := h x (Units.map (finQ D).toMonoidHom x) ⟨hi, by
    rw [← GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    exact congrArg _ (GlobalTheory.BotClassDict.toAfE_finQ _).symm⟩
  rw [hy, one_zpow] at this
  exact Circle.ext this

theorem finQ_mt_mem {V : HSp D} {g : GA D V} (hg : g ∈ congrGroup V (inertInt D)) (i j : Fin V.rank) :
    finQ D (mt V g i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have e : mt V g i j = (mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, RingHom.map_add]
  refine add_mem ((finQ_mem_iff _).2 (hg i j).1.2.1) ?_
  rw [Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]; exact one_mem _
  · rw [RingHom.map_zero]; exact zero_mem _

theorem actO_mem_iff {S T : HSp D} (hS : S.gram = 1) {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} (hc : cc ≠ ⊥)
    (hr : IsScale D cc r) {g : GA D S} {h : GA D T} (hg : g ∈ congrGroup S (inertInt D)) (hh : h ∈ congrGroup T (inertInt D))
    (u : WO S T) :
    u ∈ latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
    actO S T g h u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ g ∈ congrGroup S (inertInt D), ∀ h ∈ congrGroup T (inertInt D), ∀ u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h u ∈
      latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro g hg h hh u hu
    have h0 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
    have h1 := (GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice D S T hS cc r hc hr u h0).1 hu
    refine (GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice D S T hS cc r hc hr _ ?_).2 fun i j => ?_
    · rw [actO, Matrix.map_mul, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    · have e : finQ D (actO S T g h u i j) = ∑ l, (∑ k, finQ D (mt T h i k) * finQ D (u k l)) * finQ D (mt S g⁻¹ l j) := by
        have e1 : (actO S T g h u).map (finQ D) = (mt T h).map (finQ D) * u.map (finQ D) * (mt S g⁻¹).map (finQ D) := by
          rw [actO, Matrix.map_mul, Matrix.map_mul]
        exact congrFun (congrFun e1 i) j
      rw [e, Finset.mul_sum]
      refine sum_mem fun l _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have := GlobalTheory.FinWeil.ihE_mul D cc (mul_mem (finQ_mt_mem hh i k) (finQ_mt_mem (inv_mem hg) l j)) (h1 k l)
      convert this using 1
      ring
  refine ⟨key g hg h hh u, fun hu => ?_⟩
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rw [← e]
  exact key _ (inv_mem hg) _ (inv_mem hh) _ hu

theorem mem_congrGroup {V : HSp D} (hV : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank} (hg : IsFinPt V g x)
    (hs : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (hi : Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : g ∈ congrGroup V (inertInt D) := by
  have e1 := GlobalTheory.LevelTr.finQ_mt_of_isFinPt V hV hg
  have e2 := GlobalTheory.LevelTr.finQ_mt_inv_of_isFinPt V hV hg
  have one : ∀ i j, finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := fun i j => by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  have oneI : ∀ i j, (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have inf : ∀ k ∈ GfC V, ∀ i j, infPart D ((mt V k - 1) i j) = 0 := fun k hk i j => by
    have h1 : (infPart D).mapMatrix (mt V k) = 1 := GlobalTheory.LevelTr.infPart_mt_of_mem_GfC V hk
    have h2 : (infPart D).mapMatrix (mt V k - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    exact congrFun (congrFun h2 i) j
  have sp : ∀ v ε, IsPlaceIdem D v ε → ¬ NonSplitAt D v ε →
      g ∈ suppGroup V (1 - algebraMap (AF D.host.F) (AE D) ε) := fun v ε hε hn i j => by
    obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
    have h1 := hs q hq (fun h => hn ((GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent D q hq v ε hε hqv).1 h)) i j
    rw [← e1, Matrix.map_apply, ← one, ← RingHom.map_sub, GlobalTheory.T.finitePartRationalTensor_zeroAtPrime_iff_placeIdem D q hq] at h1
    rw [sub_mul, one_mul, Matrix.sub_apply, h1 v ε hε hqv, sub_zero]
  have sp' : ∀ (k : GA D V) (a : AE D), k ∈ suppGroup V (1 - a) → ∀ i j, a * (mt V k - 1) i j = 0 := fun k a hk i j => by
    have := hk i j
    linear_combination -this
  intro i j
  refine ⟨⟨inf g hg.1 i j, ?_, fun v ε hε hn => sp' _ _ (sp v ε hε hn) i j⟩,
    ⟨inf _ (inv_mem hg.1) i j, ?_, fun v ε hε hn => sp' _ _ (inv_mem (sp v ε hε hn)) i j⟩⟩
  · rw [← finQ_mem_iff, Matrix.sub_apply, RingHom.map_sub, one]
    exact sub_mem (by have := (hi i j).1; rwa [← e1] at this) (oneI i j)
  · rw [← finQ_mem_iff, Matrix.sub_apply, RingHom.map_sub, one]
    exact sub_mem (by have := (hi i j).2; rwa [← e2] at this) (oneI i j)

theorem latVac_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    {r : D.host.E} (hset : Setup ψ θ S T cc δ r) {e0 : VC D S.rank T.rank → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank)) {f₀ : WO S T → ℂ}
    (hf₀ : Reads ψ θ rfl rfl cc δ r e0 f₀) :
    IsSelfDualC S (lsB D cc r S.rank) ∧ IsSelfDualC T (stdL D T.rank) ∧ IsLatVac (heisO ψ S T)
      (latO S T (lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True)
      f₀ := by
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  have hone : ∀ {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GlobalTheory.MovedDict.inV 1 L = (L : Set _) := fun L => by
    ext x
    simp [GlobalTheory.MovedDict.inV]
  obtain rfl : ΛS = lsB D cc r S.rank := SetLike.coe_injective (hΛS.trans (hone _))
  obtain rfl : ΛT = stdL D T.rank := SetLike.coe_injective (hΛT.trans (hone _))
  refine ⟨hSd, hTd, ?_⟩
  obtain ⟨f, hf0⟩ := GlobalTheory.VacRead.vac_exists_gram_one ψ θ hψ hθ S T gS gT _ _ hSd hTd
  have hf := hf0
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := GlobalTheory.VacRead.theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := GlobalTheory.VacRead.th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨c, hc'⟩ := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ crv _ _ _ (GlobalTheory.NormSum.VacMove.klat (tor0 D cc δ)
    (GlobalTheory.NormSum.VacMove.moves_one D S.rank) (GlobalTheory.NormSum.VacMove.moves_one D T.rank))).1 _ he _ hG (by
      intro h0
      apply GlobalTheory.StepMove.vacO_ne_zero hf
      refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
      rw [hΦ w hw]
      have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
      simp only [Pi.zero_apply, hback] at e
      rw [e, mul_zero])
  have hR : Reads ψ θ rfl rfl cc δ r
      (fun Y => (fun Y' : VC D S.rank T.rank => Φ (δ⁻¹ • Y')) (fun τ i j => Y τ i j / embT D τ r)) f :=
    (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => by
      rw [hΦ w hw]
      simp only [hback]⟩
  have e : f₀ = c • f := hf₀.unique (hc' ▸ hR.smul c)
  have hsm : ∀ u, heisO ψ S T u f = f → heisO ψ S T u f₀ = f₀ := fun u hu => by
    funext w
    have := congrFun hu w
    rw [e]
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [mul_left_comm, this]
  exact ⟨fun u hu => hsm _ (hf0.2.lat.1 u hu), fun a ha u hu hh => hsm _ (hf0.2.lat.2 a ha u hu hh)⟩

def stab {G X : Type} [Group G] (om : G →* Module.End ℂ (X → ℂ)) (f : X → ℂ) : Subgroup G where
  carrier := {p | om p f = f}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change om _ f = f at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    change om _ f = f at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isClosed_stab {G X : Type} [Group G] [TopologicalSpace G] (om : G →* Module.End ℂ (X → ℂ)) (f : X → ℂ)
    (h : ∀ w, Continuous fun p => om p f w) : IsClosed (stab om f : Set G) :=
  isClosed_eq (continuous_pi h) continuous_const

theorem inert_vacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hom _ t0 _ _ he hχS hχT f₀ hf₀ x y g h hg hh sx sy ix iy
  subst hS hT
  obtain ⟨sdS, sdT, hvac⟩ := latVac_of_reads hset he.1 hf₀
  have s1 : ∀ (V : HSp D) (ε : AF D.host.F), SuppPl ε V 1 := fun V ε i j => by
    rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have loc : ∀ v ε, NonSplitAt D v ε → ∀ g ∈ congrGroup S (inertInt D), ∀ h ∈ congrGroup T (inertInt D),
      SuppPl ε S g → SuppPl ε T h → om (g, h) f₀ = f₀ := fun v ε hv g hg h hh sg sh =>
    GlobalTheory.VecInvInert.om_fixes_vacuum D ψ S T _ _ χS χT om hom sdS sdT (exists_isEtaTilde_unramified D) v ε hv
      (unramAt_of_hasFinPart hχS hv) (unramAt_of_hasFinPart hχT hv) g h sg sh
      (actO_mem_iff hset.gS hset.crv.1.1 hset.scale hg hh) f₀ hf₀.1 hvac
  have hc := hom.om_cont f₀ hf₀.1
  have h1 : om (g, 1) f₀ = f₀ := congrGroup_le S (stab (om.comp (MonoidHom.inl _ _)) f₀)
    (isClosed_stab _ _ fun w => (hc w).comp (Continuous.prodMk_left 1))
    (fun v ε hv k hk sk => loc v ε hv k hk 1 (one_mem _) sk (s1 T ε)) (mem_congrGroup hset.gS hg sx ix)
  have h2 : om (1, h) f₀ = f₀ := congrGroup_le T (stab (om.comp (MonoidHom.inr _ _)) f₀)
    (isClosed_stab _ _ fun w => (hc w).comp (Continuous.prodMk_right 1))
    (fun v ε hv k hk sk => loc v ε hv 1 (one_mem _) k hk (s1 S ε) sk) (mem_congrGroup hset.gT hh sy iy)
  have hp : (g, h) = ((g, 1) : GA D S × GA D T) * (1, h) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [W.inert x y ix iy sx sy, hp, map_mul, Module.End.mul_apply, h2, h1]
  exact hf₀

end GlobalTheory.VacInertMove

end
