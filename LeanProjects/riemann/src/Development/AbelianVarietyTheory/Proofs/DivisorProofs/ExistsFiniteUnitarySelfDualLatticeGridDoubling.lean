import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open scoped nonZeroDivisors

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.TopFlip.TwistElt

open GlobalTheory.LatExchPf GlobalTheory.IdemSupport

variable {D : D7}

def Clears (a : EAf D) (I : FI D) : Prop := ∀ c ∈ I, eToEAf D c * a ∈ GlobalTheory.StdFrames.OA D

theorem Clears.mul {a b : EAf D} {I J : FI D} (h : Clears a I) (h' : Clears b J) : Clears (a * b) (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on (C := fun x => eToEAf D x * (a * b) ∈ GlobalTheory.StdFrames.OA D) hx
    (fun c hc d hd => ?_) (fun c d hc hd => ?_)
  · rw [map_mul, mul_mul_mul_comm]; exact mul_mem (h c hc) (h' d hd)
  · rw [map_add, add_mul]; exact add_mem hc hd

theorem Clears.conj {a : EAf D} {I J : FI D} (h : Clears a I) (h' : StarLE J I) : Clears (sg D a) J := by
  intro c hc
  have h1 : sg D (eToEAf D (star c) * a) ∈ GlobalTheory.StdFrames.OA D := Formalism.UG.P.csDual_sig_mem _ (h _ (h' c hc))
  have h2 : sg D (eToEAf D (star c)) = eToEAf D c := by
    change star (star c) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) = _
    rw [star_star]; rfl
  rwa [RingHom.map_mul, h2] at h1

theorem cpt_rat (Q : Pl D.host.E) (x : D.host.E) :
    cpt Q (eToEAf D x) = algebraMap D.host.E (Q.adicCompletion D.host.E) x := by
  change toAd D (x ⊗ₜ[D.host.F] 1) Q = _
  rw [GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D)]
  rfl

theorem int_of_mul {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) {n : 𝓞 E} (hn : n ∉ Q.asIdeal) {x : E} {o : 𝓞 E}
    (h : (n : E) * x = o) : algebraMap E (Q.adicCompletion E) x ∈ Q.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap]
  have h1 : Q.valuation E (n : E) = 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hn
  have h2 := congrArg (Q.valuation E) h
  rw [map_mul, h1, one_mul] at h2
  rw [h2]
  exact Q.valuation_le_one o

theorem int_of_eq {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) {x : E} {o : 𝓞 E}
    (h : x = o) : algebraMap E (Q.adicCompletion E) x ∈ Q.adicCompletionIntegers E :=
  int_of_mul Q (n := 1) ((Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top) (o := o) (by simpa using h)

theorem mix_inv {A : Type} [CommRing A] {f x y : A} (hf : f * f = f) (h : x * y = 1) :
    (f * x + (1 - f)) * (f * y + (1 - f)) = 1 := by
  linear_combination f ^ 2 * h + (2 - x - y) * hf

theorem cross_inv {A : Type} [CommRing A] {a a' b b' : A} (ha : a * a' = 1) (hb : b * b' = 1) : (a' * b) * (b' * a) = 1 := by
  linear_combination b * b' * ha + hb

theorem exists_gen (B : Ideal (𝓞 D.host.E)) (hB : B ≠ ⊥) : ∃ a a' : EAf D, a * a' = 1 ∧ Clears a' (B : FI D) ∧
    Clears a (B : FI D)⁻¹ ∧ ∀ Q : Pl D.host.E, ¬ Q.asIdeal ∣ B → cpt Q a = 1 := by
  obtain ⟨m, n, β, -, -, hmn, hmB, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator B hB
  obtain ⟨f, hff, -, h1, h0⟩ := exists_idem (D := D) {Q | B ≤ Q.asIdeal}
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : eToEAf D (β : D.host.E) * eToEAf D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have c1 : ∀ (x : D.host.E) (Q : Pl D.host.E), B ≤ Q.asIdeal →
      cpt Q (f * eToEAf D x + (1 - f)) = algebraMap _ _ x := fun x Q hQ => by
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1 Q hQ, cpt_rat]; simp
  have c0 : ∀ (x : D.host.E) (Q : Pl D.host.E), ¬ B ≤ Q.asIdeal →
      cpt Q (f * eToEAf D x + (1 - f)) = 1 := fun x Q hQ => by
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h0 Q hQ]; simp
  refine ⟨f * eToEAf D β + (1 - f), f * eToEAf D (β : D.host.E)⁻¹ + (1 - f), ?_, fun c hc => ?_, fun c hc => ?_,
    fun Q hQ => c0 _ Q fun h => hQ (Ideal.dvd_iff_le.2 h)⟩
  · exact mix_inv hff hinv
  · obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_mul, cpt_rat]
    by_cases hQ : B ≤ Q.asIdeal
    · rw [c1 _ Q hQ, ← map_mul]
      obtain ⟨d, hd⟩ := hdvd b hb
      have hn : (n : 𝓞 D.host.E) ∉ Q.asIdeal := fun hn => Q.isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ (by
          obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hmn).map (Int.castRingHom (𝓞 D.host.E))
          simp only [map_natCast] at huv
          exact huv ▸ add_mem (Ideal.mul_mem_left _ _ (hQ hmB)) (Ideal.mul_mem_left _ _ hn)) isUnit_one)
      refine int_of_mul Q hn (o := d) ?_
      have hd' := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hd
      rw [map_mul, map_mul] at hd'
      rw [← mul_assoc, mul_inv_eq_iff_eq_mul₀ hβE, mul_comm (d : D.host.E)]
      exact hd'
    · rw [c0 _ Q hQ, mul_one]
      exact int_of_eq Q (o := b) rfl
  · have hB' : (B : FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hB
    have key : ∀ b ∈ B, ∃ o : 𝓞 D.host.E, (b : D.host.E) * c = o := fun b hb => by
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1
        ((FractionalIdeal.mem_inv_iff hB').1 hc _ (FractionalIdeal.mem_coeIdeal_of_mem _ hb))
      exact ⟨o, by rw [mul_comm]; exact ho.symm⟩
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_mul, cpt_rat]
    by_cases hQ : B ≤ Q.asIdeal
    · rw [c1 _ Q hQ, ← map_mul]
      obtain ⟨o, ho⟩ := key β hβB
      exact int_of_eq Q (o := o) ((mul_comm _ _).trans ho)
    · rw [c0 _ Q hQ, mul_one]
      obtain ⟨b, hb, hbQ⟩ := SetLike.not_le_iff_exists.1 hQ
      obtain ⟨o, ho⟩ := key b hb
      exact int_of_mul Q hbQ ho

theorem exists_gen_AA (D : D7) : ∃ a a' : EAf D, a * a' = 1 ∧ Clears a' D.host.AA ∧ Clears a D.host.AA⁻¹ ∧
    ∀ Q : Pl D.host.E, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q a = 1 := by
  obtain ⟨a, a', ha, h1, h2, h3⟩ := exists_gen D.host.ccE (GlobalTheory.HalfCompare.ccE_ne_bot D)
  obtain ⟨b, b', hb, k1, k2, k3⟩ := exists_gen D.host.𝔟 (ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D)
  refine ⟨a * b', a' * b, by linear_combination b * b' * ha + hb, h1.mul k2, ?_, fun Q hQ => ?_⟩
  · have := h2.mul k1
    unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
    rwa [mul_inv, inv_inv]
  · obtain ⟨q1, q2⟩ := (GlobalTheory.HalfCompare.primeToAA_iff Q).1 (GlobalTheory.HalfCompare.primeToAA_of_not_mem hQ)
    have := congrArg (cpt Q) hb
    rw [RingHom.map_mul, k3 Q q2, one_mul, RingHom.map_one] at this
    rw [RingHom.map_mul, h3 Q q1, this, one_mul]

theorem cpt_sg_eq_one {Q : Pl D.host.E} {a : EAf D} (h : cpt (cP Q) a = 1) : cpt Q (sg D a) = 1 := by
  have k2 : cpt Q (sg D (a - 1)) = 0 := cpt_sg_eq_zero (by rw [RingHom.map_sub, h, RingHom.map_one, sub_self])
  rwa [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, sub_eq_zero] at k2

theorem exists_twist (D : D7) : ∃ U : AE D, U * cA D U = 1 ∧ infPart D U = 1 ∧
    Clears (toEAf D U) (D.host.AA * D.host.AAbar⁻¹) ∧ Clears (toEAf D (cA D U)) (D.host.AAbar * D.host.AA⁻¹) ∧
    ∀ Q : Pl D.host.E, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q (toEAf D U) = 1 := by
  obtain ⟨a, a', ha, h1, h2, h3⟩ := exists_gen_AA D
  obtain ⟨z, hz, hz'⟩ := (comp_toAd D).surj (toAd D (a' * sg D a - 1))
  have e1 : toEAf D (1 + z) = a' * sg D a := by
    have : toEAf D z = a' * sg D a - 1 := GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) hz'
    rw [RingHom.map_add, RingHom.map_one, this]; ring
  have e2 : toEAf D (cA D (1 + z)) = sg D a' * a := by rw [GlobalTheory.StdFrames.toEAf_cA, e1, RingHom.map_mul, sg_sg]
  have e3 : infPart D (1 + z) = 1 := by rw [RingHom.map_add, RingHom.map_one, hz, add_zero]
  have ha' : sg D a * sg D a' = 1 := by rw [← RingHom.map_mul, ha, RingHom.map_one]
  refine ⟨1 + z, (comp_toAd D).ext' ?_ fun Q => ?_, e3, ?_, ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_mul, (parts_cA _).1, e3, RingHom.map_one, RingHom.map_one, one_mul]
  · have : toEAf D ((1 + z) * cA D (1 + z)) = toEAf D 1 := by
      rw [RingHom.map_mul, e1, e2, RingHom.map_one]; exact cross_inv ha ha'
    exact congrArg (fun t => toAd D t Q) this
  · rw [e1]; exact h1.mul (h2.conj (starLE_inv AAbar_ne AA_ne starLE_AA))
  · rw [e2]; exact (h1.conj starLE_AAbar).mul h2
  · have k1 := congrArg (cpt Q) ha
    rw [RingHom.map_mul, h3 Q hQ, one_mul, RingHom.map_one] at k1
    have k2 := cpt_sg_eq_one (h3 _ ((natCast_mem_cP Q _).not.2 hQ))
    rw [e1, RingHom.map_mul, k1, k2, one_mul]

theorem idemSum_mul {U ε : AE D} {P : Finset (Pl D.host.E)} (hε : IsIdemSum ε P) (hU : ∀ Q ∈ P, cpt Q (toEAf D U) = 1) :
    ε * U = ε := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hε
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => (comp_toAd D).ext' ?_ fun Q => ?_
  · rw [RingHom.map_mul, (delta_of_isIdemAt (comp_toAd D) (hes w hw)).1, zero_mul]
  · change cpt Q (toEAf D _) = cpt Q (toEAf D _)
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases h : Q = w
    · rw [h, hU w hw, mul_one]
    · rw [(cpt_of_isIdemAt (hes w hw)).2 Q h, zero_mul]

open GlobalTheory.AdelicLatMove in

theorem smul_mem_latO {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT LT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {U : AE D} {I J : FI D} (hIJ : I * J = 1)
    (hU : Clears (toEAf D U) J) (hL : ∀ d ∈ I, ∀ t ∈ LT, d • t ∈ LT') {y : WO S T}
    (hy : y ∈ latO S T LS LT fun _ => True) : U • y ∈ latO S T LS LT' fun _ => True := by
  induction hy using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : ∀ (s : Fin S.rank → EAf D) (t : Fin T.rank → EAf D),
        U • rankOne S T a s t = rankOne S T a s (toEAf D U • t) := fun s t => by
      ext i j
      simp only [rankOne, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.smul_apply, ← finEmb_mul]
      congr 1
      rw [← mul_assoc, mul_left_comm (eToEAf D a), ← mul_assoc]
    rw [← e, e2]
    refine rankOne_mem_latO S T LS LT' a ha _ (pure_mem_hatL LS 1 (one_mem _) s hs) _ ?_
    have h1 : (1 : D.host.E) ∈ I * J := hIJ ▸ FractionalIdeal.one_mem_one _
    have key : (eToEAf D 1 * toEAf D U) • (fun i => t i ⊗ₜ[D.host.F] α : Fin T.rank → EAf D) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) LT' := by
      refine FractionalIdeal.mul_induction_on (C := fun x => (eToEAf D x * toEAf D U) •
        (fun i => t i ⊗ₜ[D.host.F] α : Fin T.rank → EAf D) ∈ Formalism.L2.Herm.hatL (F := D.host.F) LT') h1
        (fun d hd c hc => ?_) (fun x y hx hy => ?_)
      · have h2 := Submodule.smul_mem _ (⟨_, hU c hc⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
          (pure_mem_hatL LT' α hα _ (hL d hd t ht))
        have h3 : (fun i => (d • t) i ⊗ₜ[D.host.F] α : Fin T.rank → EAf D) =
            eToEAf D d • (fun i => t i ⊗ₜ[D.host.F] α : Fin T.rank → EAf D) := by
          funext i
          change _ = (d ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) * (t i ⊗ₜ[D.host.F] α)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
        have h4 : (eToEAf D c * toEAf D U) • (fun i => (d • t) i ⊗ₜ[D.host.F] α : Fin T.rank → EAf D) ∈
            Formalism.L2.Herm.hatL (F := D.host.F) LT' := h2
        rwa [h3, smul_smul, mul_comm (eToEAf D c * toEAf D U), ← mul_assoc, ← RingHom.map_mul] at h4
      · rw [RingHom.map_add, add_mul, add_smul]; exact add_mem hx hy
    rwa [RingHom.map_one, one_mul] at key
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

open GlobalTheory.RouteSeesaw GlobalTheory.Doubling

def stack {A B : HSp D} {n : ℕ} (x : Mx D A.rank n) (y : Mx D B.rank n) : Mx D (A.rank + B.rank) n :=
  pairVec finSumFinEquiv x y

theorem topR_stack {A B : HSp D} {n : ℕ} (x : Mx D A.rank n) (y : Mx D B.rank n) : topR (stack x y) = x :=
  funext fun i => pairVec_inl finSumFinEquiv x y i

theorem botR_stack {A B : HSp D} {n : ℕ} (x : Mx D A.rank n) (y : Mx D B.rank n) : botR (stack x y) = y :=
  funext fun i => pairVec_inr finSumFinEquiv x y i

theorem rows_ext {A B : HSp D} {n : ℕ} {x y : Mx D (A.rank + B.rank) n} (h : topR x = topR y) (h' : botR x = botR y) :
    x = y := by
  funext k
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · exact congrFun h i
  · exact congrFun h' i

theorem mem_latO_sum {S A B : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {LB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {x : WO S (hsum A B)} :
    x ∈ latO S (hsum A B) LS (GlobalTheory.Doubling.sumLat finSumFinEquiv LA LB) P ↔
      topR (A := A) (B := B) x ∈ latO S A LS LA P ∧ botR (A := A) (B := B) x ∈ latO S B LS LB P := by
  constructor
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact ⟨AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, _, ht.1, rfl⟩,
        AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, _, ht.2, rfl⟩⟩
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add y z _ _ hy hz => exact ⟨add_mem hy.1 hz.1, add_mem hy.2 hz.2⟩
    | neg y _ hy => exact ⟨neg_mem hy.1, neg_mem hy.2⟩
  · rintro ⟨h1, h2⟩
    have k1 : ∀ y ∈ latO S A LS LA P, (stack (B := B) y 0 : WO S (hsum A B)) ∈
        latO S (hsum A B) LS (GlobalTheory.Doubling.sumLat finSumFinEquiv LA LB) P := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, pairVec finSumFinEquiv t 0,
          (pairVec_mem_sumLat _).2 ⟨ht, zero_mem _⟩, rows_ext ?_ ?_⟩
        · rw [topR_stack]; ext i j
          exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z * _)) (pairVec_inl finSumFinEquiv t 0 i).symm
        · rw [botR_stack]; ext i j
          refine Eq.trans ?_
            (congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z * _)) (pairVec_inr finSumFinEquiv t 0 i).symm)
          simp
      | zero =>
        rw [show stack (A := A) (B := B) (0 : Mx D _ S.rank) 0 = 0 from rows_ext (topR_stack _ _) (botR_stack _ _)]
        exact zero_mem _
      | add y z _ _ hy hz =>
        rw [show stack (A := A) (B := B) (y + z) 0 = stack y 0 + stack z 0 from rows_ext
          ((topR_stack _ _).trans (congrArg₂ (· + ·) (topR_stack _ _) (topR_stack _ _)).symm)
          ((botR_stack _ _).trans ((congrArg₂ (· + ·) (botR_stack _ _) (botR_stack _ _)).trans (add_zero _)).symm)]
        exact add_mem hy hz
      | neg y _ hy =>
        rw [show stack (A := A) (B := B) (-y) 0 = -stack y 0 from rows_ext
          ((topR_stack _ _).trans (congrArg (- ·) (topR_stack _ _)).symm)
          ((botR_stack _ _).trans ((congrArg (- ·) (botR_stack _ _)).trans neg_zero).symm)]
        exact neg_mem hy
    have k2 : ∀ y ∈ latO S B LS LB P, (stack (A := A) 0 y : WO S (hsum A B)) ∈
        latO S (hsum A B) LS (GlobalTheory.Doubling.sumLat finSumFinEquiv LA LB) P := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, pairVec finSumFinEquiv 0 t,
          (pairVec_mem_sumLat _).2 ⟨zero_mem _, ht⟩, rows_ext ?_ ?_⟩
        · rw [topR_stack]; ext i j
          refine Eq.trans ?_
            (congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z * _)) (pairVec_inl finSumFinEquiv 0 t i).symm)
          simp
        · rw [botR_stack]; ext i j
          exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z * _)) (pairVec_inr finSumFinEquiv 0 t i).symm
      | zero =>
        rw [show stack (A := A) (B := B) (0 : Mx D _ S.rank) 0 = 0 from rows_ext (topR_stack _ _) (botR_stack _ _)]
        exact zero_mem _
      | add y z _ _ hy hz =>
        rw [show stack (A := A) (B := B) 0 (y + z) = stack 0 y + stack 0 z from rows_ext
          ((topR_stack _ _).trans ((congrArg₂ (· + ·) (topR_stack _ _) (topR_stack _ _)).trans (add_zero _)).symm)
          ((botR_stack _ _).trans (congrArg₂ (· + ·) (botR_stack _ _) (botR_stack _ _)).symm)]
        exact add_mem hy hz
      | neg y _ hy =>
        rw [show stack (A := A) (B := B) 0 (-y) = -stack 0 y from rows_ext
          ((topR_stack _ _).trans ((congrArg (- ·) (topR_stack _ _)).trans neg_zero).symm)
          ((botR_stack _ _).trans (congrArg (- ·) (botR_stack _ _)).symm)]
        exact neg_mem hy
    have e : x = stack (topR (A := A) (B := B) x) 0 + stack 0 (botR (A := A) (B := B) x) := rows_ext
      ((congrArg₂ (· + ·) (topR_stack _ _) (topR_stack _ _)).trans (add_zero _)).symm
      ((congrArg₂ (· + ·) (botR_stack _ _) (botR_stack _ _)).trans (zero_add _)).symm
    rw [e]
    exact add_mem (k1 _ h1) (k2 _ h2)

def scal (V : HSp D) (U : AE D) (hU : U * cA D U = 1) : GA D V :=
  ⟨⟨U • 1, cA D U • 1, by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hU, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm, hU, one_smul]⟩, by
    change Formalism.UG.cT (cA D) (U • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) * _ * (U • 1) = _
    have hm : Formalism.UG.cT (cA D) (U • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = cA D U • 1 := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h1 : j = i
      · subst h1; simp
      · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
    rw [hm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hU, one_smul]⟩

theorem act_blk {S A B : HSp D} {U : AE D} (hU : U * cA D U = 1) (x : WO S (hsum A B)) :
    actO S (hsum A B) 1 (blk A B (1, scal B U hU)) x =
      stack (topR (A := A) (B := B) x) (U • botR (A := A) (B := B) x) := by
  have e : actO S (hsum A B) 1 (blk A B (1, scal B U hU)) x =
      blkMat finSumFinEquiv (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))
        (U • (1 : Matrix (Fin B.rank) (Fin B.rank) (AE D))) * x := by
    unfold actO
    rw [inv_one, mt_one, Matrix.mul_one, mt_blk, mt_one]
    rfl
  rw [e]
  ext k j
  have h := congrFun (blkMat_mulVec finSumFinEquiv (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))
    (U • (1 : Matrix (Fin B.rank) (Fin B.rank) (AE D))) (fun i => x (finSumFinEquiv (.inl i)) j)
    (fun i => x (finSumFinEquiv (.inr i)) j)) k
  rw [pairVec_eta finSumFinEquiv (fun k => x k j), smul_mulVec, one_mulVec, one_mulVec] at h
  refine Eq.trans h ?_
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · rw [pairVec_inl]; exact (congrFun (pairVec_inl finSumFinEquiv (topR (A := A) (B := B) x) (U • botR (A := A) (B := B) x) i) j).symm
  · rw [pairVec_inr]; exact (congrFun (pairVec_inr finSumFinEquiv (topR (A := A) (B := B) x) (U • botR (A := A) (B := B) x) i) j).symm

theorem blk_mem_GfC {A B : HSp D} {U : AE D} (hU : U * cA D U = 1) (h : infPart D U = 1) :
    blk A B (1, scal B U hU) ∈ GfC (hsum A B) := by
  refine Units.ext ?_
  change (blkMat finSumFinEquiv (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))
    (U • (1 : Matrix (Fin B.rank) (Fin B.rank) (AE D)))).map (infPart D) = 1
  have e : (U • (1 : Matrix (Fin B.rank) (Fin B.rank) (AE D))).map (infPart D) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, h, one_mul, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  rw [blkMat_map _ _ (RingHom.map_zero _), e, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), blkMat_one]

theorem smul_eq_of_half {m n : ℕ} {U e : AE D} (h : e * U = e) {x : Mx D m n} (hx : IsHalf e x) : U • x = x := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, ← hx i j, ← mul_assoc, mul_comm U, h]

open GlobalTheory.CoreOnto (scaleLat)

theorem scaleLat_pow_zero {n : ℕ} (I : FI D) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : scaleLat (I ^ 0) Λ = Λ := by
  refine le_antisymm (fun y hy => ?_) fun y hy => ?_
  · rw [pow_zero] at hy
    simpa using GlobalTheory.ScaleSelfDual.inv_smul_mem one_ne_zero (c := 1) (by rw [inv_one]; exact FractionalIdeal.one_mem_one _) hy
  · simpa using GlobalTheory.ScaleSelfDual.smul_mem_scaleLat (𝔟 := 1) (FractionalIdeal.one_mem_one _) hy

theorem adj_mem_iff {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (y : WO S T) :
    y ∈ latO S T LS (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (0 + 1)) LT) P ↔ adjM S T y ∈ latO T S LT LS P := by
  rw [← GlobalTheory.RowLoc.mem_latO_negSp (S := T)]
  constructor
  · intro h
    exact adj_mem_left (V := S) (V' := T) 0 P (by rw [scaleLat_pow_zero]; exact h)
  · intro h
    have h2 := adj_mem_right (V := S) (V' := T) 0 P h
    rw [scaleLat_pow_zero] at h2
    exact GlobalTheory.AdjLawPf.adj_invol S T y ▸ h2

theorem adjM_negSp (S T : HSp D) (y : WO S T) : adjM S (GlobalTheory.ChiGrid.negSp T) y = -adjM S T y := by
  have e : ((GlobalTheory.ChiGrid.negSp T).gram).map (incA D) = -(T.gram.map (incA D)) := Matrix.map_neg _ (map_neg _) _
  unfold adjM
  rw [e, Matrix.mul_neg]

theorem latO_neg (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (GlobalTheory.Grid.neg S) T LS LT P = latO (GlobalTheory.ChiGrid.negSp S) T LS LT P := by
  unfold latO
  rw [GlobalTheory.Grid.neg_gram]
  rfl

end GlobalTheory.TopFlip.TwistElt

open GlobalTheory.TopFlip.TwistElt GlobalTheory.LatExchPf GlobalTheory.RouteSeesaw in

theorem GlobalTheory.TopFlip.exists_twistElt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ i j : Fin D.R.m, ∃ h ∈ GfC (spX G i j), ∃ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E),
      IsSelfDualC (spX G i j) Λ ∧
      (∀ t, SquareStanding G t → ∀ ε, IsIdemSum ε (locPl G t) → ∀ (S : HSp D) (x : WO S (spX G i j)),
        IsHalf ε x ∨ IsHalf (cA D ε) x → actO S (spX G i j) 1 h x = x) ∧
      (∀ (S : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S ΛS → ∀ u : WO S (spX G i j),
        u ∈ latO S (spX G i j) ΛS Λ (fun _ => True) ↔
          ∃ u₀ ∈ latO S (spX G i j) ΛS (latX G i j) (fun _ => True), u = actO S (spX G i j) 1 h u₀) ∧
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j ∧
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j := by
  intro D T L sc G μ₀ hL i j
  obtain ⟨U, hU, hinf, c1, c2, hloc⟩ := exists_twist D
  have hV : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1))) := (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
  have hV₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid (i + 1) j)) := (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd
  have hb : (D.host.AAbar * D.host.AA⁻¹) ^ (0 + 1) = D.host.AAbar * D.host.AA⁻¹ := pow_one _
  have hbi : ((D.host.AAbar * D.host.AA⁻¹) ^ (0 + 1))⁻¹ = D.host.AA * D.host.AAbar⁻¹ := by
    rw [hb, mul_inv, inv_inv, mul_comm]
  refine ⟨blk _ _ (1, scal _ U hU), blk_mem_GfC hU hinf, GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1)))
    (GlobalTheory.CoreOnto.scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ (0 + 1)) (G.Λ (.grid (i + 1) j))),
    GlobalTheory.Twist.OrthSum.selfDual_hsum hV (GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual D _ _ hV₁ _).1,
    fun t ht ε hε S x hx => ?_, fun S ΛS _ u => ?_, ?_, ?_⟩
  · have h1 : ε * U = ε := idemSum_mul hε fun Q hQ => hloc Q fun h => ht.2 Q hQ (by
      rw [show D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK = D.host.d * GlobalTheory.HalfCompare.badInt D by ring, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ h)
    have h2 : cA D ε * U = cA D ε := by
      have h3 : ε * cA D U = ε := by rw [← h1, mul_assoc, hU, mul_one, h1]
      have h4 := congrArg (cA D) h3
      rwa [RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA] at h4
    have h5 : U • botR x = botR x := by
      rcases hx with hx | hx
      · exact smul_eq_of_half h1 fun a b => hx _ b
      · exact smul_eq_of_half h2 fun a b => hx _ b
    rw [act_blk, h5]
    exact rows_ext (topR_stack _ _) (botR_stack _ _)
  · rw [mem_latO_sum]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨stack (topR u) (cA D U • botR u), mem_latO_sum.2 ?_, ?_⟩
      · rw [topR_stack, botR_stack]
        exact ⟨h1, smul_mem_latO ((mul_comm _ _).trans b_mul_c) c2 (fun d hd t ht =>
          GlobalTheory.ScaleSelfDual.inv_smul_mem (GlobalTheory.ScaleSelfDual.twist_ne_zero D _) (hbi ▸ hd) ht) h2⟩
      · rw [act_blk, topR_stack, botR_stack, smul_smul, hU, one_smul]
        exact (rows_ext (topR_stack _ _) (botR_stack _ _)).symm
    · rintro ⟨u₀, h0, rfl⟩
      obtain ⟨h1, h2⟩ := mem_latO_sum.1 h0
      rw [act_blk, topR_stack, botR_stack]
      exact ⟨h1, smul_mem_latO b_mul_c c1 (fun d hd t ht => GlobalTheory.ScaleSelfDual.smul_mem_scaleLat (hb.symm ▸ hd) ht) h2⟩
  · ext x
    refine mem_latO_sum.trans (and_congr ?_ ?_)
    · rw [latO_neg]
    · rw [latO_neg]
      exact GlobalTheory.RowLoc.mem_latO_negSp.trans (adj_mem_iff _)
  · ext x
    refine mem_latO_sum.trans (and_congr Iff.rfl ((adj_mem_iff _).trans ?_))
    rw [adjM_negSp]
    exact (neg_mem_iff.trans GlobalTheory.RowLoc.mem_latO_negSp).symm

end
