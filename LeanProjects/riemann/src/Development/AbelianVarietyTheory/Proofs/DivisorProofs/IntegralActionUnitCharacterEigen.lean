import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemHatMul

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.CharVal

open GlobalTheory.BotClassDict (finQ)

variable {D : D7}

theorem toE_finQ (y : AE D) : toE D (finQ D y) = toEAf D y := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D _) = _
  rw [GlobalTheory.BotClassDict.toAfE_finQ]; rfl

theorem finQ_incA (y : D.host.E) : finQ D (incA D y) = inc D y := GlobalTheory.BotClassDict.finQ_inclR y

theorem toE_int_iff (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : toE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ y ∈ OhE D :=
  GlobalTheory.BotClassDict.toAfE_int_iff y

theorem finQ_int {y : AE D} (h : toEAf D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : finQ D y ∈ OhE D :=
  (toE_int_iff _).1 (by rwa [toE_finQ])

def rho (P : Formalism.L2.DIV.Pl D.host.E) : OhE D →+* Formalism.L2.DIV.kP P :=
  (Formalism.L2.DIV.resS D.host.F P).comp ((toE D).restrict _ _ fun y hy => (toE_int_iff y).2 hy)

theorem inc_int (b : 𝓞 D.host.E) : inc D (b : D.host.E) ∈ OhE D := by
  rw [← toE_int_iff, ← finQ_incA, toE_finQ]
  exact (Formalism.L2.DIV.oToS D.host.F D.host.E b).2

theorem rho_inc (P : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E) :
    rho P ⟨inc D (b : D.host.E), inc_int b⟩ = Ideal.Quotient.mk P.asIdeal b := by
  rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F)]
  refine congrArg (Formalism.L2.DIV.resS D.host.F P) (Subtype.ext ?_)
  change toE D (inc D _) = _
  rw [← finQ_incA, toE_finQ]
  rfl

theorem rho_hat (P : Formalism.L2.DIV.Pl D.host.E) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D P.asIdeal) :
    ∃ h : x ∈ OhE D, rho P ⟨x, h⟩ = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    refine ⟨mul_mem (inc_int b) ht, ?_⟩
    change rho P (⟨_, inc_int b⟩ * ⟨t, ht⟩) = 0
    rw [RingHom.map_mul, rho_inc, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  | zero => exact ⟨zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    refine ⟨add_mem h1 h3, ?_⟩
    change rho P (⟨_, h1⟩ + ⟨_, h3⟩) = 0
    rw [RingHom.map_add, h2, h4, add_zero]
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    refine ⟨neg_mem h1, ?_⟩
    change rho P (-⟨_, h1⟩) = 0
    rw [RingHom.map_neg, h2, neg_zero]

theorem hat_of_rho (P : Formalism.L2.DIV.Pl D.host.E) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (h : x ∈ OhE D) (h0 : rho P ⟨x, h⟩ = 0) :
    x ∈ hatId D P.asIdeal := by
  have hn : 0 < Ideal.absNorm P.asIdeal := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot)
  obtain ⟨b, w, hw, e⟩ := GlobalTheory.CongApprox.exists_int_approx D _ hn x h
  have hN : ((Ideal.absNorm P.asIdeal : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * w ∈ hatId D P.asIdeal :=
    AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem _, w, hw, by simp⟩
  obtain ⟨h1, h2⟩ := rho_hat P hN
  have e' : (⟨x, h⟩ : OhE D) = ⟨_, inc_int b⟩ + ⟨_, h1⟩ := Subtype.ext e
  rw [e', RingHom.map_add, h2, add_zero, rho_inc, Ideal.Quotient.eq_zero_iff_mem] at h0
  rw [e]
  exact add_mem (AddSubgroup.subset_closure ⟨b, h0, 1, one_mem _, (mul_one _).symm⟩) hN

theorem hat_mul {I J : Ideal (𝓞 D.host.E)} {x y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) (hy : y ∈ hatId D J) :
    x * y ∈ hatId D (I * J) := by
  first
  | exact @_root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul
  | exact _root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul
  | (apply _root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HatProductMembership.mul_mem_hat_mul ..)

theorem idem_hat_pow {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hO : x ∈ OhE D) (hxx : x * x = x)
    (hx : x ∈ hatId D I) (n : ℕ) : x ∈ hatId D (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact GlobalTheory.FunObj.SqNum.mem_hatId_top hO
  | succ n ih => rw [pow_succ, ← hxx]; exact hat_mul ih hx

theorem idem_hat_prod {ι : Type} (S : Finset ι) (I : ι → Ideal (𝓞 D.host.E)) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hO : x ∈ OhE D)
    (hxx : x * x = x) (hx : ∀ i ∈ S, x ∈ hatId D (I i)) : x ∈ hatId D (∏ i ∈ S, I i) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top]; exact GlobalTheory.FunObj.SqNum.mem_hatId_top hO
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← hxx]
    exact hat_mul (hx a (Finset.mem_insert_self a s)) (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

section Idem

variable {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}

theorem eps_int (he : IsIdemSum e S) : finQ D e ∈ OhE D := finQ_int (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he)

theorem eps_idem (he : IsIdemSum e S) : finQ D e * finQ D e = finQ D e := by
  rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]

theorem eps_conj (he : IsIdemSum e S) : finQ D e * Formalism.MainNotions.StandardLatticesGL3.sgA D (finQ D e) = 0 := by
  rw [← GlobalTheory.BotClassDict.finQ_sigR, ← RingHom.map_mul]
  exact (congrArg (finQ D) he.2).trans (RingHom.map_zero _)

theorem one_sub_eps_mem (he : IsIdemSum e S) {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) :
    1 - finQ D e ∈ hatId D P.asIdeal := by
  have hO := eps_int he
  refine hat_of_rho P (sub_mem (one_mem _) hO) ?_
  change rho P (1 - ⟨_, hO⟩) = 0
  obtain ⟨⟨es, hes, hs⟩, -⟩ := he
  have hi : ∀ P ∈ S, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun P hP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes P hP)).1
  have hr : ∀ Q (hQ : Q ∈ S), rho P ⟨_, finQ_int (hi Q hQ)⟩ = Formalism.L2.DIV.resS D.host.F P ⟨_, hi Q hQ⟩ :=
    fun Q hQ => congrArg (Formalism.L2.DIV.resS D.host.F P) (Subtype.ext (toE_finQ _))
  have e1 : (⟨_, hO⟩ : OhE D) = ∑ Q ∈ S.attach, ⟨_, finQ_int (hi Q.1 Q.2)⟩ := Subtype.ext (by
    refine Eq.trans ?_ (map_sum (OhE D).subtype _ _).symm
    change finQ D e = ∑ Q ∈ S.attach, finQ D (es Q.1)
    rw [hs, map_sum, Finset.sum_attach S fun P => finQ D (es P)])
  rw [RingHom.map_sub, RingHom.map_one, e1, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.hom_sum,
    Finset.sum_eq_single ⟨P, hP⟩ (fun Q _ hQ => ?_) (fun h => (h (Finset.mem_attach _ _)).elim), hr P hP,
    (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes P hP)).2, sub_self]
  rw [hr Q.1 Q.2]
  exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_idem_off (hes Q.1 Q.2) (fun hh => hQ (Subtype.ext hh.symm)) _

theorem not_mem_of_inert (he : IsIdemSum e S) {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) {q : ℕ}
    (hq : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) : (q : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro h
  have hc := hq P.asIdeal P.isPrime P.ne_bot h
  have h1 := one_sub_eps_mem he hP
  have h2 := GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId h1
  rw [hc, map_sub, map_one] at h2
  have h3 := add_mem h1 (GlobalTheory.FunObj.StdDatum.mul_mem_hatId (eps_int he) h2)
  rw [mul_sub, eps_conj he, mul_one, sub_zero, sub_add_cancel] at h3
  obtain ⟨h4, h5⟩ := rho_hat P h3
  have := P.isPrime
  exact one_ne_zero ((RingHom.map_one (rho P)).symm.trans h5)

theorem eps_zeroAt (he : IsIdemSum e S) {q : ℕ} (hp : q.Prime) (hq : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) :
    Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D e) := by
  intro k
  have hx0 : ((q : 𝓞 D.host.E) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hx0' : (((q : 𝓞 D.host.E) ^ k : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  refine ⟨1, one_pos, Nat.coprime_one_left _,
    finQ D (e * incA D ((((q : 𝓞 D.host.E) ^ k : 𝓞 D.host.E) : D.host.E)⁻¹)), ?_, ?_⟩
  · obtain ⟨es, hes, hs⟩ := he.1
    rw [hs, Finset.sum_mul, map_sum]
    refine sum_mem fun P hP => finQ_int (GlobalTheory.IdemRes.toEAf_mem_of_finPart ?_)
    by_contra hn
    exact not_mem_of_inert he hP hq (P.isPrime.mem_of_pow_mem k (((hes P hP).2 _ hx0).2 hn))
  · have e1 : (q : Formalism.MainNotions.StandardLatticesGL3.AE D) ^ k = inc D (((q : 𝓞 D.host.E) ^ k : 𝓞 D.host.E) : D.host.E) := by simp
    rw [RingHom.map_mul, finQ_incA, e1, mul_left_comm, ← map_mul, mul_inv_cancel₀ hx0', map_one, Nat.cast_one, one_mul,
      mul_one]

end Idem

theorem one_sub_eps_mod {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 1 - finQ D e ∈ hatId D 𝔪 := by
  obtain ⟨S, c, he, -, rfl, -⟩ := h
  have hO : 1 - finQ D e ∈ OhE D := sub_mem (one_mem _) (eps_int he)
  have hxx : (1 - finQ D e) * (1 - finQ D e) = 1 - finQ D e := by linear_combination eps_idem he
  exact idem_hat_prod S _ hO hxx fun P hP => idem_hat_pow hO hxx (one_sub_eps_mem he hP) _

theorem exists_finIdl (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : ∃ x : (AE D)ˣ, IsFinIdl x y ∧ toEAf D (x : AE D) = toE D y ∧
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = toE D (y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) := by
  obtain ⟨x, h1, h2, h3⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit (u := toE D y)
    (v := toE D (y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ)) (by rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  refine ⟨x, ⟨h1, ?_⟩, h2, h3⟩
  have e : finPart D (x : AE D) = GlobalTheory.BotFormula.toAfE D y :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h2
  rw [e]
  exact GlobalTheory.BotClassDict.finAdEquiv_toAfE _

variable {δ t0 : ℂ} {Q : ℕ}

theorem om_split (P : Pair D ⊤ δ t0 Q) {k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hk : k ∈ intG D P.a)
    (hs : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ)
    (hy : ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q ((y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1))
    (hd : y = Matrix.GeneralLinearGroup.det (k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * Formalism.MainNotions.StandardLatticesGL3.sgU D y) :
    P.W.Om k 1 P.e0 = ((P.W.chV'.f y ^ P.W.ep' : ℂˣ) : ℂ) • P.e0 := by
  have hm : Formalism.MainNotions.StandardLatticesGL3.Moves D (k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (stdL D P.a) := by
    simpa using GlobalTheory.NormSum.VacMove.moves_mul_int hk (GlobalTheory.NormSum.VacMove.moves_one D P.a)
  have e := P.W.split k 1 y 1 (stdL D P.a) (stdL D P.d) hs (fun q _ _ => GlobalTheory.FunObj.CosetFix.trivAt_one q)
    (fun q hq hi => ⟨hy q hq hi, by simpa using GlobalTheory.FunObj.CosetFix.zeroAt_zero (D := D) q⟩) hd (by simp) hm
    (GlobalTheory.NormSum.VacMove.moves_one D P.d)
  rw [e, map_one, one_zpow, one_mul,
    show La D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d) = La0 D (tor0 D ⊤ δ) P.a P.d from rfl,
    GlobalTheory.NormSum.VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) P.a P.d) P.vac.1]
  rfl

theorem om_cong (hI : GlobalTheory.NormSum.Inp D) (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} {ν : (AE D)ˣ →* Circle}
    (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep') (hK : KillsCong ν 𝔪) {k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hk : k ∈ intG D P.a)
    (hc : CongOne D (𝔪 * D.host.conj • 𝔪) k) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨ks, ki, rfl, hs, hi, hs', hss, hii⟩ := GlobalTheory.CongSplitFactor.exists_split_inert_factor hk hc
  have hT := GlobalTheory.NormSum.VacMove.vac_TT hI.g1 P.crv P.vac.1
  have h1 : P.W.Om ki 1 P.e0 = P.e0 :=
    P.W.inert ki 1 ((GlobalTheory.NormSum.mem_intG ki).1 hi) ((GlobalTheory.NormSum.mem_intG 1).1 (one_mem _)) hii
      (fun q _ _ => GlobalTheory.FunObj.CosetFix.trivAt_one q)
  have e := P.W.mul ks ki 1 1 P.e0 hT
  rw [mul_one] at e
  obtain ⟨y, hyu, hyi, hy, h2, -⟩ := GlobalTheory.FunObj.NormUniq.SplitDet.exists_splitComp_det hs hs' hss
  obtain ⟨x, hx, -⟩ := exists_finIdl y
  rw [e, h1, om_split P hs hss y hyi hy, ← hν x y hx, MonoidHom.inv_apply, hK x y hx hyu h2, inv_one, Circle.coe_one,
    one_smul]

theorem det_phi {N : ℕ} {f : Formalism.MainNotions.StandardLatticesGL3.AE D} (hf : f * f = f) (A : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
    f * (GlobalTheory.CongSplitFactor.phi f A).det = f * A.det ∧ (1 - f) * (GlobalTheory.CongSplitFactor.phi f A).det = 1 - f := by
  have key : ∀ (g : Formalism.MainNotions.StandardLatticesGL3.AE D), g * g = g → ∀ B C : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D),
      g • B = g • C → g * B.det = g * C.det := by
    intro g hg B C h
    have h1 := congrArg (fun M => g * M.det) h
    simp only [Matrix.det_smul, ← mul_assoc] at h1
    have h2 : g * g ^ Fintype.card (Fin N) = g := by
      rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ hg
    rwa [h2] at h1
  refine ⟨key f hf _ _ ?_, ?_⟩
  · rw [GlobalTheory.CongSplitFactor.phi, smul_add, smul_smul, smul_smul, hf, show f * (1 - f) = 0 by linear_combination -hf,
      zero_smul, add_zero]
  · rw [key (1 - f) (by linear_combination hf) _ 1, Matrix.det_one, mul_one]
    rw [GlobalTheory.CongSplitFactor.phi, smul_add, smul_smul, smul_smul, show (1 - f) * f = 0 by linear_combination -hf,
      zero_smul, zero_add, show (1 - f) * (1 - f) = 1 - f by linear_combination hf]

theorem unitChar_eq (ν : (AE D)ˣ →* Circle) (e : AE D) {a : ℕ} (N : Matrix (Fin a) (Fin a) (EAf D)) {x : (AE D)ˣ}
    (hx : IsUnitDet e N x) : unitChar ν e N = (((ν x)⁻¹ : Circle) : ℂ) := by
  have h : ∃ x, IsUnitDet e N x := ⟨x, hx⟩
  have e1 : h.choose = x := Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (h.choose_spec.1.trans hx.1.symm)
    (h.choose_spec.2.1.trans hx.2.1.symm))
  unfold unitChar
  rw [dif_pos h, e1]

set_option maxHeartbeats 1000000 in

theorem om_vac_eq : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, HasFinPart ν⁻¹ P.W.chV' P.W.ep' → KillsCong ν 𝔪 →
  ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a, k ∈ intG D P.a → P.W.Om k 1 P.e0 = unitChar ν e (matE k) • P.e0 := by
  intro D hI δ t0 Q P e 𝔪 hG ν hν hK k hk
  have hm := one_sub_eps_mod hG
  obtain ⟨S, -, he, -⟩ := hG
  have hO := eps_int he
  have h1 := eps_idem he
  have h2 := eps_conj he
  have hz := fun q => eps_zeroAt (q := q) he
  have hte := toE_finQ e
  generalize finQ D e = ε at hm hO h1 h2 hz hte
  have h1' : Formalism.MainNotions.StandardLatticesGL3.sgA D ε * Formalism.MainNotions.StandardLatticesGL3.sgA D ε = Formalism.MainNotions.StandardLatticesGL3.sgA D ε := by rw [← map_mul, h1]
  have hss : Formalism.MainNotions.StandardLatticesGL3.sgA D (Formalism.MainNotions.StandardLatticesGL3.sgA D ε) = ε := GlobalTheory.NormSum.VacMove.sgA_sgA D ε
  have hm' := hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm)
  rw [map_sub, map_one] at hm'
  have hηO := GlobalTheory.NormSum.VacMove.sgA_mem D hO
  have hz' : ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (ε + Formalism.MainNotions.StandardLatticesGL3.sgA D ε) := by
    intro q hq hi n
    obtain ⟨m, a, b, s, hs, c⟩ := hz q hq hi n
    refine ⟨m, a, b, s + Formalism.MainNotions.StandardLatticesGL3.sgA D s, add_mem hs (GlobalTheory.NormSum.VacMove.sgA_mem D hs), ?_⟩
    have c' := congrArg (Formalism.MainNotions.StandardLatticesGL3.sgA D) c
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast] at c'
    rw [mul_add, mul_add, c, c']
  have hse : Formalism.MainNotions.StandardLatticesGL3.sgA D (ε + Formalism.MainNotions.StandardLatticesGL3.sgA D ε) = ε + Formalism.MainNotions.StandardLatticesGL3.sgA D ε := by rw [map_add, hss, add_comm]
  generalize hη : Formalism.MainNotions.StandardLatticesGL3.sgA D ε = η at h2 h1' hss hm' hηO hz' hse
  have hee : (ε + η) * (ε + η) = ε + η := by linear_combination h1 + h1' + 2 * h2
  have hsf : Formalism.MainNotions.StandardLatticesGL3.sgA D (1 - (ε + η)) = 1 - (ε + η) := by rw [map_sub, map_one, hse]
  have hff : (1 - (ε + η)) * (1 - (ε + η)) = 1 - (ε + η) := by linear_combination hee
  have hfO : ε + η ∈ OhE D := add_mem hO hηO
  have hf𝔪 : 1 - (ε + η) ∈ hatId D (𝔪 * D.host.conj • 𝔪) := by
    convert hm' using 1
    linear_combination -h2
  have hint := (GlobalTheory.NormSum.mem_intG k).1 hk
  have hprod : k = GlobalTheory.CongSplitFactor.part hee hse k * GlobalTheory.CongSplitFactor.part hff hsf k :=
    Subtype.ext (Units.ext (GlobalTheory.CongSplitFactor.phi_mul_compl hee _).symm)
  have hfix : P.W.Om (GlobalTheory.CongSplitFactor.part hff hsf k) 1 P.e0 = P.e0 := by
    refine om_cong hI P hν hK (GlobalTheory.CongSplitFactor.part_intG hff hsf (sub_mem (one_mem _) hfO) hk) fun i j => ?_
    rw [Matrix.sub_apply, GlobalTheory.CongSplitFactor.part_sub_one_apply, mul_comm (1 - (ε + η))]
    refine GlobalTheory.FunObj.StdDatum.mul_mem_hatId ?_ hf𝔪
    rw [Matrix.sub_apply]
    refine sub_mem (hint i j).1 ?_
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have huO := GlobalTheory.NormSum.VacMove.det_int D _ hint
  have hn := GlobalTheory.NormSum.VacMove.det_norm D k
  rw [Matrix.GeneralLinearGroup.val_det_apply] at huO hn
  obtain ⟨d1, d2⟩ := det_phi hee ((k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin P.a) (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D))
  have hdet : (matE k).det = toE D ((k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin P.a) (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).det := (RingHom.map_det (toE D) _).symm
  have hdv : ((Matrix.GeneralLinearGroup.det (GlobalTheory.CongSplitFactor.part hee hse k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = (GlobalTheory.CongSplitFactor.phi (ε + η) ((k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin P.a) (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D))).det := Matrix.GeneralLinearGroup.val_det_apply _
  generalize (GlobalTheory.CongSplitFactor.phi (ε + η) ((k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin P.a) (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D))).det = w at d1 d2 hdv
  generalize ((k : GL (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin P.a) (Fin P.a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).det = u
    at d1 huO hn hdet
  have hy : ((1 - ε) + ε * u) * ((1 - ε) + ε * Formalism.MainNotions.StandardLatticesGL3.sgA D u) = 1 := by
    linear_combination (1 - u - Formalism.MainNotions.StandardLatticesGL3.sgA D u + u * Formalism.MainNotions.StandardLatticesGL3.sgA D u) * h1 + ε * hn
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := ⟨_, _, hy, by rw [mul_comm, hy]⟩
  have hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * u := rfl
  have hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * Formalism.MainNotions.StandardLatticesGL3.sgA D u := rfl
  obtain ⟨x, hx, hx1, hx2⟩ := exists_finIdl y
  have hU : IsUnitDet e (matE k) x := by
    refine ⟨hx.1, ?_, ?_⟩
    · rw [hx1, hyv, hdet, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hte]
    · rw [hx2, toE_int_iff, hyi]
      exact add_mem (sub_mem (one_mem _) hO) (mul_mem hO (GlobalTheory.NormSum.VacMove.sgA_mem D huO))
  have hsp := om_split P (GlobalTheory.CongSplitFactor.part_intG hee hse hfO hk) (fun q hq hi i j => by
      rw [GlobalTheory.CongSplitFactor.part_sub_one_apply]
      exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq (hz' q hq hi) _) y
    (fun q hq hi => by
      convert GlobalTheory.NormSum.VacMove.zeroAt_mul D hq (hz q hq hi) (u - 1) using 1
      rw [hyv]; ring)
    (by
      ext
      rw [Units.val_mul, hdv]
      change (1 - ε) + ε * u = w * Formalism.MainNotions.StandardLatticesGL3.sgA D ((1 - ε) + ε * u)
      have hw : w = 1 - (ε + η) + (ε + η) * u := by linear_combination d1 + d2
      rw [map_add, map_mul, map_sub, map_one, hη, hw]
      linear_combination (-η) * hn + (-1 + u + Formalism.MainNotions.StandardLatticesGL3.sgA D u - u * Formalism.MainNotions.StandardLatticesGL3.sgA D u) * (h1' + h2))
  have em := P.W.mul (GlobalTheory.CongSplitFactor.part hee hse k) (GlobalTheory.CongSplitFactor.part hff hsf k) 1 1 P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT hI.g1 P.crv P.vac.1)
  rw [mul_one, ← hprod] at em
  rw [em, hfix, hsp, ← hν x y hx, MonoidHom.inv_apply, unitChar_eq ν e _ hU]

end GlobalTheory.StdRead.CharVal

end
