import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction

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

namespace GlobalTheory.StdRead

variable {D : D7}

theorem det_mem_intAf {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

def finHom (D : D7) : AE D →* Formalism.MainNotions.StandardLatticesGL3.AE D :=
  ((GlobalTheory.BotFormula.toAfE D).symm.toRingHom.comp (finPart D)).toMonoidHom

theorem isFinIdl_map (x : (AE D)ˣ) (h : infPart D (x : AE D) = 1) : IsFinIdl x (Units.map (finHom D) x) := by
  refine ⟨h, ?_⟩
  change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))
  rw [← GlobalTheory.BotClassDict.finAdEquiv_toAfE, RingEquiv.apply_symm_apply]

theorem intU_map (x : (AE D)ˣ) (h : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IntU D (Units.map (finHom D) x) := by
  refine ⟨(GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_, (GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_⟩
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h'

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem exists_pow_cong (u : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) (hu : IntU D u) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D, ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  have hpow : ∀ k : ℕ, ((u : Formalism.MainNotions.StandardLatticesGL3.AE D)) ^ k ∈ OhE D := fun k => pow_mem hu.1 k
  choose b w hw hb using fun k => GlobalTheory.CongApprox.exists_int_approx D N hN _ (hpow k)
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have key : ∀ i j : ℕ, i < j → Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b i) =
      Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b j) →
      ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D,
        ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    intro i j hij hq
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hq.symm)
    have ht' : inc D ((b j : 𝓞 D.host.E) : D.host.E) - inc D ((b i : 𝓞 D.host.E) : D.host.E) =
        (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D ((t : 𝓞 D.host.E) : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) ht
      simp only [map_mul, map_sub, map_natCast] at this
      rw [← this, mul_comm]
    set U := (u : Formalism.MainNotions.StandardLatticesGL3.AE D)
    set V := ((u⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D)
    have hUV : U * V = 1 := Units.mul_inv u
    refine ⟨j - i, Nat.sub_pos_of_lt hij, (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) * V ^ i,
      mul_mem (sub_mem (add_mem (GlobalTheory.CongApprox.inc_mem_OhE D t) (hw j)) (hw i)) (pow_mem hu.2 i), ?_⟩
    have hj : U ^ j = U ^ (j - i) * U ^ i := by rw [← pow_add, Nat.sub_add_cancel hij.le]
    have e1 : U ^ j - U ^ i = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) := by
      rw [hb j, hb i]
      linear_combination ht'
    rw [Units.val_pow_eq_pow_val]
    calc U ^ (j - i) - 1 = (U ^ j - U ^ i) * V ^ i := by
          rw [hj, sub_mul, mul_assoc, ← mul_pow, hUV, one_pow, mul_one]
      _ = _ := by rw [e1, mul_assoc]
  obtain ⟨i, j, hij, hq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b k))
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hq
  · exact key j i h hq.symm

theorem absNorm_mem_conj (𝔪 : Ideal (𝓞 D.host.E)) : ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ 𝔪 (Ideal.absNorm_mem 𝔪)
  have h2 : D.host.conj • ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) = ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) := by
    first
    | exact smul_natCast _ _
    | simp
    | exact map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) _
  rw [h2] at this
  exact this

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem unitChar_pow_eq_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle,
    KillsCong ν 𝔪 → ∀ {n : ℕ} (β : GL (Fin n) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
    ∃ m : ℕ, 0 < m ∧ unitChar ν e β.val ^ m = 1 := by
  intro D e 𝔪 h𝔪 ν hν n β hβ hβ'
  have h0 := h𝔪.ne_bot
  obtain ⟨SS, c, he, -, -, -⟩ := h𝔪
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hd := det_mem_intAf hβ
  have hd' := det_mem_intAf hβ'
  have hdd : β.val.det * (β⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have huv : (1 - toEAf D e + toEAf D e * β.val.det) * (1 - toEAf D e + toEAf D e * (β⁻¹).val.det) = 1 := by
    linear_combination (1 - β.val.det - (β⁻¹).val.det + β.val.det * (β⁻¹).val.det) * hee + toEAf D e * hdd
  obtain ⟨x, a1, a2, a3⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit huv
  have hex : ∃ x, IsUnitDet e β.val x :=
    ⟨x, a1, a2, by rw [a3]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')⟩
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  set x0 := hex.choose
  have hx0 : toEAf D (x0 : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hN : 0 < Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0)) (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0))
  obtain ⟨m, hm, s, hs, hys⟩ := exists_pow_cong (Units.map (finHom D) x0) (intU_map x0 hx0 h3) hN
  have hinf : infPart D ((x0 ^ m : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, h1, one_pow]
  have hfin : IsFinIdl (x0 ^ m) ((Units.map (finHom D) x0) ^ m) := by
    rw [← map_pow]
    exact isFinIdl_map _ hinf
  have hU : IntU D ((Units.map (finHom D) x0) ^ m) := by
    have hu := intU_map x0 hx0 h3
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val]
      exact pow_mem hu.1 m
    · rw [← inv_pow, Units.val_pow_eq_pow_val]
      exact pow_mem hu.2 m
  have hmem : (((Units.map (finHom D) x0) ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈
      hatId D (𝔪 * D.host.conj • 𝔪) := by
    rw [hys]
    refine AddSubgroup.subset_closure ⟨((Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E), ?_, s, hs, ?_⟩
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_mul (Ideal.absNorm_mem 𝔪) (absNorm_mem_conj 𝔪)
    · simp only [map_natCast]
  have hk : ν (x0 ^ m) = 1 := hν _ _ hfin hU hmem
  have hc : ((ν x0)⁻¹ : Circle) ^ m = 1 := by rw [inv_pow, ← map_pow, hk, inv_one]
  refine ⟨m, hm, ?_⟩
  unfold unitChar
  rw [dif_pos hex]
  have := congrArg (fun z : Circle => (z : ℂ)) hc
  simpa using this

end GlobalTheory.StdRead
