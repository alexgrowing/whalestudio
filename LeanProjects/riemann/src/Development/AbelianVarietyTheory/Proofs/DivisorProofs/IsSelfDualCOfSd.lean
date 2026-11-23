import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulConjSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt

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

open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LatVac
open Formalism.L2.DIV (idS oToS cmpS cmpS_inj cmpS_surj starO starO_coe)

noncomputable section

namespace GlobalTheory.IopRead

variable {D : D7}

theorem toEAf_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : toEAf D x = toEAf D y) : x = y :=
  GlobalTheory.SplitScalar.adele_ext h1 ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h2)

theorem toEAf_incA (b : 𝓞 D.host.E) :
    toEAf D (incA D (b : D.host.E)) = (oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

theorem mem_of_oToS {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) {b : 𝓞 D.host.E}
    (h : oToS D.host.F D.host.E b ∈ idS D.host.F I) : b ∈ I := by
  have h1 : cmpS D.host.F I (Ideal.Quotient.mk I b) = cmpS D.host.F I 0 := by
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (cmpS_inj I hI h1)

set_option maxHeartbeats 1600000 in

theorem exists_near_idem {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) {N : ℕ} (hN : 0 < N)
    (hNm : (N : 𝓞 D.host.E) ∈ 𝔪) :
    ∃ (μ : 𝓞 D.host.E) (s : AE D), finPart D s ∈ intAE D ∧
      finPart D (incA D (μ : D.host.E)) = finPart D (e + (N : AE D) * s) ∧ 1 - μ ∈ 𝔪 ∧
      ∃ k : 𝓞 D.host.E, μ * starO μ = N * k := by
  have h𝔪 := h.ne_bot
  obtain ⟨SS, c, he, -, rfl, -⟩ := h
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he
  have hI : Ideal.span {(N : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have hid : idS D.host.F (Ideal.span {(N : 𝓞 D.host.E)}) =
      Ideal.span {(N : Formalism.L2.Herm.intAf D.host.F D.host.E)} := by
    rw [idS, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨q, hq⟩ := cmpS_surj (F := D.host.F) _ hI (Ideal.Quotient.mk _ ⟨_, heO⟩)
  obtain ⟨μ, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : oToS D.host.F D.host.E μ - ⟨_, heO⟩ ∈ idS D.host.F (Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.Quotient.eq.1 hq
  rw [hid, Ideal.mem_span_singleton'] at h1
  obtain ⟨s', hs'⟩ := h1
  obtain ⟨s, -, hs⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (s' : EAf D)
  have hsi : finPart D s ∈ intAE D := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by rw [hs]; exact s'.2)
  have h2 : toEAf D (incA D (μ : D.host.E)) = toEAf D (e + (N : AE D) * s) := by
    have := congrArg Subtype.val hs'
    simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast] at this
    rw [toEAf_incA, RingHom.map_add, RingHom.map_mul, map_natCast, hs]
    linear_combination -this
  have h3 : finPart D (incA D (μ : D.host.E)) = finPart D (e + (N : AE D) * s) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h2
  refine ⟨μ, s, hsi, h3, mem_of_oToS h𝔪 ?_, ?_⟩
  · have : oToS D.host.F D.host.E (1 - μ) = t - oToS D.host.F D.host.E N * s' := by
      apply Subtype.ext
      have := congrArg Subtype.val hs'
      simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast] at this
      simp only [map_sub, map_one, map_natCast, Subring.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast,
        OneMemClass.coe_one, hte]
      linear_combination this
    rw [this]
    exact sub_mem ht (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hNm))
  · have h4 : finPart D (incA D (starO μ : D.host.E)) = finPart D (cA D e + (N : AE D) * cA D s) := by
      rw [starO_coe, ← GlobalTheory.DualPairCheck.cA_incA, Formalism.IndefR.Fin.finPart_cA, h3, ← Formalism.IndefR.Fin.finPart_cA,
        RingHom.map_add (cA D), RingHom.map_mul (cA D), map_natCast]
    have h5 : toEAf D (incA D (starO μ : D.host.E)) = toEAf D (cA D e + (N : AE D) * cA D s) :=
      congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) h4
    have hc : ∀ x : AE D, toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
        toEAf D (cA D x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x hx =>
      GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem (by
        rw [Formalism.IndefR.Fin.finPart_cA]; exact Formalism.IndefR.Fin.cF_int (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx))
    have hs1 : toEAf D s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [hs]; exact s'.2
    have h6 : toEAf D e * toEAf D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, RingHom.map_zero]
    have h7 : μ * starO μ ∈ Ideal.span {(N : 𝓞 D.host.E)} := by
      refine mem_of_oToS hI ?_
      rw [hid, Ideal.mem_span_singleton']
      refine ⟨⟨_, heO⟩ * ⟨_, hc s hs1⟩ + ⟨_, hs1⟩ * ⟨_, hc e heO⟩ + N * (⟨_, hs1⟩ * ⟨_, hc s hs1⟩), Subtype.ext ?_⟩
      rw [map_mul, Subring.coe_mul _ (oToS _ _ μ), ← toEAf_incA, ← toEAf_incA, h2, h5]
      simp only [Subring.coe_mul, Subring.coe_add, SubringClass.coe_natCast, RingHom.map_add, RingHom.map_mul, map_natCast]
      linear_combination -h6
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.1 h7
    exact ⟨k, hk⟩

theorem starO_mem_conj {𝔪 : Ideal (𝓞 D.host.E)} {x : 𝓞 D.host.E} (hx : x ∈ 𝔪) : starO x ∈ D.host.conj • 𝔪 := by
  have : starO x = D.host.conj • x := by
    apply RingOfIntegers.ext
    rw [starO_coe]
    exact GlobalTheory.SkewLatSelfDual.star_eq_conj _
  rw [this]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hx

theorem starO_one_sub (x : 𝓞 D.host.E) : starO (1 - x) = 1 - starO x := by
  exact (map_sub Formalism.L2.DIV.starOHom 1 x).trans (by rw [map_one]; rfl)

theorem coprime_conj {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : IsCoprime 𝔪 (D.host.conj • 𝔪) := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.ne_bot)
  obtain ⟨μ, s, -, -, h1, k, hk⟩ := exists_near_idem h hn (Ideal.absNorm_mem 𝔪)
  have h2 := starO_mem_conj h1
  rw [starO_one_sub] at h2
  refine Ideal.isCoprime_iff_exists.2 ⟨(1 - μ) * starO μ + μ * starO μ, add_mem (Ideal.mul_mem_right _ _ h1) ?_,
    1 - starO μ, h2, by ring⟩
  rw [hk]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem 𝔪)

variable {S T : HSp D}

theorem isSelfDualC_of_sd {V : HSp D} (hV : V.gram = 1) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Formalism.MainNotions.StandardLatticesGL3.SD D L) : IsSelfDualC V L := by
  have hL' : IsSDLat D.host.E V.rank L := hL
  refine ⟨⟨hL'.1, hL'.2.1⟩, fun y => ?_⟩
  rw [hL'.2.2 y]
  refine forall₂_congr fun x _ => ?_
  have e : ∑ i, ∑ j, star (x i) * V.gram i j * y j = stdH D.host.E V.rank x y := by
    rw [hV, stdH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ stdL D N ↔ ∀ i, x i ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]

theorem mem_latRat_iff (hc : D.host.ccK = ⊤) (hS : S.gram = 1) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hLT : ∀ x, x ∈ LT ↔ ∀ i, x i ∈ I)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) ↔
      ∀ i j, M i j ∈ D.host.AA0 * I := by
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    simp [hS, Matrix.one_apply]
  constructor
  · intro hM i j
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [GlobalTheory.AdForm.RatLat.AA_eq hc] at ha
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((mem_stdL s).1 hs j)
      have h1 := Submodule.smul_mem ((D.host.AA0 * I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) (starO o) (FractionalIdeal.mul_mem_mul ha ((hLT t).1 ht i))
      have h2 : genMap S T a s t i j = starO o • (a * t i) := by
        rw [genMap, Matrix.of_apply, hg, ← ho, mul_comm, Algebra.smul_def]
        rfl
      rw [h2]
      exact h1
    | zero => exact FractionalIdeal.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem (_ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).coeToSubmodule hx hy
    | neg x _ hx => exact Submodule.neg_mem (_ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).coeToSubmodule hx
  · intro hM
    rw [Matrix.matrix_eq_sum_single M]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    refine FractionalIdeal.mul_induction_on (C := fun r => Matrix.single i j r ∈
      latRat S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))) (hM i j) ?_ ?_
    · intro a ha b hb
      refine AddSubgroup.subset_closure ⟨a, by rwa [GlobalTheory.AdForm.RatLat.AA_eq hc], Pi.single j 1, (mem_stdL _).2 fun k => ?_,
        Pi.single i b, (hLT _).2 fun k => ?_, ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [FractionalIdeal.one_mem_one _, FractionalIdeal.zero_mem _]
      · rw [Pi.single_apply]
        split_ifs
        exacts [hb, FractionalIdeal.zero_mem _]
      · refine Matrix.ext fun k l => ?_
        rw [genMap, Matrix.of_apply, hg, Matrix.single_apply, Pi.single_apply, Pi.single_apply]
        by_cases h1 : k = i
        · by_cases h2 : l = j
          · simp [h1, h2]
          · simp [h2, Ne.symm h2]
        · simp [h1, Ne.symm h1]
    · intro x y hx hy
      rw [Matrix.single_add]
      exact add_mem hx hy

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice in
theorem bb_ne_zero (D : D7) : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun h =>
  inverseHalfDifferent_ne_zero D (by rw [Formalism.BasicNotions.Host.AA0, h, inv_zero])

def idGrp (I : Ideal (𝓞 D.host.E)) : AddSubgroup (EAf D) :=
  (idS D.host.F I).toAddSubgroup.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.toAddMonoidHom

theorem inId_iff {I : Ideal (𝓞 D.host.E)} {z : EAf D} : InId I z ↔ z ∈ idGrp I :=
  ⟨fun ⟨h, h'⟩ => ⟨⟨z, h⟩, h', rfl⟩, by rintro ⟨t, ht, rfl⟩; exact ⟨t.2, ht⟩⟩

theorem mul_mem_idGrp {I : Ideal (𝓞 D.host.E)} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {b : 𝓞 D.host.E} (hb : b ∈ I) : c * toEAf D (incA D (b : D.host.E)) ∈ idGrp I :=
  ⟨⟨c, hc⟩ * oToS D.host.F D.host.E b, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb), rfl⟩

set_option maxHeartbeats 1600000 in

theorem inId_of_mem (hc : D.host.ccK = ⊤) (hS : S.gram = 1) {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪)
    {u : WO S T} (hu : u ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (skewLat D 𝔪 T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) (i : Fin T.rank) (j : Fin S.rank) :
    toEAf D (e * u i j) ∈ idGrp 𝔪 := by
  have hcop := coprime_conj h
  have h𝔪 := h.ne_bot
  obtain ⟨SS, c, ⟨⟨es, hes, he⟩, -⟩, hpos, h𝔪e, hb⟩ := h
  obtain ⟨μ, hμ, β, hβ, hsum⟩ := Ideal.isCoprime_iff_exists.1 (hb.mul_right hcop)
  have hβP : ∀ P ∈ SS, β ∉ P.asIdeal := fun P hP hh => by
    have h1 : 𝔪 ≤ P.asIdeal := by
      rw [h𝔪e]
      exact Ideal.le_of_dvd ((dvd_pow_self _ (hpos P hP).ne').trans
        (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hP))
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ add_mem (h1 hμ) hh))
  have hb0 := bb_ne_zero D
  have hn0 := GlobalTheory.SkewLatSelfDual.coe_ne_zero (GlobalTheory.SkewLatSelfDual.conj_smul_ne_bot h𝔪)
  refine latO_induction (p := fun u => toEAf D (e * u i j) ∈ idGrp 𝔪) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := (mem_latRat_iff hc hS (GlobalTheory.SkewLatSelfDual.mem_skewLat (𝔪 := 𝔪)) M).1 hM i j
    have h2 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ (P := D.host.E) hβ) h1
    rw [FractionalIdeal.coeIdeal_mul, Formalism.BasicNotions.Host.AA0, mul_mul_mul_comm, mul_inv_cancel₀ hb0, one_mul,
      mul_div_cancel₀ _ hn0] at h2
    obtain ⟨m, hm, hme⟩ := (FractionalIdeal.mem_coeIdeal _).1 h2
    have hme' : (m : D.host.E) = (β : D.host.E) * M i j := hme
    rw [he, Finset.sum_mul, show toEAf D (∑ P ∈ SS, es P * finTens α M i j) = ∑ P ∈ SS, toEAf D (es P * finTens α M i j) from
      map_sum (toEAf D).toAddMonoidHom _ SS]
    refine sum_mem fun P hP => ?_
    have hβ0 : β ≠ 0 := fun hh => hβP P hP (hh ▸ zero_mem _)
    have hβ0' : (β : D.host.E) ≠ 0 := fun hh => hβ0 (RingOfIntegers.ext hh)
    have h3 : finPart D (es P * incA D ((β : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hh
      exact hβP P hP (((hes P hP).2 β hβ0).2 hh)
    have h4 : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
    have h5 := mul_mem_idGrp (mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem h3)
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem h4)) hm
    have h6 : finTens α M i j = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (M i j) := by
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    have h7 : incA D ((β : D.host.E)⁻¹) * incA D (m : D.host.E) = incA D (M i j) := by
      rw [← RingHom.map_mul, hme', inv_mul_cancel_left₀ hβ0']
    rw [← RingHom.map_mul, ← RingHom.map_mul, mul_right_comm, mul_assoc (es P), h7, mul_assoc, mul_comm (incA D _), ← h6] at h5
    exact h5
  · rw [Matrix.zero_apply, mul_zero, RingHom.map_zero]; exact zero_mem _
  · intro x y hx hy; rw [Matrix.add_apply, mul_add, RingHom.map_add]; exact add_mem hx hy
  · intro x hx; rw [Matrix.neg_apply, mul_neg, RingHom.map_neg]; exact neg_mem hx

set_option maxHeartbeats 1600000 in

theorem mem_of_inId (hc : D.host.ccK = ⊤) (hS : S.gram = 1) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hLT : ∀ x, x ∈ LT ↔ ∀ i, x i ∈ I)
    {𝔪 : Ideal (𝓞 D.host.E)} (hI : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ I) {u : WO S T}
    (h0 : ∀ i j, infPart D (u i j) = 0) (hu : ∀ i j, toEAf D (u i j) ∈ idGrp 𝔪) :
    u ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have h1 : (1 : D.host.E) ∈ D.host.AA0 := by
    have hb0 := bb_ne_zero D
    refine (show (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ D.host.AA0 from ?_) (FractionalIdeal.one_mem_one _)
    rw [Formalism.BasicNotions.Host.AA0, ← one_div, FractionalIdeal.le_div_iff_mul_le hb0, one_mul]
    exact FractionalIdeal.coeIdeal_le_one
  have key : ∀ i j, ∀ t ∈ idS D.host.F 𝔪, ∃ y : AE D, infPart D y = 0 ∧ toEAf D y = t ∧
      (Matrix.single i j y : WO S T) ∈
        latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    intro i j t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (m : D.host.E), infPart_pair _ _, rfl, ?_⟩
      have h2 : Matrix.single i j (m : D.host.E) ∈
          latRat S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) := by
        refine (mem_latRat_iff hc hS hLT _).2 fun k l => ?_
        rw [Matrix.single_apply]
        split_ifs
        · simpa using FractionalIdeal.mul_mem_mul h1 (hI (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ hm))
        · exact FractionalIdeal.zero_mem _
      convert finTens_mem_latO (one_mem_intAf _) h2 using 1
      refine Matrix.ext fun k l => ?_
      rw [finTens, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
      split_ifs
      · rfl
      · exact (TensorProduct.tmul_zero _ _).symm
    | zero => exact ⟨0, RingHom.map_zero _, RingHom.map_zero _, by rw [Matrix.single_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hb⟩ := hx
      obtain ⟨b, hc, hc', hd⟩ := hy
      exact ⟨a + b, by rw [RingHom.map_add, ha, hc, add_zero], by rw [RingHom.map_add, ha', hc', Subring.coe_add],
        by rw [Matrix.single_add]; exact add_mem hb hd⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha', hb⟩ := hx
      obtain ⟨w, -, hw⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (c : EAf D)
      refine ⟨w * a, by rw [RingHom.map_mul, ha, mul_zero], by rw [RingHom.map_mul, ha', hw, smul_eq_mul, Subring.coe_mul], ?_⟩
      have := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ w
        (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by rw [hw]; exact c.2)) _ hb
      rwa [Matrix.smul_single, smul_eq_mul] at this
  rw [Matrix.matrix_eq_sum_single u]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  obtain ⟨t, ht, hte⟩ := hu i j
  obtain ⟨y, hy, hy', hy''⟩ := key i j t ht
  rwa [toEAf_ext (x := u i j) (y := y) (by rw [h0, hy]) (hte.symm.trans hy'.symm)]

theorem mem_of_char_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u : WO S T} (hu : ∀ i j, infPart D (u i j) = 0)
    (h : ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)),
      ψ (symplO S T u (finTens 1 ℓ)) = 1) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨M, u₀, hu₀, hM⟩ := approx hS hT u
  have e : u = finTens 1 M + u₀ := by
    ext i j
    rw [← sub_eq_zero]
    apply eq_zero_of_parts
    · have h2 : infPart D (finTens 1 M i j) = 0 := infPart_pair _ _
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, hu, h2, infPart_of_mem hu₀, add_zero, sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, hM, sub_eq_zero]
      rfl
  rw [e]
  refine add_mem (finTens_mem_latO (one_mem_intAf _) ?_) hu₀
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have hl := finTens_mem_latO (one_mem_intAf _) hℓ
  have h1 := h _ hℓ
  rw [e, symplO_add_left, ψ.map_add_eq_mul, char_sympl_eq_one hψ hS hT hu₀ hl, mul_one, symplO_finTens,
    one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

end GlobalTheory.IopRead
