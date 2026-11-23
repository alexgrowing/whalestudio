import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HyperbolicZeroEmbeddingId
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwoLtCardResidueField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfinitelyManySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyExtUnramTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTameRamified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Filter
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Inhab

variable {D : D7}

def intGrp (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mem_intGrp {v : Pl D} {a : AE D} : a ∈ intGrp D v ↔ a ∈ intAt D (· = v) := Iff.rfl

theorem int_mul {v : Pl D} {a b : AE D} (ha : a ∈ intGrp D v) (hb : b ∈ intGrp D v) : a * b ∈ intGrp D v :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a := by
  have h := GlobalTheory.LatAlmostStd.tmul_mem_intAt (D := D)
    (GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) fun w => by rw [map_one]; exact one_mem _) 1
  rw [mul_one] at h
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)), GlobalTheory.IdemSupport.cA_algebraMap _, h,
    fun a => ⟨fun ha => ?_, fun ha => ha ▸ Ideal.mul_mem_right _ _ h.1⟩⟩
  rw [← Algebra.smul_def]
  exact GlobalTheory.LatAlmostStd.smul_eq_of_mem_idAt ha

theorem int_cA {v : Pl D} {a : AE D} (ha : a ∈ intGrp D v) : cA D a ∈ intGrp D v := by
  obtain ⟨ε, hc, -, hid⟩ := exists_idem v
  refine ⟨(hid _).2 ?_, GlobalTheory.IdemSupport.finPart_cA_mem ha.2⟩
  conv_lhs => rw [← hc, ← map_mul, (hid a).1 ha.1]

theorem int_cA_iff {v : Pl D} {a : AE D} : cA D a ∈ intGrp D v ↔ a ∈ intGrp D v :=
  ⟨fun h => by simpa only [Formalism.L2.Theta.cA_cA] using int_cA h, int_cA⟩

theorem mulVec_mem {v : Pl D} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {y : Fin n → AE D} {i : Fin m}
    (h : ∀ j, M i j * y j ∈ intGrp D v) : (M *ᵥ y) i ∈ intGrp D v := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => h j

def RatInt (v : Pl D) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Prop :=
  ∀ i j, ∀ a ∈ intGrp D v, incA D (M i j) * a ∈ intGrp D v

theorem ae_ratInt {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : ∀ᶠ v : Pl D in cofinite, RatInt v M :=
  eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (M i j)

theorem RatInt.mulVec {v : Pl D} {m n : ℕ} {M : Matrix (Fin m) (Fin n) D.host.E} (h : RatInt v M) {y : Fin n → AE D}
    (hy : ∀ j, y j ∈ intGrp D v) (i : Fin m) : (rat M *ᵥ y) i ∈ intGrp D v :=
  mulVec_mem fun j => h i j _ (hy j)

theorem ae_family {ι : Type} [Finite ι] {x : ι → D.host.E} (hx : x ≠ 0) :
    ∀ᶠ v : Pl D in cofinite, ∀ a, (∀ k, a * incA D (x k) ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  filter_upwards [eventually_all.2 fun j => GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x j), GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (x k)⁻¹] with v h1 h2 a
  refine ⟨fun h => ?_, fun h j => by rw [mul_comm]; exact h1 j a h⟩
  have := h2 _ (h k)
  rwa [mul_left_comm, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one] at this

def Std (S : HSp D) (L : Lat S) (v : Pl D) : Prop := ∀ y, y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intGrp D v

theorem ae_std {S : HSp D} {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, Std S L v :=
  GlobalTheory.LatAlmostStd.eventually_latV_iff D S L h.1

theorem ae_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) :
    ∀ᶠ v : Pl D in cofinite, ∀ u : WO S T, u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) ↔ ∀ i j, u i j ∈ intGrp D v := by
  filter_upwards [ae_std hS, ae_std hT, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D] with v h1 h2 h3 u
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, h3]
  refine ⟨fun ⟨hm, h⟩ i j => ?_, fun h => ⟨fun i j => (h i j).1, fun y hy => (h2 _).2 fun i =>
    mulVec_mem fun j => int_mul (h i j) ((h1 y).1 hy j)⟩⟩
  have := (h2 _).1 (h (Pi.single j ε) ((h1 _).2 fun k => by
    by_cases hk : k = j
    · subst hk; rw [Pi.single_eq_same]; exact hε
    · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)) i
  rw [mulVec_single] at this
  have e : u i j * ε = u i j := by rw [mul_comm]; exact (hid _).1 (hm i j)
  rw [← e]
  exact this

theorem ae_monoAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} (h : IsSelfDualC S L)
    (h₀ : IsSelfDualC S₀ L₀) : ∀ᶠ v : Pl D in cofinite, MonoAt d L L₀ v := by
  filter_upwards [ae_std h, ae_std h₀, ae_ratInt d.e, ae_ratInt d.e', ae_ratInt d.i₀, ae_ratInt d.qX, ae_ratInt d.qY,
    ae_ratInt d.q0] with v h1 h2 e e' i qX qY q0 y
  simp only [h1 _, h2 _]
  refine ⟨fun hy => ⟨fun j k => ?_, fun j k => ?_, q0.mulVec hy⟩, fun ⟨a, b, c⟩ k => ?_⟩
  · rw [colMul, mul_comm]; exact e k j _ (qX.mulVec hy j)
  · rw [colMul, mul_comm]; exact e' k j _ (qY.mulVec hy j)
  · have : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← add_mulVec, ← add_mulVec]
      exact (one_mulVec y).symm.trans (congrArg (· *ᵥ y) d.sum_eq_one.symm)
    rw [this]
    refine add_mem (add_mem (mulVec_mem fun j => ?_) (i.mulVec c k)) (mulVec_mem fun j => ?_)
    · rw [mul_comm]; exact a j k
    · rw [mul_comm]; exact b j k

theorem ae_orthAt {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B} (h : IsSelfDualC S L)
    (hA : IsSelfDualC A LA) (hB : IsSelfDualC B LB) : ∀ᶠ v : Pl D in cofinite, OrthAt o L LA LB v := by
  filter_upwards [ae_std h, ae_std hA, ae_std hB, ae_ratInt o.iA, ae_ratInt o.iB, ae_ratInt o.qA, ae_ratInt o.qB]
    with v h1 h2 h3 iA iB qA qB y
  simp only [h1 _, h2 _, h3 _]
  refine ⟨fun hy => ⟨qA.mulVec hy, qB.mulVec hy⟩, fun ⟨a, b⟩ k => ?_⟩
  have : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec]
    exact (one_mulVec y).symm.trans (congrArg (· *ᵥ y) o.sum_eq_one.symm)
  rw [this]
  exact add_mem (iA.mulVec a k) (iB.mulVec b k)

def RatCols {m n : ℕ} (x : Mx D m n) : Prop := ∀ i, ∃ c : Fin m → D.host.E, c ≠ 0 ∧ ∀ k, x k i = incA D (c k)

theorem RatCols.ae {m n : ℕ} {x : Mx D m n} (h : RatCols x) :
    ∀ᶠ v : Pl D in cofinite, ∀ i a, (∀ k, colMul x i a k ∈ intGrp D v) ↔ a ∈ intGrp D v := by
  refine eventually_all.2 fun i => ?_
  obtain ⟨c, hc, e⟩ := h i
  simpa only [colMul, e] using ae_family hc

theorem ratCols_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : RatCols d.jX := fun i => by
  refine ⟨fun k => d.e k i, fun h => ?_, fun _ => rfl⟩
  have := congrFun (congrFun d.e'e i) i
  rw [mul_apply, one_apply_eq, Finset.sum_eq_zero fun k _ => by rw [show d.e k i = 0 from congrFun h k, mul_zero]] at this
  exact zero_ne_one this

theorem vecB_ne_zero {S₀ A L : HSp D} (o : OrthDec S₀ A L) {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    vecB o ζ ≠ 0 := fun h0 => by
  have : ζ = 0 := by rw [← one_mulVec ζ, ← o.qB_iB, ← mulVec_mulVec, show o.iB *ᵥ ζ = 0 from h0, mulVec_zero]
  exact h.2 (by rw [this, mulVec_zero, dotProduct_zero])

theorem ratCols_xLast {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) {z : Fin T₀.rank → D.host.E} (hz : z ≠ 0) :
    RatCols (xLast d z) := fun i => by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · refine ⟨d.i₀ *ᵥ z, fun h => hz ?_, fun k => ?_⟩
    · have h1 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
      rw [← one_mulVec z, ← h1, ← mulVec_mulVec, h, mulVec_zero]
    · simp only [xLast, of_apply, Fin.snoc_last]
      exact (RingHom.map_mulVec (incA D) d.i₀ z k).symm
  · obtain ⟨c, hc, e⟩ := ratCols_jX d j
    exact ⟨c, hc, fun k => by simp only [xLast, of_apply, Fin.snoc_castSucc, e]⟩

theorem ae_colsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {x : Mx D W.rank ρ} (hx : RatCols x) {LV : Lat V}
    {LW : Lat W} (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW) : ∀ᶠ v : Pl D in cofinite, ColsAt d x LV LW v := by
  filter_upwards [ae_std hV, ae_std hW, GlobalTheory.FinPl.AlmostAll.latA_eq_latV D, (ratCols_jX d).ae, hx.ae] with v h1 h2 h3 h4 h5 i a _
  rw [h3, h1, h2, h4, h5]

theorem ae_primAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {L : Lat S} (h : IsSelfDualC S L) : ∀ᶠ v : Pl D in cofinite, PrimAt ψ d L v := by
  filter_upwards [ae_std h, (ratCols_jX d).ae, GlobalTheory.FinPl.Conductor.eventually_conductor D ψ hψ] with v h1 h2 h3 i j _ s hs
  obtain ⟨ε, -, hε, hid⟩ := exists_idem v
  simp only [h1 _, h2]
  rw [h3 s hs]
  refine ⟨fun h => ?_, fun h a ha => int_mul h ha⟩
  have := h ε hε
  rwa [mul_comm, (hid s).1 hs] at this

theorem ae_tame (D : D7) : ∀ᶠ v : Pl D in cofinite, Tame D v :=
  (GlobalTheory.FinPl.eventually_extUnram_two_notMem D).mono fun _ h => ⟨h.1, Or.inl h.2⟩

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (a : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (a • y) = cA D a • (show Mx D T.rank S.rank from d.incAdj S y) := by
  show d.jY * (incA D (-D.host.xi0⁻¹) • (adj (a • y) * gA S)) = cA D a • (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
  rw [adj_smul, Matrix.smul_mul, smul_comm, Matrix.mul_smul]

theorem incAdj_yZero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {z : Fin S.rank → D.host.E} (hz : z ≠ 0)
    (hρ : 0 < ρ) : ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, M ≠ 0 ∧ d.incAdj S (yZero S ρ z) = rat M := by
  let y : Matrix (Fin S.rank) (Fin ρ) D.host.E := of fun k i => if i.1 + 1 = ρ then -z k else 0
  have hy : yZero S ρ z = rat y := by
    ext k i
    show -(incA D (z k) * (if i.1 + 1 = ρ then 1 else 0)) = incA D (if i.1 + 1 = ρ then -z k else 0)
    split_ifs
    · rw [mul_one, RingHom.map_neg]
    · rw [mul_zero, neg_zero, RingHom.map_zero]
  refine ⟨d.e' * (-D.host.xi0⁻¹ • (yᴴ * S.gram)), fun h => hz ?_, ?_⟩
  · have h1 : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
    have h2 : -D.host.xi0⁻¹ • (yᴴ * S.gram) = 0 := by
      rw [← Matrix.one_mul (-D.host.xi0⁻¹ • _), ← h1, Matrix.mul_assoc, h, Matrix.mul_zero]
    rw [smul_eq_zero, neg_eq_zero, inv_eq_zero] at h2
    have h3 : yᴴ = 0 := by
      rw [← Matrix.mul_one yᴴ, ← mul_nonsing_inv _ (gram_isUnit_det S), ← Matrix.mul_assoc,
        h2.resolve_left (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), Matrix.zero_mul]
    funext k
    have h4 := congrFun (congrFun (conjTranspose_eq_zero.1 h3) k) ⟨ρ - 1, by omega⟩
    simpa [y, show ρ - 1 + 1 = ρ by omega] using h4
  · rw [hy, rat_mul, rat_smul, rat_mul, rat_conjTranspose]
    rfl

theorem ae_goodBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ)
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} (hV : IsSelfDualC B.V LV)
    (hV₀ : IsSelfDualC B.V₀ LV₀) (hW : IsSelfDualC J.W LW) (hW₀ : IsSelfDualC J.W₀ LW₀) :
    ∀ᶠ v : Pl D in cofinite, GoodBF ψ B J LV LV₀ LW LW₀ v := by
  have hl : ∀ᶠ v : Pl D in cofinite, 0 < ρ → ∀ a ∈ idAt D (· = v),
      J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ)) ∈ latO B.V₀ J.W (LV₀ : Set _) (LW : Set _) (· = v) ↔
        a ∈ intAt D (· = v) := by
    rcases Nat.eq_zero_or_pos ρ with h0 | hρ
    · exact Eventually.of_forall fun v h => absurd h (by omega)
    obtain ⟨M, hM, e⟩ := incAdj_yZero J.d B.V₀ (vecB_ne_zero B.o B.line) hρ
    have hM' : (fun ij : Fin J.W.rank × Fin B.V₀.rank => M ij.1 ij.2) ≠ 0 := fun h =>
      hM (Matrix.ext fun i j => congrFun h (i, j))
    filter_upwards [ae_latO hV₀ hW, ae_family hM'] with v h1 h2 _ a _
    rw [h1, incAdj_smul, e, ← mem_intGrp, ← int_cA_iff, ← h2, Prod.forall]
    rfl
  filter_upwards [ae_tame D, ae_monoAt B.d hV hV₀, ae_monoAt J.d hW hW₀, ae_primAt hψ B.d hV,
    ae_colsAt B.d (ratCols_jX J.d) hV hW, hl] with v a b c d e f
  exact ⟨a, hV, hV₀, hW, hW₀, b, c, d, e, f⟩

theorem ae_adaptFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) {LV : Lat J.W} {LV₀ : Lat J.W₀} {LW : Lat B.V} {LW₀ : Lat B.V₀} (hV : IsSelfDualC J.W LV)
    (hV₀ : IsSelfDualC J.W₀ LV₀) (hW : IsSelfDualC B.V LW) (hW₀ : IsSelfDualC B.V₀ LW₀) :
    ∀ᶠ v : Pl D in cofinite, AdaptFB ψ J B LV LV₀ LW LW₀ v := by
  filter_upwards [ae_tame D, ae_monoAt J.d hV hV₀, ae_monoAt B.d hW hW₀, ae_primAt hψ J.d hV,
    ae_colsAt J.d (ratCols_xLast B.d (vecB_ne_zero B.o B.line)) hV hW] with v a b c d e
  exact ⟨a, hV, hV₀, hW, hW₀, b, c, d, e⟩

theorem ae_splitCore {ρ : ℕ} (B : BesLev D ρ) {L₀ : Lat B.V₀} (h : IsSelfDualC B.V₀ L₀) :
    ∀ᶠ v : Pl D in cofinite, SplitCore B L₀ v :=
  (ae_orthAt B.o h (GlobalTheory.PlaceModel.isSelfDualC_latFrame B.A) (GlobalTheory.PlaceModel.isSelfDualC_latFrame B.L)).mono
    fun _ hv => ⟨_, _, GlobalTheory.PlaceModel.isSelfDualC_latFrame B.A, GlobalTheory.PlaceModel.isSelfDualC_latFrame B.L, hv⟩

section Split

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_splitPt {e : AE D} (he : IsSplitIdem D e) :
    ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)), p.e = e ∧ p.v = v := by
  obtain ⟨v, ε, h1, h2⟩ := he.2.2
  exact ⟨v, GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2⟩

theorem exists_splitPt_of_ae {Q : Pl D → Prop} (h : ∀ᶠ v : Pl D in cofinite, Q v) :
    ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)), p.v = v ∧ Q v := by
  obtain ⟨v, ⟨e, ε, he, h1, h2⟩, hv⟩ := ((GlobalTheory.FinPl.infinite_splitIdem_places D).frequently_cofinite.and_eventually h).exists
  obtain ⟨p, -, hp⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2
  exact ⟨v, p, hp, hv⟩

theorem exists_splitPt_unit (D : D7) : ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)), p.v = v ∧ p.UnitAA ∧
    2 < Nat.card 𝓀[Fv D.host.F v] := by
  obtain ⟨v, p, hp, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := exists_splitPt_of_ae ((((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    (GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹)).and (GlobalTheory.FinPl.AlmostAll.latA_eq_latV D)).and (GlobalTheory.FinPl.eventually_extUnram_two_notMem D))
  refine ⟨v, p, hp, ?_, GlobalTheory.FinPl.two_lt_card_residueField _ v h4.2⟩
  rw [SplitPt.UnitAA, hp]
  exact ⟨fun a ha => ⟨h1 a ha, h2 a ha⟩, h3⟩

end Split

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isChar (p : SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ χ ≠ 1 := by
  let χ : AddChar k Circle :=
    { toFun := fun a => ⟨psiE ψ (p.sec a), mem_sphere_zero_iff_norm.2 (hψ.1.2.1 _)⟩
      map_zero_eq_one' := Circle.ext (by simp [psiE])
      map_add_eq_mul' := fun a b => Circle.ext (by
        show psiE ψ (p.sec (a + b)) = psiE ψ (p.sec a) * psiE ψ (p.sec b)
        simp [psiE, AddChar.map_add_eq_mul]) }
  obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
  exact ⟨χ, fun _ => rfl, fun h => ha (congrArg (fun c : AddChar k Circle => (c a : ℂ)) h)⟩

theorem exists_frame_of_basis (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k) (h : b * b' = 1) (h' : b' * b = 1) :
    ∃ β : Frame p S n, β.b = b :=
  let ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k p S n b b' h h'
  ⟨⟨b, b', h, h', gl, h1, h2⟩, rfl⟩

theorem exists_frame (p : SplitPt D k) (S : HSp D) : ∃ β : Frame p S (Fin S.rank), β.b = 1 ∧ β.b' = 1 := by
  obtain ⟨β, h⟩ := exists_frame_of_basis p S (Fin S.rank) 1 1 (one_mul _) (one_mul _)
  exact ⟨β, h, by rw [← β.bb', h, Matrix.one_mul]⟩

variable {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

theorem exists_sumFrame {S₀ A L : HSp D} (o : OrthDec S₀ A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    (β : Frame p A n) : ∃ β₀ : Frame p S₀ (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let φ : D.host.E →+* k := p.pr.comp (incA D)
  have hz : ζ ≠ 0 := fun h => hζ.2 (by rw [h, mulVec_zero, dotProduct_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have hs : ∀ j : Fin L.rank, j = i := fun j => Fin.ext (by have := j.2; have := i.2; have := hζ.1; omega)
  let Z : Matrix (Fin L.rank) (Fin 1) D.host.E := replicateCol (Fin 1) ζ
  let Z' : Matrix (Fin 1) (Fin L.rank) D.host.E := of fun _ _ => (ζ i)⁻¹
  have h1 : Z' * Z = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [mul_apply, Finset.sum_eq_single i (fun j _ h => absurd (hs j) h) (by simp), Subsingleton.elim a b, one_apply_eq]
    exact inv_mul_cancel₀ (a := ζ i) hi
  have h2 : Z * Z' = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [mul_apply, Fin.sum_univ_one, hs a, hs b, one_apply_eq]
    exact mul_inv_cancel₀ (a := ζ i) hi
  have e : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) = (o.iB * Z).map φ := by
    ext a b
    simp only [replicateCol_apply, map_apply, mul_apply, Z, ratV, vecB, mulVec, dotProduct, φ, RingHom.comp_apply]
  have eA : o.jA.map p.pr = o.iA.map φ := rfl
  obtain ⟨β₀, h⟩ := exists_frame_of_basis p S₀ (n ⊕ Fin 1) (fromCols (o.iA.map φ * β.b) ((o.iB * Z).map φ))
    (fromRows (β.b' * o.qA.map φ) ((Z' * o.qB).map φ)) (by
      rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, ← Matrix.map_mul,
        ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Z, h2, Matrix.one_mul, ← Matrix.map_add _ φ.map_add,
        o.iA_qA_add, Matrix.map_one _ φ.map_zero φ.map_one]) (by
      rw [fromRows_mul_fromCols, ← fromBlocks_one]
      congr 1
      · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map φ), ← Matrix.map_mul, o.qA_iA,
          Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul, β.b'b]
      · rw [Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc o.qA, o.qA_iB, Matrix.zero_mul,
          Matrix.map_zero _ φ.map_zero, Matrix.mul_zero]
      · rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc Z', o.qB_iA, Matrix.mul_zero,
          Matrix.map_zero _ φ.map_zero, Matrix.zero_mul]
      · rw [← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc o.qB, o.qB_iB, Matrix.one_mul, h1,
          Matrix.map_one _ φ.map_zero φ.map_one])
  exact ⟨β₀, by rw [IsSumFrame, h, e, eA]⟩

theorem exists_selfDual_isLat {S : HSp D} (β : Frame p S n) (Λ : Submodule 𝒪[k] (n → k)) (hΛ : Λ.IsLattice k) :
    ∃ L : Lat S, IsSelfDualC S L ∧ β.IsLat L Λ :=
  let ⟨L, h1, h2, _⟩ := GlobalTheory.FrameGlob.main D k p S n β _ Λ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) hΛ
  ⟨L, h1, h2⟩

theorem exists_gluedCore_at (hp : p.UnitAA) (q : Unif k) {V : HSp D} {ρ : ℕ} (d : HypDec V (Unf.Inhab.plane D) ρ)
    (β : Frame p (Unf.Inhab.posLine D) n) (P : Pair k n) :
    ∃ (c : D.host.E) (hc : c ≠ 0) (β₀ : Frame p (Unf.Inhab.plane D) (n ⊕ Fin 1)) (L₀ : Lat (Unf.Inhab.plane D)),
      IsSelfDualC (Unf.Inhab.plane D) L₀ ∧ GluedCore (Unf.Inhab.besPlane d hc) L₀ q β β₀ P := by
  obtain ⟨c, h1, h2⟩ := GlobalTheory.FinPl.SplitApprox.exists_unif_unit D k p q
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨β₀, hβ⟩ := exists_sumFrame (orthDecPlane D) (Unf.Inhab.isLineVec_negLine hc) β
  obtain ⟨L₀, a, b⟩ := exists_selfDual_isLat β₀ (gluedS q 1 P.ker P.vec) (gluedLat_one q 1 P.ker P.vec ▸ inferInstance)
  refine ⟨c, hc, β₀, L₀, a, hp, hβ, ?_, b⟩
  have : star (fun _ => c) ⬝ᵥ (Unf.Inhab.negLine D).gram *ᵥ (fun _ => c) = -(star c * c) := by
    rw [diagSp_gram]
    change ∑ i : Fin 1, star c * ∑ j : Fin 1, Matrix.diagonal (fun i => Examples₂.sgn (![true] i)) i j * c = _
    simp [Examples₂.sgn]
  show valuation k (p.pr (incA D (star (fun _ => c) ⬝ᵥ (Unf.Inhab.negLine D).gram *ᵥ (fun _ => c)))) = _
  rw [this, RingHom.map_neg, RingHom.map_neg, Valuation.map_neg, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
    h1, h2, one_mul]

theorem exists_over {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {n' : Type} [Fintype n']
    [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) :
    ∃ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ),
      f₀ ≠ 0 ∧ f ≠ 0 ∧ Over ψ α β LS LT f₀ Ψ f := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _ hS hT
  obtain ⟨h1, h2, -⟩ := hf 1
  simp only [one_mul] at h1 h2
  have hv : Vac ψ S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) (· = p.v) f :=
    ⟨h1, fun u hu => h2.1 u (GlobalTheory.PlaceModel.latO_le_top _ hu),
      fun e he u hu => h2.2 e he u (GlobalTheory.PlaceModel.latO_le_top _ hu)⟩
  obtain ⟨Ψ, hΨ, e⟩ := GlobalTheory.FinPl.HalfInd.exists_SB_extFun_eq_halfInd D k p S T n n' α β _ _ hS hT
  obtain ⟨ε, a, b⟩ := p.above
  have hm := GlobalTheory.PlaceModel.placeModelExistsO D ψ hψ S T p.e p.v ε p.split a b 1 f one_ne_zero h1
  rw [← GlobalTheory.PlaceModel.coe_latFrame, ← GlobalTheory.PlaceModel.coe_latFrame] at hm
  refine ⟨_, _, f, Ψ, f, f0, f0, hS, hT, hv, hΨ, hm hv.2, fun Tm hT => ?_⟩
  rw [e, ← hT.vac, one_smul]

end Frames

section Ram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_smul_eq (g : GL (Fin 1) k) (x : Fin 1 → k) : g • x = g.val 0 0 • x := by
  funext i
  rw [Subsingleton.elim i 0]
  show (g.val *ᵥ x) 0 = _
  simp [mulVec, dotProduct]

theorem valuation_of_stab {g : GL (Fin 1) k} (h : g • stdPair k (0 : Fin 1) = stdPair k 0) :
    valuation k (g.val 0 0 - 1) < 1 := by
  have h1 : (stdPair k (0 : Fin 1)).HasVal (fun _ => 1) 1 := stdPair_hasVal.2 ⟨fun _ => one_mem _, map_one _⟩
  have h2 := h1.gl_smul g
  rw [h, gl_smul_eq, stdPair_hasVal] at h2
  obtain ⟨a, b⟩ := h2
  have h3 : residue 𝒪[k] (⟨_, a 0⟩ - 1) = 0 := by rw [map_sub, b, map_one, sub_self]
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one] at h3
  have h4 := (Valuation.integer.integers (valuation k)).map_le_one (⟨_, a 0⟩ - 1)
  have h5 := lt_of_le_of_ne h4 h3
  simp only [map_sub, map_one, Pi.smul_apply, smul_eq_mul, mul_one] at h5
  exact h5

theorem exists_dia_eq {u : GL (Fin 1) k} (hu : valuation k (u.val 0 0) = 1) (P : Pair k (Fin 1)) :
    ∃ c : 𝓀[k]ˣ, c • P = u • P := by
  have h1 : (u⁻¹).val 0 0 * u.val 0 0 = 1 := by
    have := congrFun (congrFun u.inv_mul 0) 0
    simpa [mul_apply] using this
  have hu' : valuation k ((u⁻¹).val 0 0) = 1 := by
    have := congrArg (valuation k) h1
    rwa [map_mul, hu, mul_one, map_one] at this
  let s : 𝒪[k] := ⟨_, hu.le⟩
  let t : 𝒪[k] := ⟨_, hu'.le⟩
  have hts : t * s = 1 := Subtype.ext h1
  have hr : residue 𝒪[k] t * residue 𝒪[k] s = 1 := by rw [← map_mul, hts, map_one]
  refine ⟨⟨_, _, hr, by rw [mul_comm, hr]⟩, Pair.ext fun x a => ?_⟩
  rw [Pair.dia_hasVal, Pair.smul_hasVal, gl_smul_eq]
  show P.HasVal x (residue 𝒪[k] s * a) ↔ P.HasVal (t • x) a
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.smul t
    rwa [← mul_assoc, hr, one_mul] at this
  · have := h.smul s
    rwa [smul_smul, mul_comm s, hts, one_smul] at this

theorem exists_isRam {p : SplitPt D k} {S : HSp D} (hS : S.rank = 1) (β : Frame p S (Fin 1)) (hk : 2 < Nat.card 𝓀[k]) :
    ∃ (φ : Form k (Fin 1) (GA D S → ℂ)) (P : Pair k (Fin 1)), IsRam β φ ∧ φ P ≠ 0 := by
  obtain ⟨f, hf, h1, u, hu, hne⟩ := GlobalTheory.RamLine.exists_tame_ramified D k p S hS β hk
  let P₀ := stdPair k (0 : Fin 1)
  choose γ hγ using fun Q => MulAction.exists_smul_eq (GL (Fin 1) k) P₀ Q
  let φ₀ : Form k (Fin 1) (GA D S → ℂ) := fun Q => β.rep (γ Q) f
  have key : ∀ g : GL (Fin 1) k, φ₀ (g • P₀) = β.rep g f := fun g => by
    have h2 := h1 (g⁻¹ * γ (g • P₀)) (valuation_of_stab (by rw [mul_smul, hγ, inv_smul_smul]))
    conv_rhs => rw [← h2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have eqv : ∀ (g : GL (Fin 1) k) Q, φ₀ (g • Q) = β.rep g (φ₀ Q) := fun g Q => by
    conv_lhs => rw [← hγ Q, ← mul_smul, key, map_mul]
    rfl
  have cont : ∀ Q, IsContAut S (φ₀ Q) := fun Q =>
    ⟨fun a ha g => by
      show f (a * g * _) = f (g * _)
      rw [mul_assoc, hf.1 a ha], hf.2.comp (continuous_mul_right _)⟩
  obtain ⟨c, hc⟩ := exists_dia_eq hu P₀
  refine ⟨fun Q => φ₀ (c • Q) - φ₀ Q, P₀, ⟨fun g Q => ?_, ?_, fun Q => ⟨fun a ha g => ?_, (cont _).2.sub (cont _).2⟩⟩, ?_⟩
  · simp only [map_sub, ← eqv, smul_comm g c]
  · classical
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine LinearMap.mem_ker.2 (funext fun Q => ?_)
    rw [Nm_apply, Finset.sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun a => by rw [Equiv.coe_mulLeft, mul_smul]
  · simp only [Pi.sub_apply, (cont _).1 a ha]
  · have h0 : φ₀ P₀ = f := by simpa using key 1
    show φ₀ (c • P₀) - φ₀ P₀ ≠ 0
    rwa [hc, key, h0, sub_ne_zero]

end Ram

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  rw [heisO, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem symplO_zero (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  rw [symplO_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, trace_zero, mul_zero, map_zero]

theorem p_zero_hyperbolic_zero_eq_one (V : HSp D) : (hypZero V).p0 = 1 := by
  have h := (hypZero V).p0_j0
  rwa [GlobalTheory.HypZeroTriv.hyperbolic_zero_j0_one, Matrix.mul_one] at h

theorem heisLaws_id (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (x : Mx D W.rank 0) (y : Mx D V.rank 0)
    (P : Pl D → Prop) : HeisLaws ψ (hypZero V) (hypZero W) x y P id where
  theta _ h := h
  dual f _ a _ _ := by
    rw [Subsingleton.elim a 0, map_zero, heisO_zero, symplO_zero, AddChar.map_zero_eq_one, one_smul]
  iso f _ a _ := by
    rw [Subsingleton.elim a 0, map_zero, map_zero, heisO_zero, symplO_zero, AddChar.map_zero_eq_one, one_smul]
  core f _ w _ := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, p_zero_hyperbolic_zero_eq_one, GlobalTheory.HypZeroTriv.hyperbolic_zero_j0_one, Matrix.mul_one, Matrix.one_mul]
    rfl

theorem opA_zero (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} (d : HypDec W W₀ 0) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) (n : GA D W) (h : GA D W₀) (Ξ : WO V₀ W₀ → ℂ) :
    opA ψ d o ζ om n h Ξ = om (1, h) Ξ := by
  rw [opA, jacT, Subsingleton.elim (yZero _ _ _) 0, cenT, ptT, map_zero, symplOH_zero_left]
  erw [Matrix.mul_zero, Matrix.mul_zero]
  rw [heisO_zero, AddChar.map_zero_eq_one, one_smul]

theorem exists_isFlatBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)),
      0 < B.A.rank ∧ 0 < J.W₀.rank ∧ (∀ P, IsFlatBF s P 𝔉) ∧ ∃ f, IsThetaFunO ψ B.V J.W f ∧ 𝔉 f ≠ 0 := by
  let B : BesLev D 0 := Unf.Inhab.besPlane (hypZero (Unf.Inhab.plane D)) one_ne_zero
  let J : JacLev D 0 := Unf.Inhab.jacLine (hypZero (Unf.Inhab.posLine D))
  obtain ⟨s⟩ := Unf.Inhab.nonempty_stepBF hψ B J
  refine ⟨B, J, { s with om₀ := s.om, weil₀ := s.weil }, id, Nat.one_pos, Nat.one_pos,
    fun P => ⟨heisLaws_id ψ _ _ _ _ P, fun f _ n hn _ h _ => ?_⟩, GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ _ _⟩
  obtain rfl := GlobalTheory.HypZeroTriv.mem_flagN_hypZero _ hn
  have e1 : J.d.emb0 h = h := GlobalTheory.HypZeroTriv.hyperbolic_zero_embedding_id _ h
  have e2 : psiFlag ψ J.d 1 = 1 := by simp [psiFlag, upSum, psiE]
  rw [e1, e2, star_one, one_smul]
  exact (congrArg (fun g => s.om (1, g) f) (one_mul h)).trans (opA_zero ψ J.d B.o B.ζ s.om 1 h f).symm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_good {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) :
    ∃ (L₀ : Lat B.V) (M₀ : Lat B.V₀) (L₁ : Lat J.W) (M₁ : Lat J.W₀) (L₂ : Lat B'.V) (M₂ : Lat B'.V₀) (v : Pl D),
      GoodBF ψ B J L₀ M₀ L₁ M₁ v ∧ AdaptFB ψ J B' L₁ M₁ L₂ M₂ v ∧ SplitCore B M₀ v ∧ SplitCore B' M₂ v := by
  have h := fun S : HSp D => GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  obtain ⟨v, -, -, hv⟩ := exists_splitPt_of_ae ((ae_goodBF hψ B J (h _) (h _) (h _) (h _)).and
    ((ae_adaptFB hψ J B' (h _) (h _) (h _) (h _)).and ((ae_splitCore B (h _)).and (ae_splitCore B' (h _)))))
  exact ⟨_, _, _, _, _, _, v, hv⟩

theorem inhabitants (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) :
    (∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)) (χ : AddChar (Fv D.host.F v) Circle) (B : BesLev D 1)
      (q : Unif (Fv D.host.F v)) (β : Frame p B.A (Fin 1)) (β₀ : Frame p B.V₀ (Fin 1 ⊕ Fin 1)) (L₀ : Lat B.V₀)
      (φ : Form (Fv D.host.F v) (Fin 1) (GA D B.A → ℂ)) (P : Pair (Fv D.host.F v) (Fin 1)),
      p.v = v ∧ 2 < Nat.card 𝓀[Fv D.host.F v] ∧ p.IsChar ψ χ ∧ χ ≠ 1 ∧ 0 < B.A.rank ∧ IsSelfDualC B.V₀ L₀ ∧
      GluedCore B L₀ q β β₀ P ∧ IsRam β φ ∧ φ P ≠ 0 ∧
      ∃ (LS : Lat B.V₀) (LT : Lat B.A) (f₀ : WO B.V₀ B.A → ℂ) (Ψ : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) (Fv D.host.F v) → ℂ)
        (f : WO B.V₀ B.A → ℂ), f₀ ≠ 0 ∧ f ≠ 0 ∧ Over ψ β₀ β LS LT f₀ Ψ f) ∧
    (∃ (B : BesLev D 1) (J : JacLev D 1) (B' : BesLev D 0) (L₀ : Lat B.V) (M₀ : Lat B.V₀) (L₁ : Lat J.W) (M₁ : Lat J.W₀)
      (L₂ : Lat B'.V) (M₂ : Lat B'.V₀) (v : Pl D), 0 < B.A.rank ∧ 0 < J.W₀.rank ∧ 0 < B'.A.rank ∧
      GoodBF ψ B J L₀ M₀ L₁ M₁ v ∧ AdaptFB ψ J B' L₁ M₁ L₂ M₂ v ∧ SplitCore B M₀ v ∧ SplitCore B' M₂ v) ∧
    ∃ (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)),
      0 < B.A.rank ∧ 0 < J.W₀.rank ∧ (∀ P, IsFlatBF s P 𝔉) ∧ ∃ f, IsThetaFunO ψ B.V J.W f ∧ 𝔉 f ≠ 0 := by
  refine ⟨?_, ?_, exists_isFlatBF hψ⟩
  · obtain ⟨v, p, hv, hp, hk⟩ := exists_splitPt_unit D
    obtain ⟨χ, h1, h2⟩ := exists_isChar p hψ
    obtain ⟨q⟩ : Nonempty (Unif (Fv D.host.F v)) := inferInstance
    obtain ⟨β, -⟩ := exists_frame_of_basis p (Unf.Inhab.posLine D) (Fin 1) (1 : Matrix (Fin 1) (Fin 1) _)
      (1 : Matrix (Fin 1) (Fin 1) _) (one_mul _) (one_mul _)
    obtain ⟨φ, P, h3, h4⟩ := exists_isRam rfl β hk
    obtain ⟨c, hc, β₀, L₀, h5, h6⟩ := exists_gluedCore_at hp q (GlobalTheory.RegSW.Model.hypFour D) β P
    exact ⟨v, p, χ, Unf.Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) hc, q, β, β₀, L₀, φ, P, hv, hk, h1, h2, Nat.one_pos, h5,
      h6, h3, h4, exists_over hψ β₀ β⟩
  · let B : BesLev D 1 := Unf.Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) (Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
    let J : JacLev D 1 := Unf.Inhab.jacLine (hypDecThree D)
    let B' : BesLev D 0 := Unf.Inhab.besPlane (Unf.Inhab.hypRefl (Unf.Inhab.plane D)) one_ne_zero
    obtain ⟨L₀, M₀, L₁, M₁, L₂, M₂, v, h⟩ := exists_good (σ := 0) hψ B J B'
    exact ⟨B, J, B', L₀, M₀, L₁, M₁, L₂, M₂, v, Nat.one_pos, Nat.one_pos, Nat.one_pos, h⟩

end GlobalTheory.FinPl.Inhab

end
