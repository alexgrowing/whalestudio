import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulConjSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMovesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedFiniteUnitaryLeOneOffOpenSubsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongrStatement

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open Formalism.MainNotions.TaylorLogMetric (VC tor0 Th La Iop YYl U al)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt Wd wdPh La0)
open GlobalTheory.SplitScalar

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

section Read

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
  {δ : ℂ} {r : D.host.E}

theorem symplOH_self (x : WO S T) : symplOH S T x x = 0 := by
  have h := symplOH_add_self S T x x
  have h2 := symplOH_skew S T x x
  have h3 : symplO S T x x = 0 := by rw [← h]; nth_rewrite 1 [h2]; exact neg_add_cancel _
  rw [symplOH, h3, mul_zero]

theorem finPt_neg (z : Matrix (Fin d) (Fin a) D.host.E) : finPt hS hT r (-z) = -finPt hS hT r z := by
  unfold finPt
  rw [← map_neg]
  congr 1
  ext i j
  simp

theorem u_neg_u (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : VC D a d) (G : VC D a d → ℂ) : U D T (-x) (U D T x G) = G := by
  funext z
  have h1 : ∀ y, Formalism.MainNotions.TaylorLogMetric.Hf D T y (-x) = -Formalism.MainNotions.TaylorLogMetric.Hf D T y x := fun y => by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, neg_div]
  have h2 : Formalism.MainNotions.TaylorLogMetric.Hf D T (z + -x) x = Formalism.MainNotions.TaylorLogMetric.Hf D T z x - Formalism.MainNotions.TaylorLogMetric.Hf D T x x := by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, sub_eq_add_neg, add_div, neg_div]
  have h3 : Formalism.MainNotions.TaylorLogMetric.Hf D T (-x) x = -Formalism.MainNotions.TaylorLogMetric.Hf D T x x := by
    simp [Formalism.MainNotions.TaylorLogMetric.Hf, neg_div]
  simp only [U, h1, h2, h3, neg_add_cancel_right]
  rw [mul_assoc, ← Complex.exp_add]
  convert mul_one _
  rw [← Complex.exp_zero]
  congr 1
  ring

theorem exists_read_of_wd (h : Setup ψ θ S T ⊤ δ r) {G : VC D a d → ℂ} {φ : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (z : Matrix (Fin d) (Fin a) D.host.E)
    (hφ : Reads ψ θ hS hT ⊤ δ r (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G) φ) :
    ∃ (c' : ℂ) (φ₁ : WO S T → ℂ), Reads ψ θ hS hT ⊤ δ r G φ₁ ∧ φ = c' • heisO ψ S T (finPt hS hT r z) φ₁ := by
  set x := pt D (tor0 D ⊤ δ) δ z with hx
  have hw : wdPh D (tor0 D ⊤ δ) x ≠ 0 := by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.exp_ne_zero]
  have hc' : c * wdPh D (tor0 D ⊤ δ) x ≠ 0 := mul_ne_zero hc hw
  have e : (c * wdPh D (tor0 D ⊤ δ) x)⁻¹ • c • Wd D (tor0 D ⊤ δ) x G = U D (tor0 D ⊤ δ) x G := by
    funext y
    simp only [Wd, Pi.smul_apply, smul_eq_mul]
    field_simp
  have h1 := hφ.smul (c * wdPh D (tor0 D ⊤ δ) x)⁻¹
  rw [e] at h1
  have h2 := GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT ⊤ δ r h _ _ h1 (-z)
  have e2 : pt D (tor0 D ⊤ δ) δ (-z) = -x := by
    funext τ i j
    simp [hx, pt, Formalism.MainNotions.TaylorLogMetric.embV, tor0]
  rw [e2, u_neg_u] at h2
  refine ⟨c * wdPh D (tor0 D ⊤ δ) x, _, h2, ?_⟩
  rw [heisO_heisO, finPt_neg, add_neg_cancel, heisO_zero, ← neg_neg (symplOH _ _ _ _), ← symplOH_skew]
  have : symplOH S T (-finPt hS hT r z) (finPt hS hT r z) = 0 := by
    have h3 := symplOH_add_left S T (-finPt hS hT r z) (finPt hS hT r z) (finPt hS hT r z)
    rw [neg_add_cancel, symplOH_self, add_zero, symplOH, symplO_zero_left, mul_zero] at h3
    exact h3.symm
  rw [this, neg_zero, AddChar.map_zero_eq_one, one_smul, smul_smul, mul_inv_cancel₀ hc', one_smul]

theorem heis_two_finPt (h : Setup ψ θ S T ⊤ δ r) {L L'} {G : VC D a d → ℂ} (hG : G ∈ Th D (tor0 D ⊤ δ) L L')
    {f : WO S T → ℂ} (hf : Reads ψ θ hS hT ⊤ δ r G f) {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ YYl D L L') :
    heisO ψ S T (2 • finPt hS hT r z) f = f := by
  set x := pt D (tor0 D ⊤ δ) δ z with hx
  have hxm : x ∈ La D (tor0 D ⊤ δ) L L' :=
    AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩
  have h1 := (GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT ⊤ δ r h _ _ hf z).smul (al D (tor0 D ⊤ δ) x)
  have e : al D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G = G := funext fun y => hG.2 x hxm y
  rw [e] at h1
  have h2 := h1.unique hf
  have hal : al D (tor0 D ⊤ δ) x * al D (tor0 D ⊤ δ) x = 1 := by
    rw [al, ← mul_zpow]; simp
  have h3 : heisO ψ S T (finPt hS hT r z) f = al D (tor0 D ⊤ δ) x • f := by
    conv_rhs => rw [← h2]
    rw [smul_smul, hal, one_smul]
  have h4 := heisO_heisO ψ S T (finPt hS hT r z) (finPt hS hT r z) f
  rw [symplOH_self, AddChar.map_zero_eq_one, one_smul, ← two_nsmul, h3, heisO_smul, h3, smul_smul, hal, one_smul] at h4
  exact h4.symm

end Read

theorem heis_two_hatPt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {r : D.host.E}
    {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hr : r ≠ 0) (hI : I ≠ 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) →
      heisO ψ S T (2 • finPt (S := S) (T := T) rfl rfl r z) f = f) {u : WO S T} (hu : HatPt r I u) :
    heisO ψ S T (2 • u) f = f := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨z, hz, hk⟩ := GlobalTheory.T.dense_rationalHomPoints_idealCompletion S T r I hr hI U hU u hu
  set x := finPt (S := S) (T := T) rfl rfl r z with hx
  have hxi : x.map (infPart D) = 0 := GlobalTheory.VacUnique.finRat_inf S T _
  have hki : (u - x).map (infPart D) = 0 := by
    funext i j
    have a1 : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    have a2 : infPart D (x i j) = 0 := congrFun (congrFun hxi i) j
    change infPart D (u i j - x i j) = 0
    rw [RingHom.map_sub, a1, a2, sub_self]
  have h1 := hUf _ hk hki
  have h2 : heisO ψ S T (2 • x) f = f := h z hz
  obtain ⟨k, rfl⟩ : ∃ k, u = x + k := ⟨u - x, (add_sub_cancel x u).symm⟩
  rw [add_sub_cancel_left] at h1
  have h3 := heisO_comm ψ S T (2 • x) k f
  rw [h1, h2, h1] at h3
  have h4 := heisO_heisO ψ S T k k f
  rw [h1, h1, symplOH_self, AddChar.map_zero_eq_one, one_smul] at h4
  have h5 := heisO_heisO ψ S T (2 • x) (k + k) f
  rw [← h4, h2, symplOH_add_right, symplOH_add_self, ← two_nsmul k, ← nsmul_add] at h5
  have h0 : ψ (symplO S T (2 • x) k) ≠ 0 := left_ne_zero_of_mul_eq_one (b := ψ (-symplO S T (2 • x) k))
    (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])
  exact smul_right_injective _ h0 (h5.symm.trans h3)

theorem mem_YYl_skew {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : ∀ i j, z i j ∈ skewId D 𝔪) : z ∈ YYl D (stdL D a) (skewLat D 𝔪 d) := by
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, z i j * x j ∈ (skewId D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx j trivial)
      rw [← hb, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ b (hz i j)
    exact this

theorem count_coe_eq_zero_iff {E : Type} [Field E] [NumberField E] {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ≠ ⊥) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (𝔞 : FractionalIdeal (𝓞 E)⁰ E) = 0 ↔ ¬ 𝔞 ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w h, Nat.cast_eq_zero, ← Ideal.dvd_iff_le,
    ← Associates.count_ne_zero_iff_dvd h w.irreducible, not_not]

theorem place_facts {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : D.host.conj • 𝔪 ≤ w.asIdeal) (k : ℕ) :
    FractionalIdeal.count D.host.E w (skewId D 𝔪) = -FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ∧
    1 ≤ FractionalIdeal.count D.host.E w ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ∧
    w.valuation D.host.E (2 * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E)) = 1 := by
  have hc := GlobalTheory.FunObj.CosetTheta.conj_ne_bot hG.1
  have h0 : ¬ 𝔪 ≤ w.asIdeal := fun h => w.isPrime.ne_top (top_le_iff.1 (hG.2.1 ▸ sup_le h hw))
  refine ⟨?_, ?_, ?_⟩
  · rw [skewId, div_eq_mul_inv, FractionalIdeal.count_mul D.host.E w (FractionalIdeal.coeIdeal_ne_zero.2 hG.1)
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)), FractionalIdeal.count_inv,
      (count_coe_eq_zero_iff hG.1 w).2 h0, zero_add]
  · have h1 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    have h2 := (count_coe_eq_zero_iff hc w).not.2 (not_not.2 hw)
    omega
  · have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
      intro hq
      obtain ⟨x, hx, y, hy, e⟩ := Ideal.isCoprime_iff_exists.1 hG.2.2.1
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have e2 := congrArg (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) e
      rw [map_add, map_mul, map_natCast, map_one] at e2
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← e2]
      exact add_mem (hw (Ideal.smul_mem_pointwise_smul _ _ _ hx)) (Ideal.mul_mem_left _ _ hq)
    have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hq (by
      obtain ⟨c, hc2⟩ := D.host.two_dvd_QS
      rw [hc2, mul_assoc, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have val : ∀ n : ℕ, (n : 𝓞 D.host.E) ∉ w.asIdeal → w.valuation D.host.E (n : D.host.E) = 1 := fun n hn => by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E), not_lt] at hn
      have := le_antisymm (w.valuation_le_one (K := D.host.E) (n : 𝓞 D.host.E)) hn
      simpa using this
    have v2 := val 2 h2
    rw [Nat.cast_ofNat] at v2
    rw [map_mul, map_mul, v2, Nat.cast_pow, map_pow, val _ hq, one_pow, one_mul, one_mul]

theorem stdLat_selfDual {V : HSp D} (hG : V.gram = 1) : IsSelfDualC V (stdLat V) := by
  have e : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
    ext x
    rw [GlobalTheory.SW.Base.mem_stdL]
    simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rw [e]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG

theorem mem_of_char_eq {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {r : D.host.E} (hψ : IsStdChar D ψ (-1))
    (gS : S.gram = 1) (gT : T.gram = 1) (hr : r ≠ 0) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf)
    {LB : Lat T} (hLB : IsSelfDualC T LB)
    (hY : ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) → z ∈ YYl D (stdL D S.rank) (stdL D T.rank))
    {o : ℕ} (ho : o + S.rank ≤ T.rank) {g : GA D S} {y : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank} (hg : GlobalTheory.BotFormula.IsFinPt S g y)
    (hg' : GlobalTheory.BotFormula.IsFinPt S g⁻¹ y⁻¹) (hy : g ∈ openOff S (stdLat S) Sf)
    (h : ∀ u : WO S T, HatPt r (skewId D 𝔪) u → HatPt r (skewId D 𝔪) (actO S T g 1 u) →
      ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
        ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) :
    y ∈ intG D S.rank ∧ CongOne D 𝔪 y := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_integral_completedHomLattice S T r LB hr hY
  have hH : ∀ i j, fe D (mt S g⁻¹ i j) = finMat y⁻¹ i j := fun i j => by
    obtain ⟨e, he⟩ := hg'.2
    exact he i j
  have hH1 : ∀ i j, fe D ((1 - mt S g⁻¹) i j) = (1 - finMat y⁻¹) i j := fun i j => by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, hH, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [RingHom.map_one]
    · rw [RingHom.map_zero]
  have key : ∀ (s : FA D) (i j : Fin S.rank), InHat (skewId D 𝔪) s → (∀ l, InHat (skewId D 𝔪) (s * finMat y⁻¹ i l)) →
      InHat 1 (algebraMap D.host.E (FA D)
        (2 * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * (((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E)) * (s * (1 - finMat y⁻¹) i j)) := by
    intro s i j hs hs'
    obtain ⟨σ, hσ, eσ⟩ := exists_fe (algebraMap D.host.E (FA D) r⁻¹ * s)
    have e1 : algebraMap D.host.E (FA D) r * fe D σ = s := by
      rw [eσ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]
    have h1 := GlobalTheory.T.integral_of_completedLattice_selfDual_rankOne ψ S T r LB _ hψ gS gT (stdLat_selfDual gS) hLB hr hk ⟨o + j, by omega⟩ j
      (2 * σ * (1 - mt S g⁻¹) i j) (by rw [RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, zero_mul]) fun t ht ht' => by
        have e2 : algebraMap D.host.E (FA D) r * fe D (t * σ) = fe D t * s := by
          rw [RingHom.map_mul, mul_left_comm, e1]
        have h2 := GlobalTheory.T.addChar_trace_unitBlock_trivial_of_moves ψ S T r (skewId D 𝔪) o g gS gT ho h (t * σ) i j
          (by rw [RingHom.map_mul, ht, zero_mul]) (by rw [e2]; exact ht'.mul_left hs)
          fun l => by rw [e2, hH, mul_assoc]; exact ht'.mul_left (hs' l)
        rw [← h2]
        congr 4
        ring
    convert h1 using 1
    rw [(fe D).map_mul, (fe D).map_mul, hH1, ← e1, ← one_add_one_eq_two (R := AE D), (fe D).map_add, (fe D).map_one,
      ← one_add_one_eq_two (R := D.host.E)]
    simp only [RingHom.map_mul, RingHom.map_add, RingHom.map_one]
    ring
  have hc := GlobalTheory.T.unitaryFinitePoint_congr_one_of_inv_conj_congr (GlobalTheory.T.conjugatePlace_valuation_count_under D) 𝔪 Sf hG y (GlobalTheory.T.valued_finiteUnitary_le_one_off_openSubset S g y Sf gS hg hy) fun w hw => by
    obtain ⟨h1, h2, h3⟩ := place_facts hG hw k
    exact GlobalTheory.T.valued_one_sub_le_of_moves_idealCompletion (skewId D 𝔪) w _ _ (finMat y⁻¹) h3 h1 h2 key
  refine ⟨(GlobalTheory.NormSum.mem_intG y).2 fun i j => ⟨?_, ?_⟩, fun i j => GlobalTheory.T.mem_idealIntegralFiniteAdeles_of_memCompletion 𝔪 hG.1 _ ?_⟩
  · exact (GlobalTheory.ZeroAtPlaces.mem_OhE_iff _).2 fun w =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((inHat_one_iff _).1 (hc i j).1 w)
  · exact (GlobalTheory.ZeroAtPlaces.mem_OhE_iff _).2 fun w =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((inHat_one_iff _).1 (hc i j).2.1 w)
  · convert (hc i j).2.2 using 1
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [map_one]; rfl
    · rw [map_zero]; rfl

theorem actO_two {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (2 • u) = 2 • actO S T g h u := by
  simp only [actO, two_nsmul, Matrix.mul_add, Matrix.add_mul]

theorem ip_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    {δ : ℂ} {r : D.host.E} (h : Setup ψ θ S T ⊤ δ r) {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {e0 : VC D a d → ℂ} (he0 : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d))
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} (hG : GoodMod D 𝔪 Sf) {LB : Lat T} (hLB : IsSelfDualC T LB)
    (hY : ∀ z : Matrix (Fin d) (Fin a) D.host.E,
      finPt hS hT r z ∈ (latO S T (stdLat S) LB fun _ => True) → z ∈ YYl D (stdL D a) (stdL D d))
    {o : ℕ} (ho : o + a ≤ d) {c : ℂ} (hc : c ≠ 0) {φ : WO S T → ℂ}
    (hφ : Reads ψ θ hS hT ⊤ δ r (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) φ)
    {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {g : GA D S} {y : Formalism.MainNotions.StandardLatticesGL3.GA D a} (hg : GlobalTheory.BotFormula.IsFinPt S g y)
    (hg' : GlobalTheory.BotFormula.IsFinPt S g⁻¹ y⁻¹) (hy : g ∈ openOff S (stdLat S) Sf) (hn : ¬ (y ∈ intG D a ∧ CongOne D 𝔪 y)) :
    ip S T ν 𝓕 (om (g, 1) φ) φ = 0 := by
  subst hS hT
  have hr : r ≠ 0 := h.scale.ne_zero top_ne_bot
  obtain ⟨c', φ₁, hφ₁, e⟩ := exists_read_of_wd h hc _ hφ
  have hI : skewId D 𝔪 ≠ 0 := div_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hG.1)
    (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.FunObj.CosetTheta.conj_ne_bot hG.1))
  have hth := GlobalTheory.SkewTheta.iop_mem_thSp D δ h.crv e0 he0 𝔪 (GlobalTheory.SkewLatSelfDual.skewLat_SD hG.1 _)
  have eig : ∀ u : WO S T, HatPt r (skewId D 𝔪) u → heisO ψ S T (2 • u) φ =
      ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) • φ := fun u hu => by
    have h1 := heis_two_hatPt hr hI hφ₁.1 (fun z hz => heis_two_finPt h hth hφ₁ (mem_YYl_skew hz)) hu
    rw [e, heisO_smul, heisO_comm, h1, smul_comm]
  by_contra hne
  refine hn (mem_of_char_eq h.std h.gS h.gT hr hG hLB hY ho hg hg' hy fun u hu hu' => ?_)
  by_contra hd
  refine hne (ip_eq_zero_of_heis_eigen h.std hν (hω.om_pres _ _ hφ.1) hφ.1 (actO S T g 1 (2 • u)) ?_ ?_ (h.std.1.2.1 _) hd)
  · rw [← hω.om_heis _ _ _ _ hφ.1, eig u hu, map_smul]
  · rw [actO_two]; exact eig _ hu'

end GlobalTheory.CosetOrth

theorem GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  o + P.a ≤ P.d → ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
  ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
    ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0 := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ _ _ hφ hoa ν 𝓕 hcov y hy hn
  have hc : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < Ideal.absNorm 𝔪 := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (pow_pos this _)).ne')
  have hg' := hX.std.ptA y⁻¹
  rw [map_inv] at hg'
  exact GlobalTheory.CosetOrth.ip_eq_zero X.rkA X.rkB hX.setup hX.weil P.vac.1 hG hLB (fun z => (hY z).2) hoa hc hφ hcov
    (hX.std.ptA y) hg' hy hn
