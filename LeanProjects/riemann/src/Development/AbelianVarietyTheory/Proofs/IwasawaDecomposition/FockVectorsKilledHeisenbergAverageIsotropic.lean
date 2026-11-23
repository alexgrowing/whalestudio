import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.ThetaSupport

open GlobalTheory.IdemModTwo GlobalTheory.SplitHecke

variable {D : D7}

theorem exists_edge {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ x, psiV D.host.F ψ v x ≠ 1 ∧ ∀ y, Valued.v y < Valued.v x → psiV D.host.F ψ v y = 1 := by
  have : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨a, ha, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling hψ
  have h := GlobalTheory.AdeleCharConductor.conductor_of_scaling hψ ha hinf v
  generalize FractionalIdeal.count (↥D.host.F) v _ = m at h
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective D.host.F v (WithZero.exp (m + 1))
  have h1 := (h z).not.2 (by rw [hz, WithZero.exp_le_exp]; omega)
  push Not at h1
  obtain ⟨s, hs, h1⟩ := h1
  refine ⟨z * s, h1, fun y hy => ?_⟩
  have h2 : Valued.v y < WithZero.exp (m + 1) := by
    refine hy.trans_le ?_
    rw [map_mul, hz]
    exact mul_le_of_le_one_right' hs
  have h3 : Valued.v y ≤ WithZero.exp m := by
    rcases eq_or_ne (Valued.v y) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at h2
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  simpa only [mul_one] using (h y).2 h3 1 (one_mem _)

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

theorem char_trace (ψ : AddChar (AF D.host.F) ℂ) (he : SplitAt D v e) (a : AE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (e * a)) = psiV D.host.F ψ v (GlobalTheory.SplitChart.comp he a) := by
  have h1 := GlobalTheory.SplitChart.sc_spec he 1
  rw [← GlobalTheory.SplitChart.comp_apply, map_one, mul_one] at h1
  have h2 := GlobalTheory.SplitAnnihilator.trace_split he (GlobalTheory.SplitChart.comp he a) 1
  rw [← h1, mul_assoc, he.1, mul_one, GlobalTheory.SplitChart.comp_apply, ← GlobalTheory.SplitChart.sc_spec he a] at h2
  rw [h2]
  rfl

theorem psiV_add (ψ : AddChar (AF D.host.F) ℂ) (he : SplitAt D v e) (x y : Fv D.host.F v) :
    psiV D.host.F ψ v (x + y) = psiV D.host.F ψ v x * psiV D.host.F ψ v y := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.SplitChart.chart_comp he).1 x
  obtain ⟨b, rfl⟩ := (GlobalTheory.SplitChart.chart_comp he).1 y
  rw [← RingHom.map_add, ← char_trace, ← char_trace, ← char_trace, mul_add, map_add, AddChar.map_add_eq_mul]

theorem psiV_natCast (ψ : AddChar (AF D.host.F) ℂ) (he : SplitAt D v e) (n : ℕ) (x : Fv D.host.F v) :
    psiV D.host.F ψ v (n * x) = psiV D.host.F ψ v x ^ n := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.SplitChart.chart_comp he).1 x
  rw [← map_natCast (GlobalTheory.SplitChart.comp he), ← RingHom.map_mul, ← char_trace, ← char_trace, mul_left_comm,
    ← nsmul_eq_mul, map_nsmul, AddChar.map_nsmul_eq_pow]

variable {π : AE D →+* Fv D.host.F v} {PP : Pl D.host.E}

theorem val_lt_one_of_mem (he : Formalism.L2.NTheta.IsIdemAt e PP) (hπ : Chart e v π) {x : 𝓞 D.host.E} (hx : x ∈ PP.asIdeal) :
    Valued.v (π (incA D (x : D.host.E))) < 1 := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hx0 : Valued.v ((π.comp (incA D)) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff, _root_.map_ne_zero]
      exact fun h => h0 (Subtype.ext h)
    rw [he.2 x h0, hπ.2.2.2, isInt_Ov] at hx
    have hx' : ¬ Valued.v ((π.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1 := hx
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)] at hx'
    exact hx'

theorem exists_chart_levels (he : Formalism.L2.NTheta.IsIdemAt e PP) (hπ : Chart e v π) :
    ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ z, φ (toEAf D z) = π z) ∧
      ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 → Valued.v (φ s) < 1 := by
  obtain ⟨φ₀, h₀⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  let φ : Datum.EAf D →+* Fv D.host.F v := φ₀.comp
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom
  have hφ : ∀ z, φ (toEAf D z) = π z := fun z => by
    rw [← h₀]
    exact congrArg φ₀ ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply _)
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, Valued.v (φ s) ≤ 1 := fun s => by
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) s
    rw [← ha, hφ]
    refine isInt_Ov.1 ((hπ.2.2.2 a).1 (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_))
    rw [RingHom.map_mul, ha]
    exact mul_mem hi s.2
  refine ⟨φ, hφ, fun s h => ?_⟩
  have hm : s ∈ idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS D.host.F PP.asIdeal)
      (cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm.injective).1 h
  clear h
  refine Submodule.span_induction (p := fun s _ => Valued.v (φ (s : Formalism.L2.Herm.intAf D.host.F D.host.E)) < 1)
    ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨x, hx, rfl⟩
    have : φ (oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) = π (incA D (x : D.host.E)) :=
      hφ (incA D (x : D.host.E))
    rw [this]
    exact val_lt_one_of_mem he hπ hx
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, RingHom.map_add]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, RingHom.map_mul, Valuation.map_mul]
    exact (mul_le_of_le_one_left' (hint c)).trans_lt hx

theorem val_row_lt {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n : ℕ}
    (u d : Fin n → K) (j : Fin n) (hj : d j ≠ 0) (hd : ∀ i, w (d i) ≤ w (d j))
    (hu : ∀ i, w (u i - if j = i then 1 else 0) < 1) : w (u ⬝ᵥ d - d j) < w (d j) := by
  have h0 : w (d j) ≠ 0 := (Valuation.ne_zero_iff _).2 hj
  have : u ⬝ᵥ d - d j = ∑ i, (u i - if j = i then 1 else 0) * d i := by
    simp [dotProduct, sub_mul, Finset.sum_sub_distrib]
  rw [this]
  refine Valuation.map_sum_lt _ h0 fun i _ => ?_
  rw [Valuation.map_mul]
  calc _ ≤ w (u i - if j = i then 1 else 0) * w (d j) := mul_le_mul_right (hd i) _
    _ < w (d j) := mul_lt_of_lt_one_left (zero_lt_iff.2 h0) (hu i)

def adj (S T : HSp D) (t : WO S T) : Matrix (Fin S.rank) (Fin T.rank) (AE D) :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

theorem hO_vecMulVec (S T : HSp D) (t : WO S T) (c : Fin T.rank → AE D) (l : Fin S.rank → AE D) :
    hO S T (vecMulVec c l) t = l ⬝ᵥ adj S T t *ᵥ c := by
  rw [hO_trace, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  rfl

theorem symplO_vecMulVec (S T : HSp D) (t : WO S T) (c : Fin T.rank → AE D) (l : Fin S.rank → AE D) (e : AE D) :
    symplO S T t (vecMulVec c fun a => e * l a) =
      Algebra.trace (AF D.host.F) (AE D) (e * (-(incA D D.host.xi0 * (l ⬝ᵥ adj S T t *ᵥ c)) : AE D)) := by
  rw [GlobalTheory.SplitScalar.symplO_skew, symplO, hO_vecMulVec]
  refine (LinearMap.map_neg _ _).symm.trans (congrArg _ ?_)
  have : (fun a => e * l a) ⬝ᵥ adj S T t *ᵥ c = e * (l ⬝ᵥ adj S T t *ᵥ c) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [this]
  ring

theorem val_sub_lt (φ : Datum.EAf D →+* Fv D.host.F v)
    (hres : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 → Valued.v (φ s) < 1) {a b : ℕ} (hr : a ≤ b)
    {U : Matrix (Fin b) (Fin a) (Datum.EAf D)} (hU : IsIntM U) (hU' : topL a (redM PP U) = 1) (j i : Fin a) :
    Valued.v (U.map φ (Fin.castLE hr j) i - if j = i then 1 else 0) < 1 := by
  have h1 := congrFun (congrFun hU' j) i
  rw [topL, dif_pos ⟨(Fin.castLE hr j).2, i.2⟩, redM, dif_pos (hU _ _), Matrix.one_apply] at h1
  by_cases h : j = i
  · rw [if_pos h] at h1 ⊢
    have h2 := hres (⟨_, hU (Fin.castLE hr j) i⟩ - 1) (by
      rw [RingHom.map_sub, sub_eq_zero, RingHom.map_one]
      exact h1)
    rwa [AddSubgroupClass.coe_sub, RingHom.map_sub, Subring.coe_one, RingHom.map_one] at h2
  · rw [if_neg h] at h1 ⊢
    rw [sub_zero]
    exact hres ⟨_, hU (Fin.castLE hr j) i⟩ h1

set_option maxHeartbeats 1000000 in

theorem exists_const {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (c : Fin T.rank → AE D) (hc : ∃ i, e * c i ≠ 0) (hr : T.rank ≤ S.rank) :
    ∃ (l : Fin S.rank → AE D) (ζ : ℂ) (n : ℕ), 0 < n ∧ ζ ≠ 1 ∧ ζ ^ n = 1 ∧ (∀ a, e * l a = l a) ∧
      ∀ t, IsIntM (frMapAdj S T βS βT t) → topL T.rank (redM PP (frMapAdj S T βS βT t)) = 1 →
        ψ (symplO S T t (vecMulVec c l)) = ζ := by
  obtain ⟨v, hv⟩ := (isSplitIdem_iff e).1 he.1
  have hπ := GlobalTheory.SplitChart.chart_comp hv
  set π := GlobalTheory.SplitChart.comp hv with hπdef
  obtain ⟨φ, hφ, hres⟩ := exists_chart_levels he hπ
  obtain ⟨x, hx, hx'⟩ := exists_edge hψ v
  let d : Fin T.rank → Fv D.host.F v := (βT⁻¹).val.map φ *ᵥ (π ∘ c)
  have hd : βT.val.map φ *ᵥ d = π ∘ c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mulVec]
  obtain ⟨i₀, hi₀⟩ := hc
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_max_image (fun i => Valued.v (d i)) ⟨i₀, Finset.mem_univ _⟩
  have hj0 : d j ≠ 0 := fun h => by
    have h0 : d = 0 := funext fun i => by
      have := hj i (Finset.mem_univ _)
      rwa [h, map_zero, le_zero_iff, map_eq_zero] at this
    rw [h0, Matrix.mulVec_zero] at hd
    exact hi₀ ((hπ.2.1 _).1 (congrFun hd i₀).symm)
  have hξ : π (incA D D.host.xi0) ≠ 0 :=
    (_root_.map_ne_zero (π.comp (incA D))).2 (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D)
  let s : Fv D.host.F v := -(x / (π (incA D D.host.xi0) * d j))
  choose l₀ hl₀ using fun a => hπ.1 (s * φ ((βS⁻¹).val (Fin.castLE hr j) a))
  have hN : Ideal.absNorm PP.asIdeal ≠ 0 := fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hx0 : Valued.v x ≠ 0 := fun h => by
    rw [map_eq_zero] at h
    have := psiV_natCast ψ hv 0 x
    rw [Nat.cast_zero, zero_mul, pow_zero, ← h] at this
    exact hx this
  refine ⟨fun a => e * l₀ a, psiV D.host.F ψ v x, Ideal.absNorm PP.asIdeal, Nat.pos_of_ne_zero hN, hx, ?_,
    fun a => by rw [← mul_assoc, hv.1], fun t ht ht' => ?_⟩
  · rw [← psiV_natCast ψ hv]
    refine hx' _ ?_
    have := val_lt_one_of_mem he hπ (Ideal.absNorm_mem PP.asIdeal)
    have e1 : ((Ideal.absNorm PP.asIdeal : 𝓞 D.host.E) : D.host.E) = Ideal.absNorm PP.asIdeal :=
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
    rw [e1, map_natCast, map_natCast] at this
    rw [Valuation.map_mul]
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 hx0) this
  · have hU : (frMapAdj S T βS βT t).map φ = (βS⁻¹).val.map φ * (adj S T t).map π * βT.val.map φ := by
      have : (adj S T t).map π = ((adj S T t).map (toEAf D)).map φ := by
        exact Matrix.ext fun a b => (hφ _).symm
      rw [this, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl
    have hrow := val_row_lt Valued.v ((frMapAdj S T βS βT t).map φ (Fin.castLE hr j)) d j hj0
      (fun i => hj i (Finset.mem_univ _)) (val_sub_lt φ hres hr ht ht' j)
    set z := (frMapAdj S T βS βT t).map φ (Fin.castLE hr j) ⬝ᵥ d with hz
    have h1 : π (l₀ ⬝ᵥ adj S T t *ᵥ c) = s * z := by
      have h2 : z = ((frMapAdj S T βS βT t).map φ *ᵥ d) (Fin.castLE hr j) := rfl
      rw [h2, hU, ← Matrix.mulVec_mulVec, hd, ← Matrix.mulVec_mulVec, RingHom.map_dotProduct]
      have h3 : π ∘ (adj S T t *ᵥ c) = (adj S T t).map π *ᵥ (π ∘ c) := funext fun a => RingHom.map_mulVec π _ _ a
      rw [h3]
      generalize (adj S T t).map π *ᵥ (π ∘ c) = w
      simp only [dotProduct, Matrix.mulVec, Function.comp_apply, hl₀, Matrix.map_apply, Finset.mul_sum, mul_assoc]
    rw [symplO_vecMulVec, char_trace ψ hv, ← hπdef, RingHom.map_neg, RingHom.map_mul, h1]
    have h5 : -(π (incA D D.host.xi0) * (s * z)) = x + x * ((z - d j) / d j) := by
      simp only [s]
      field_simp
      ring
    rw [h5, psiV_add ψ hv, hx' (x * _), mul_one]
    rw [Valuation.map_mul, map_div₀]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hx0)
      ((div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hj0))).2 hrow)

set_option maxHeartbeats 1000000 in
open Classical in

theorem exists_eigen {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hr : T.rank ≤ S.rank) (hPP : PP ∈ Pg) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f)
    (c : Fin T.rank → AE D) (hc : ∀ e, IsSplitIdem D e → ∃ i, e * c i ≠ 0) :
    ∃ (l : Fin S.rank → AE D) (ζ : ℂ) (n : ℕ), 0 < n ∧ ζ ≠ 1 ∧ ζ ^ n = 1 ∧ ∀ k : ℕ,
      (vecMulVec c (k • l)).map (infPart D) = 0 ∧ heisO ψ S T (vecMulVec c (k • l)) f = ζ ^ k • f := by
  obtain ⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinf := ho.conj.infPart_eq
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
    (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hP := Finset.mem_union_left Q hPP
  have h3 : es PP * ∑ j ∈ Pg ∪ Q, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (GlobalTheory.PlaceVec.isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hP
  rw [← h2] at h3
  obtain ⟨l, ζ, n, hn, hζ, hζn, hl, hconst⟩ := exists_const hv.1.1 S T βS βT (h1 PP hP) c (hc _ (h1 PP hP).1) hr
  refine ⟨l, ζ, n, hn, hζ, hζn, fun k => ?_⟩
  have hk : vecMulVec c (k • l) = k • vecMulVec c l := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, vecMulVec_apply, vecMulVec_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
  have hhalf : IsHalf e (vecMulVec c (k • l)) := fun i j => by
    rw [vecMulVec_apply, Pi.smul_apply, nsmul_eq_mul]
    rw [← hl j]
    linear_combination (c i * k * l j) * h3
  refine ⟨Matrix.ext fun i j => by
    rw [Matrix.map_apply, ← hhalf i j, RingHom.map_mul, ho.infPart_eq, zero_mul]; rfl, ?_⟩
  rw [hall Tm hTm, ← hTm.modul _ hSB _ (by rwa [GlobalTheory.LatVac.cA_cA]), ← map_smul]
  refine congrArg Tm (funext fun t => ?_)
  rw [Pi.smul_apply, smul_eq_mul]
  split_ifs with ht
  · by_cases hK : ∀ PP ∈ Pg, LowZero T.rank (redM PP (frMapAdj S T βS βT t)) ∧
        topL T.rank (redM PP (frMapAdj S T βS βT t)) = 1
    · rw [← hconst t ht.2 (hK PP hPP).2, hk, ← GlobalTheory.LatVac.symplHom_apply, map_nsmul, AddChar.map_nsmul_eq_pow]
      rfl
    · rw [omegaK, if_neg hK, zero_mul, mul_zero, mul_zero]
  · rw [mul_zero, mul_zero]

theorem exists_mem_Pg {T : Type} {L : LevCh D T} {μ0 : T} (h : L.Is μ0) : ∃ PP, PP ∈ L.Pg := by
  have hp := D.host.g_prime 0
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 D.host.E)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h1)
  have hg := hle (Ideal.mem_span_singleton_self _)
  have h0 : m ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (Nat.cast_eq_zero.1 hg)
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P 0 ⟨m, hm.isPrime, h0⟩ hg with h1 | ⟨w, h1, -⟩
  · exact ⟨_, (h.Pg _).2 ⟨0, h1⟩⟩
  · exact ⟨_, (h.Pg _).2 ⟨0, h1⟩⟩

theorem mt_mul_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  have : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = Formalism.L2.Theta.mt V (g * g⁻¹) := rfl
  rw [this, mul_inv_cancel]
  rfl

theorem sum_heisO_along_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → R.thP_pt_theta → ∀ i t P h g ξ, IsoVec (Wc D i) ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin (Vc D i).rank → AE D, ∑ k, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ (a k)) (R.ωP i t (h, g) (R.ptP i t P)) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hθ hω hv hth i t P h g ξ hξ
  obtain ⟨PP, hPP⟩ := exists_mem_Pg hL
  let c : Fin (Wc D i).rank → AE D := Formalism.L2.Theta.mt (Wc D i) g⁻¹ *ᵥ fun a => incA D (ξ a)
  have hc : Formalism.L2.Theta.mt (Wc D i) g *ᵥ c = fun a => incA D (ξ a) := by
    rw [Matrix.mulVec_mulVec, mt_mul_inv, Matrix.one_mulVec]
  obtain ⟨l, ζ, n, hn, hζ, hζn, hl⟩ := exists_eigen
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) hPP (hv i t) c fun e he => by
      by_contra hn
      push Not at hn
      obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
      refine hξ.1 (funext fun a => ?_)
      refine (map_eq_zero (π.comp (incA D))).1 ?_
      rw [RingHom.comp_apply, ← congrFun hc a, RingHom.map_mulVec]
      have : π ∘ c = 0 := funext fun b => (hπ.2.1 _).2 (hn b)
      rw [this, Matrix.mulVec_zero]
      rfl
  refine ⟨n, hn, fun k => ((k : ℕ) • l) ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹, ?_⟩
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hth i t 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  have key : ∀ k : ℕ, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ ((k • l) ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹))
      (R.ωP i t (h, g) (R.ptP i t P)) = ζ ^ k • R.ωP i t (h, g) (R.ptP i t P) := fun k => by
    have h1 : along (Vc D i) (Wc D i) ξ ((k • l) ᵥ* Formalism.L2.Theta.mt (Vc D i) h⁻¹) =
        actO (Vc D i) (Wc D i) h g (vecMulVec c (k • l)) := by
      rw [actO, Matrix.mul_vecMulVec, hc, Matrix.vecMulVec_mul, along]
    rw [h1, ← (hω i t).om_heis h g _ _ (hth i t P), ← map_smul]
    refine congrArg _ ?_
    rw [RealDat.ptP, ← ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ (hω i t).std hθ _ hf).2 _ (hl k).1).2, (hl k).2,
      GlobalTheory.FiniteFock.pureTensorO_smul]
  simp only [key]
  rw [← Finset.sum_smul, Fin.sum_univ_eq_sum_range (fun k => ζ ^ k), geom_sum_eq hζ, hζn, sub_self, zero_div, zero_smul]

end GlobalTheory.ThetaSupport

end
