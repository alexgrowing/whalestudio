import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OrderValuation
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChangeStatement

noncomputable section

namespace GlobalTheory.TransferCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.PjFree (valSet algCls cusp Unf regular₂ trivSet isVal_valSet DomWt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36 (algVal allVal ordVal Comb LeastLe Transfer TransferAt TransferInt TransferComb TransferLeast
  ordVal_smul)

section Order

theorem iInf_le_iff_exists {m : ℕ} (f : Fin m → EReal) {x : EReal} (hx : x ≠ ⊤) :
    (⨅ k, f k) ≤ x ↔ ∃ k, f k ≤ x := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty (Fin m) with hm | hm
    · rw [iInf_of_empty] at h
      exact absurd (top_le_iff.1 h) hx
    · obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := f)
      exact ⟨k, hk.le.trans h⟩
  · rintro ⟨k, hk⟩
    exact (iInf_le f k).trans hk

theorem lin_ne_top (ν c' : ℝ) {x : EReal} (h0 : 0 ≤ x) (ht : x ≠ ⊤) : (ν : EReal) + (c' : EReal) * x ≠ ⊤ := by
  have hb : x ≠ ⊥ := fun hb => by simp [hb] at h0
  lift x to ℝ using ⟨ht, hb⟩
  rw [← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_ne_top _

theorem leastLe_iff {R : Type} {m : ℕ} (w : Fin m → R) (ν : ℝ) (v : R → EReal) :
    LeastLe w ν v ↔ (⨅ k, v (w k)) ≤ (ν : EReal) :=
  (iInf_le_iff_exists _ (EReal.coe_ne_top ν)).symm

theorem comb_iff {R : Type} {m : ℕ} (w : Fin m → R) (η : R) (ν c' : ℝ) (v : R → EReal) :
    Comb w η ν c' v ↔ 0 ≤ v η ∧ (v η ≠ ⊤ → (⨅ k, v (w k)) ≤ (ν : EReal) + (c' : EReal) * v η) :=
  and_congr_right fun h0 => forall_congr' fun ht => (iInf_le_iff_exists _ (lin_ne_top ν c' h0 ht)).symm

theorem comb_zero_iff {R : Type} {m : ℕ} (w : Fin m → R) (η : R) (c' : ℝ) (v : R → EReal) :
    Comb w η 0 c' v ↔ 0 ≤ v η ∧ (v η ≠ ⊤ → (⨅ k, v (w k)) ≤ (c' : EReal) * v η) := by
  rw [comb_iff, EReal.coe_zero, zero_add]

end Order

section Approx

variable {K : Type} [Field K] [NumberField K]

theorem vLa_le_of_le (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : la.valuation K b ≤ la.valuation K a) : vLa la a ≤ vLa la b := by
  have := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 hb) ((la.valuation K).ne_zero_iff.2 ha)).2 h
  simp only [vLa]; omega

theorem exists_unit_at (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ vLa la b = 0 ∧ ∀ la' : HeightOneSpectrum (𝓞 K), la' ≠ la → vLa la' a ≤ vLa la' b := by
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx0
  have := la.isMaximal
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI la.asIdeal
  obtain ⟨p, hp, b, hb, hpb⟩ := Submodule.mem_sup.1 (hQ ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ la.asIdeal ⊔ Q)
  have hbn : b ∉ la.asIdeal := fun h => la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hpb ▸ add_mem hp h))
  have hb0 : b ≠ 0 := by rintro rfl; exact hbn (zero_mem _)
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  refine ⟨algebraMap (𝓞 K) K b, hbK, ?_, fun la' hne => vLa_le_of_le la' ha hbK ?_⟩
  · have : la.valuation K (algebraMap (𝓞 K) K b) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hbn
    simp only [vLa, this, WithZero.log_one, neg_zero]
  · have hnle : ¬ la.asIdeal ^ Multiset.count la.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x}))
        ≤ la'.asIdeal := fun h => by
      have h1 : la.asIdeal ≤ la'.asIdeal := by
        have := la'.isPrime
        exact Ideal.IsPrime.le_of_pow_le h
      exact hne (HeightOneSpectrum.ext (la.isMaximal.eq_of_le la'.isPrime.ne_top h1).symm)
    obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.1 hnle
    have hm : t * b ∈ Ideal.span {x} := hfac ▸ Ideal.mul_mem_mul ht hb
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hm
    have ht1 : la'.intValuation t = 1 := (HeightOneSpectrum.intValuation_eq_one_iff).2 htn
    have h1 : la'.intValuation b ≤ la'.intValuation x := by
      have e : la'.intValuation s * la'.intValuation x = la'.intValuation b := by
        rw [← map_mul, hs, map_mul, ht1, one_mul]
      rw [← e]
      exact mul_le_of_le_one_left' (la'.intValuation_le_one s)
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have hy' : 0 < la'.intValuation y := zero_lt_iff.2 (la'.intValuation_ne_zero y hy0)
    rw [le_div_iff₀ hy']
    exact (mul_le_of_le_one_right' (la'.intValuation_le_one y)).trans h1

end Approx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Objects

variable (Xo c)

theorem trivSet_eq : trivSet Xo c = ordVal Xo c := by
  ext q
  exact ⟨fun ⟨T, ι, y, ht, hq⟩ => ⟨T, ι, ht, y, hq⟩, fun ⟨T, ι, ht, y, hq⟩ => ⟨T, ι, y, ht, hq⟩⟩

variable {Xo c}

theorem noCommonZero_of_fields (hT : AllTest Xo c) {m : ℕ} {w : Fin m → Rul Xo c}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) : Formalism.L2.PjFree.NoCommonZero Xo c w :=
  fun k _ _ _ y => h k y (hT k y)

theorem noCommonZero_of_closed
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hB : GlobalTheory.Reg.FrBC Xo c)
    {m : ℕ} {w : Fin m → Rul Xo c}
    (hw : ∀ k, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (w k))
    (h : Formalism.L2.PjFree.NoCommonZero Xo c w) : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w := by
  intro L _ _ y hy
  let φ : L →ₐ[c.F] AlgebraicClosure L := IsScalarTower.toAlgHom c.F L (AlgebraicClosure L)
  obtain ⟨z, hz⟩ := hB L _ φ y
  obtain ⟨k, hk⟩ := h _ z
  refine ⟨k, fun h0 => hk ?_⟩
  have hz' : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, ψ, y', hy'⟩ := hy
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hz⟩
  have e : evR Xo c (w k) z = φ (evR Xo c (w k) y) := by
    unfold evR evalAt
    rw [dif_pos hz', dif_pos hy]
    exact hW (w k) (hw k) _ _ _ _ _ _ _ z hz'.choose_spec.choose_spec.choose_spec
      (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y z hy.choose_spec.choose_spec.choose_spec hz)
  rw [e, h0, map_zero]

end Objects

section Joint

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def JointInt : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n,
    (∀ la, ∀ v ∈ algVal Xo c la, 0 ≤ v F) → (∀ la, ∀ v ∈ allVal Xo c la, 0 ≤ v F) ∧ ∀ o ∈ ordVal Xo c, 0 ≤ o F

def JointComb (nz : ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE : ℕ),
    Dom aL nL → Dom aE nE → ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz w →
    ∀ η ∈ cusp Xo c U aE nE, ∀ (ν : HeightOneSpectrum (𝓞 c.F) → ℝ) (c' : ℝ), 0 ≤ c' →
      (∀ la, ∀ v ∈ algVal Xo c la, Comb w η (ν la) c' v) →
        (∀ la, ∀ v ∈ allVal Xo c la, Comb w η (ν la) c' v) ∧ ∀ o ∈ ordVal Xo c, Comb w η 0 c' o

def JointLeast (nz : ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ), Dom aL nL →
    ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz w →
    ∀ ν : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ algVal Xo c la, LeastLe w (ν la) v) → ∀ la, ∀ v ∈ allVal Xo c la, LeastLe w (ν la) v

theorem regular_iff_joint : regular₂ Xo c U ↔ JointInt Xo c U ∧
    JointComb Xo c U (fun w => Formalism.L2.PjFree.NoCommonZero Xo c w) ∧
    JointLeast Xo c U (fun w => Formalism.L2.PjFree.NoCommonZero Xo c w) := by
  unfold regular₂ ReciprocityTheory.ChartRestriction.G.T0.RegLaw
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h a n hd F hF h0
      obtain ⟨h1, h2⟩ := h ⟨(a, n), hd⟩ ⟨F, hF⟩ fun la y => h0 la y.1 y.2
      exact ⟨fun la v hv => h1 la ⟨v, hv⟩, fun o ho => h2 ⟨o, (trivSet_eq Xo c).symm ▸ ho⟩⟩
    · intro h w F h0
      obtain ⟨h1, h2⟩ := h w.1.1 w.1.2 w.2 F.1 F.2 fun la v hv => h0 la ⟨v, hv⟩
      exact ⟨fun la y => h1 la y.1 y.2, fun q => h2 q.1 (trivSet_eq Xo c ▸ q.2)⟩
  · constructor
    · intro h aL nL aE nE hL hE m w hw hz η hη ν c' hc h0
      obtain ⟨h1, h2⟩ := h ⟨(aL, nL), hL⟩ ⟨(aE, nE), hE⟩ m (fun k => ⟨w k, hw k⟩) ⟨η, hη⟩ ν c' hc hz
        fun la y => (comb_iff w η _ c' y.1).1 (h0 la y.1 y.2)
      exact ⟨fun la v hv => (comb_iff w η _ c' v).2 (h1 la ⟨v, hv⟩),
        fun o ho => (comb_zero_iff w η c' o).2 (h2 ⟨o, (trivSet_eq Xo c).symm ▸ ho⟩)⟩
    · intro h wL wE m ws et ν c' hc hz h0
      obtain ⟨h1, h2⟩ := h _ _ _ _ wL.2 wE.2 m (fun k => (ws k).1) (fun k => (ws k).2) hz et.1 et.2 ν c' hc
        fun la v hv => (comb_iff _ _ _ c' v).2 (h0 la ⟨v, hv⟩)
      exact ⟨fun la y => (comb_iff _ _ _ c' y.1).1 (h1 la y.1 y.2),
        fun q => (comb_zero_iff _ _ c' q.1).1 (h2 q.1 (trivSet_eq Xo c ▸ q.2))⟩
  · unfold JointLeast
    simp only [leastLe_iff]
    exact Iff.rfl

def BoundedDenominators : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n,
    ∃ b : c.F, b ≠ 0 ∧ ∀ la, ∀ v ∈ algVal Xo c la, 0 ≤ v (b • F)

def BoundsSpread : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ), Dom aL nL → ∀ (m : ℕ) (w : Fin m → Rul Xo c),
    (∀ k, w k ∈ cusp Xo c U aL nL) → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w →
    ∀ la la' : HeightOneSpectrum (𝓞 c.F),
      (∀ ν : ℝ, (∀ v ∈ algVal Xo c la, LeastLe w ν v) → ∃ ν' : ℝ, ∀ v ∈ algVal Xo c la', LeastLe w ν' v) ∧
      ∀ (aE : (E →+* ℂ) × ℕ → ℕ) (nE : ℕ), Dom aE nE → ∀ η ∈ cusp Xo c U aE nE, ∀ ν c' : ℝ, 0 ≤ c' →
        (∀ v ∈ algVal Xo c la, Comb w η ν c' v) → (∀ v ∈ algVal Xo c la', 0 ≤ v η) →
          ∃ ν' : ℝ, ∀ v ∈ algVal Xo c la', Comb w η ν' c' v

variable {Xo c U}

theorem exists_place : Nonempty (HeightOneSpectrum (𝓞 c.F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 c.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField c.F)⟩⟩

theorem regular_of_transfer
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hB : GlobalTheory.Reg.FrBC Xo c)
    (h : Transfer Xo c U) : regular₂ Xo c U := by
  obtain ⟨la₀⟩ := exists_place (c := c)
  refine (regular_iff_joint Xo c U).2 ⟨fun a n hd F hF h0 => ?_, fun aL nL aE nE hL hE m w hw hz η hη ν c' hc h0 => ?_,
    fun aL nL hL m w hw hz ν h0 la => ?_⟩
  · exact ⟨fun la => (h.1 la a n hd F hF (h0 la)).1, (h.1 la₀ a n hd F hF (h0 la₀)).2⟩
  · have hz' := noCommonZero_of_closed hW hB (fun k => (Formalism.L2.PjFree.cusp_le_sec Xo c U _ _ (hw k)).1) hz
    exact ⟨fun la => (h.2.1 la aL nL aE nE hL hE m w hw hz' η hη _ c' hc (h0 la)).1,
      (h.2.1 la₀ aL nL aE nE hL hE m w hw hz' η hη _ c' hc (h0 la₀)).2⟩
  · have hz' := noCommonZero_of_closed hW hB (fun k => (Formalism.L2.PjFree.cusp_le_sec Xo c U _ _ (hw k)).1) hz
    exact (h.2.2 la aL nL hL m w hw hz' _ (h0 la)).1

theorem regular_of_transferAt
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hB : GlobalTheory.Reg.FrBC Xo c)
    (h : TransferAt Xo c U) : regular₂ Xo c U :=
  regular_of_transfer hW hB h.transfer

theorem BoundedDenominators.exists_unit (hD : BoundedDenominators Xo c U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hd : Dom a n) {F : Rul Xo c} (hF : F ∈ cusp Xo c U a n) (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ b : c.F, b ≠ 0 ∧ (∀ v ∈ allVal Xo c la, v (b • F) = v F) ∧
      ∀ la', la' ≠ la → ∀ v ∈ algVal Xo c la', 0 ≤ v (b • F) := by
  obtain ⟨a₀, ha, h0⟩ := hD a n hd F hF
  obtain ⟨b, hb, hb0, hle⟩ := exists_unit_at la ha
  refine ⟨b, hb, fun v hv => ?_, fun la' hne v hv => (h0 la' v hv).trans ?_⟩
  · rw [(isVal_valSet la v hv).smul b F hb, hb0]; simp
  · rw [(isVal_valSet la' v hv).smul b F hb, (isVal_valSet la' v hv).smul a₀ F ha]
    refine add_le_add_left (EReal.coe_le_coe_iff.2 ?_) _
    exact_mod_cast hle la' hne

variable (Xo c)

theorem evalWD_framed : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_fr (frChartF_of (GlobalTheory.T.chartCoverF_of_sectionBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))

theorem frBC_framed : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem allTest_framed : AllTest Xo c :=
  GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c

variable {Xo c} in

theorem noCommonZero_iff_of_sec {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {w : Fin m → Rul Xo c}
    (hw : ∀ k, w k ∈ sec Xo c a n) :
    Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w :=
  ⟨noCommonZero_of_closed (evalWD_framed Xo c) (frBC_framed Xo c) fun k => (hw k).1,
    noCommonZero_of_fields (allTest_framed Xo c)⟩

omit [NumberField E] [IsCMField E] in

theorem forall_domWt (P : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Prop) :
    (∀ w : DomWt E, P w.1.1 w.1.2) ↔ ∀ a n, Dom a n → P a n :=
  ⟨fun h a n hd => h ⟨(a, n), hd⟩, fun h w => h _ _ w.2⟩

variable (U)

theorem regular_iff_joint_valuation : regular₂ Xo c U ↔ JointInt Xo c U ∧
    JointComb Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) ∧
    JointLeast Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) := by
  have e : ∀ {a n m} {w : Fin m → Rul Xo c}, (∀ k, w k ∈ cusp Xo c U a n) →
      (Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) :=
    fun hw => noCommonZero_iff_of_sec fun k => Formalism.L2.PjFree.cusp_le_sec Xo c U _ _ (hw k)
  rw [regular_iff_joint]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact ⟨fun h aL nL aE nE hL hE m w hw hz => h aL nL aE nE hL hE m w hw ((e hw).2 hz),
      fun h aL nL aE nE hL hE m w hw hz => h aL nL aE nE hL hE m w hw ((e hw).1 hz)⟩
  · exact ⟨fun h aL nL hL m w hw hz => h aL nL hL m w hw ((e hw).2 hz),
      fun h aL nL hL m w hw hz => h aL nL hL m w hw ((e hw).1 hz)⟩

theorem compare :
    Formalism.L2.PjFree.trivialClassCondition Xo c = GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.trivialClassCondition Xo c ∧ trivSet Xo c = ordVal Xo c ∧
    (∀ P : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Prop, (∀ w : DomWt E, P w.1.1 w.1.2) ↔ ∀ a n, Dom a n → P a n) ∧
    (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ sec Xo c a n) →
      (Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w)) ∧
    (regular₂ Xo c U ↔ JointInt Xo c U ∧ JointComb Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) ∧
      JointLeast Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w)) ∧
    (Transfer Xo c U → regular₂ Xo c U) ∧ (TransferAt Xo c U → regular₂ Xo c U) :=
  ⟨rfl, trivSet_eq Xo c, forall_domWt, fun _ _ _ _ hw => noCommonZero_iff_of_sec hw, regular_iff_joint_valuation Xo c U,
    regular_of_transfer (evalWD_framed Xo c) (frBC_framed Xo c),
    regular_of_transferAt (evalWD_framed Xo c) (frBC_framed Xo c)⟩

end Joint

end GlobalTheory.TransferCompare
