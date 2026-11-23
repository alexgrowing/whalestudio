import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTraceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumClsLeEncard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMassesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClassesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem pair_mem_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, S.IsCls C → φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · rw [mul_one]
    gcongr
    exact h _ ho.1
  · simp

theorem q_pow_le (S : Frames L r k) (e : ℤ) (he0 : 0 ≤ e) (he : e ≤ S.vth + S.a + S.vD) (m : ℕ) :
    (S.q : ℝ≥0∞) ^ (m * e.toNat) ≤ ENNReal.ofReal (S.Hp ^ m) := by
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [← zpow_natCast, Int.toNat_of_nonneg he0]
  exact zpow_le_zpow_right₀ hq1 he

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem vth_nonneg (S : Frames L r k) : 0 ≤ S.vth := by
  unfold Frames.vth
  split_ifs <;> norm_num

theorem total_weight_le (S : Frames L r k) (ha : 0 ≤ S.a) (hD : 0 ≤ S.vD) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (r * (r + 1))) := by
  have hv := vth_nonneg S
  exact ((GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans (GlobalTheory.IntClsCount.main L r k S hD)).trans
    (q_pow_le S _ (by omega) (by omega) _)

theorem sumCls_eq_single (S : Frames L r k) (h1 : (S.sumCls fun _ => 1) ≤ 1) (φ : Set S.FrP → ℝ≥0∞)
    (hφ : ∀ h ∈ S.St, ∀ C, φ (h • C) = φ C) (C : Set S.FrP) (hC : S.IsIntCls C) :
    S.sumCls φ = ENNReal.ofReal (S.wC C) * φ C := by
  let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C
  obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St C :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
  have hh' : h.1 • C = o'.out := hh
  have ho' : S.IsIntCls o'.out := hh' ▸ GlobalTheory.HL.ClassCount.isIntCls_smul S h.2 hC
  unfold Frames.sumCls at h1 ⊢
  rw [tsum_eq_single o', if_pos ho', ← hh', hφ _ h.2, ((GlobalTheory.HL.volSt L r k S).2 C hC.1).2.2.2 _ h.2]
  intro o hne
  refine if_neg fun ho => ?_
  have h2 := (ENNReal.sum_le_tsum {o, o'}).trans h1
  rw [Finset.sum_pair hne, if_pos ho, if_pos ho', mul_one, mul_one] at h2
  have h3 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho.1).2.2.1
  have h4 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho'.1).2.2.1
  have h5 := (add_le_add h3 h4).trans h2
  norm_num at h5

end GlobalTheory.HL.GenMass

open GlobalTheory.HL.GenMass in

theorem GlobalTheory.HL.GenMass.total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ d₁ Λ₁, S.IsTerm d₁ Λ₁ → ∀ g : ℝ≥0∞, g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * (S.sumData fun d => S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ) → 0 < g ∧ g < ⊤ ∧ S.nn ≤ ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (S.Hp = 1 → S.nn = g) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk d₁ Λ₁ hT g hg
  obtain ⟨hSD, -, hMs, -, -, -, hI, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d₁ Λ₁ hT
  obtain ⟨ha, hD, -, -, hH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₁ Λ₁ hT
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ₁, hSD⟩
  have hv := vth_nonneg S
  have hp : (S.fr d₁ Λ₁, S.fr' d₁ Λ₁) ∈ S.Fr d₁ Λ₁ := pair_mem_cls S _ _
  have hsw := GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hnn : S.nn = S.sumCls fun C => S.sumData fun d => S.nT d C fun _ => True := hsw.1
  have hM := hU _ hI.1 _ hp (S.M d₁ Λ₁) le_rfl (fun x hx => (hMs hx).2)
    (fun x hx y hy => (hSD.2 y).2 (hMs hy).1 x (hMs hx).1)
  have hM' : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.M d₁ Λ₁) ∧
      S.massSig (S.M d₁ Λ₁) ≤ ENNReal.ofReal (2 * κ) := by
    simpa [Frames.M] using hM
  have hg' : g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.massSig (S.M d₁ Λ₁) := by
    rw [hg, (GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S _ hI.1 _ hp).2]
    rfl
  have hw := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ hI.1).2.2.1
  have hlow : ENNReal.ofReal (κ / 2) ≤ g := by
    rw [hg', ← one_mul (ENNReal.ofReal (κ / 2))]
    exact mul_le_mul' hw hM'.1
  refine ⟨(ENNReal.ofReal_pos.2 (by positivity)).trans_le hlow, ?_, ?_, fun h1 => ?_⟩
  · rw [hg']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hM'.2.trans_lt ENNReal.ofReal_lt_top)
  · have hφ : ∀ C, S.IsCls C → (S.sumData fun d => S.nT d C fun _ => True) ≤
        ENNReal.ofReal (S.Hp ^ (2 * (2 * r + 2))) * ENNReal.ofReal (2 * κ) := by
      intro C hC
      obtain ⟨p, hpC⟩ : ∃ p, p ∈ C := by
        obtain ⟨n, -, n', -, rfl⟩ := hC
        exact ⟨_, pair_mem_cls S _ _⟩
      refine ((GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC p hpC).1 fun _ => True).trans ?_
      refine (ENNReal.tsum_le_tsum (g := fun _ => ENNReal.ofReal (2 * κ)) fun Mh => ?_).trans ?_
      · refine (hU C hC p hpC Mh.1 Mh.2.1 Mh.2.2.1 Mh.2.2.2.1).2.trans (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← Nat.cast_pow]
        exact Nat.cast_inv_le_one _
      · have hc := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC p hpC ha
        have he : 2 * S.a.toNat * (2 * r + 2) = 2 * (2 * r + 2) * S.a.toNat := by ring
        rw [he] at hc
        have hc' := hc.trans (q_pow_le S _ ha (by omega) _)
        rw [ENNReal.tsum_const]
        refine mul_le_mul_left (le_trans (le_of_eq ?_) hc') _
        simp only [and_true]
        rfl
    rw [hnn]
    refine (sumCls_le S _ _ hφ).trans ?_
    refine (mul_le_mul_left (total_weight_le S ha hD) _).trans ?_
    refine le_trans ?_ (mul_le_mul_right hlow _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : S.Hp ^ (r * (r + 1)) * S.Hp ^ (2 * (2 * r + 2)) ≤
        S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hH (by nlinarith)
    have h3 : 0 ≤ S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hκ.le, mul_nonneg h3 hκ.le]
  · have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    have hB : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ := fun d Λ h => by
      by_contra hc
      have h2 := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.2.2.1 hc
      rw [h1] at h2
      have : S.q ≤ 1 := by exact_mod_cast h2
      omega
    have htw := total_weight_le S ha hD
    rw [h1, one_pow, ENNReal.ofReal_one] at htw
    rw [hnn, sumCls_eq_single S htw _ (fun h hh C => by simp only [hsw.2 h hh]) _ hI, hg]
    congr 2
    funext d
    unfold Frames.nT
    congr 2
    ext Λ
    exact ⟨fun h => ⟨h.1, hB _ _ h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2.2⟩⟩
