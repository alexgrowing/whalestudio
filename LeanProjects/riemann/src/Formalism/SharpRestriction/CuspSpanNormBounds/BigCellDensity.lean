import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.StatementD
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

noncomputable section

namespace Formalism.MainNotions.BigCellDensity

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DensAt (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (O : Formalism.FourierDecayAlt.C6.OrbData D γ),
    1 ≤ r → 0 < ε → (r : ℝ) * Formalism.FourierDecayAlt.C6.AV CV r (2 * r + k + 1) ≤ A → Formalism.FourierDecayAlt.C6.mmV CV r ≤ mm →
    Formalism.FourierDecayAlt.B.InCC A mm F' →
    (∀ g ∈ Formalism.FourierDecayAlt.B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    (∀ g ∈ Formalism.FourierDecayAlt.C6.bigPos D, Formalism.FourierDecayAlt.B.JF D F' g = 0) →
    Formalism.FourierDecayAlt.C6.IsRelevant D γ → 0 < Gf k r D.z D.z' γ → O.J F' = 0

def StandardBesselSetting : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd →
    IsSection (k0 + 1) r L.z L.z' μsec → L.κN ≠ 0 → L.κN ≠ ⊤ →
    ∃ D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq, D.z = L.z ∧ D.z' = L.z' ∧ D.π = L.π ∧ D.π' = L.π' ∧
      D.μW = L.μW ∧ D.μN = L.μN ∧ D.μW' = L.μW' ∧ D.μsec = μsec

theorem settingTie : StandardBesselSetting := by
  intro k0 r L μsec hc hsec hκ0 hκ1
  obtain ⟨μG, hG⟩ := Formalism.MainNotions.BridgeLemma₅.lb_haarG (k0 + 1) r
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := Formalism.FourierDecayAlt.P.character_exists_alt
  obtain ⟨p1, p2, p3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  obtain ⟨q1, q2, q3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset (k0 + 1) r) L.μN :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1)
  exact ⟨{ z := L.z, z' := L.z', π := L.π, π' := L.π', μG := μG, μW := L.μW, μN := L.μN, μW' := L.μW', μsec := μsec
           χ := χ, k_pos := by omega, z_mem := L.hz.1, z'_mem := L.hz'.1, T_pos := L.hz.2, T'_pos := L.hz'.2
           π_rep := p1, π'_rep := q1, π_unitary := p2, π'_unitary := q2, π_cont := p3, π'_cont := q3, haarG := hG
           haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ L.hz.1 L.hz.2 L.hμW.1, haarN := hN
           haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ L.hz'.1 L.hz'.2 L.hμW'.1
           sec := hsec, χ_smooth := hχ1, χ_supp := hχ2, χ_int := hχ3 }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def CCRight : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (mm : ℕ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E), 0 ≤ A → IsCC k r A mm F → ∀ m ≤ mm,
      Formalism.FourierDecayAlt.B.CkOn (m : ℕ∞) (Formalism.FourierDecayAlt.B.GV k r) F ∧ ∃ c : ℝ, ∀ v : List (Formalism.FourierDecayAlt.B.Mat k r),
        (∀ X ∈ v, Formalism.FourierDecayAlt.B.unitLie k r X) → v.length ≤ m →
          ∀ g ∈ Formalism.FourierDecayAlt.B.GV k r, Formalism.FourierDecayAlt.B.gN g ^ A * ‖Formalism.FourierDecayAlt.B.Rw v F g‖ ≤ c

def BigCellJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (A : ℝ) (mm : ℕ) (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)),
    (r = 0 ∨ 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A) → Formalism.FourierDecayAlt.B.InCC A mm F →
    (∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz k r D.z * Tz k r D.z' < Complex.normSq q.2 →
      Formalism.FourierDecayAlt.B.JF D F (bigCell k r q.1 (D.μsec q.2)) = 0) →
    ∀ g ∈ Formalism.FourierDecayAlt.C6.bigPos D, Formalism.FourierDecayAlt.B.JF D F g = 0

theorem uw_inv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  obtain ⟨hdet, hUinv⟩ := (Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hH).2.2 h hU
  have key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v := by
    intro v hv
    calc Matrix.mulVec h⁻¹ v = Matrix.mulVec h⁻¹ (Matrix.mulVec h v) := by rw [hv]
      _ = Matrix.mulVec (h⁻¹ * h) v := Matrix.mulVec_mulVec _ _ _
      _ = v := by rw [Matrix.nonsing_inv_mul h hdet, Matrix.one_mulVec]
  exact ⟨hUinv, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem psi_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) : psi k r z c 1 = 1 := by
  have h1 := (Formalism.QuantumDeterminants.nSubgroup k r).1
  have hell := Formalism.QuantumDeterminants.ellAdd k r z hz 1 h1 1 h1
  rw [Matrix.mul_one] at hell
  have h0 : ell k r z 1 = 0 := by linear_combination -hell
  simp [psi, h0]

def OrbTie : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.z = L.z → D.z' = L.z' → D.π = L.π → D.π' = L.π' → D.μW = L.μW →
    D.μN = L.μN → D.μW' = L.μW' →
    ∀ (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
        ∃ O : Formalism.FourierDecayAlt.C6.OrbData D g, ∀ F, O.J F = OrbInt L F g ν

def GTie : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    g ∈ UH (Hpk k r) → Zhat k r z z' g = ptMat γ → Gf k r z z' g = ThB.Gpt (Tz k r z) (Tz k r z') γ

theorem gTie : GTie := by
  intro k r z z' γ g _ hZ
  simp only [Gf, Dmin, ThB.Gpt, leadMinor, hZ]

def KappaEdge : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r), L.c = cStd → L.κN = 0 ∨ L.κN = ⊤ →
    ∀ (F : GramWordSpace.GFn L) (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

def KappaTop : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r), L.c = cStd → L.κN = ⊤ →
    ∀ (F : GramWordSpace.GFn L) (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

theorem ucStd : ‖cStd‖ = 2 := by simp [cStd]

theorem muR_ne_zero {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r))
    (h : IsRootMeas L γ g μR) : μR ≠ 0 := by
  intro h0
  have h2 := h.2
  rw [h0, Measure.map_zero] at h2
  have hv : (volume : Measure ((rootPat γ) → ℂ)) Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (NeZero.ne _)
  have hpos : (0 : ℝ) < (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by
    rw [hc, ucStd]
    positivity
  have h3 := congrArg (fun μ : Measure ((rootPat γ) → ℂ) => μ Set.univ) h2
  simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3.symm with h4 | h4
  · rw [ENNReal.ofReal_eq_zero] at h4
    linarith
  · exact hv h4

def LevelOneB (D : D7) (CB : ℝ) : Prop := D.R.rS = 0 → OnePlaceEstimates.PositivityTheoremP D CB

def InPair {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (p : PairSp (k0 + 1) r) : Prop :=
  Matrix.of p.1.1 ∈ UWset (k0 + 1) r L.z ∧ Matrix.of p.1.2 ∈ Nset (k0 + 1) r ∧
    Matrix.of p.2.1 ∈ UWset (k0 + 1) r L.z' ∧ Matrix.of p.2.2 ∈ Nset (k0 + 1) r

theorem det_unit_of_UH {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det :=
  ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1)).2.2 g hg).1

theorem inPair_act_iff {k0 r : ℕ} (L : LocBessel (k0 + 1) r)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (ha : a ∈ RStab (k0 + 1) r g)
    (x : PairSp (k0 + 1) r) : InPair L (stabAct g a x) ↔ InPair L x := by
  have hN := Formalism.QuantumDeterminants.nSubgroup (k0 + 1) r
  have hainv : a⁻¹ ∈ Nset (k0 + 1) r := hN.2.2 a ha.1
  have hbinv : (g⁻¹ * a * g)⁻¹ ∈ Nset (k0 + 1) r := hN.2.2 _ ha.2
  have hda := det_unit_of_UH ha.1.1
  have hdb := det_unit_of_UH ha.2.1
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · have := hN.2.1 _ hainv _ h2
      have e : a⁻¹ * (a * Matrix.of x.1.2) = Matrix.of x.1.2 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
      rw [← e]
      exact this
    · have := hN.2.1 _ hbinv _ h4
      have e : (g⁻¹ * a * g)⁻¹ * (g⁻¹ * a * g * Matrix.of x.2.2) = Matrix.of x.2.2 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdb, Matrix.one_mul]
      rw [← e]
      exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, hN.2.1 _ ha.1 _ h2, h3, hN.2.1 _ ha.2 _ h4⟩

theorem besselIntg_act {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (F : GramWordSpace.GFn L)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (hg : g ∈ UH (Hpk (k0 + 1) r))
    (hrel : IsRelStab L g) (ha : a ∈ RStab (k0 + 1) r g) (x : PairSp (k0 + 1) r) (hx : InPair L x) :
    besselIntg L F g (stabAct g a x) = besselIntg L F g x := by
  have hda := det_unit_of_UH ha.1.1
  have hdg := det_unit_of_UH hg
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have harg : (Matrix.of x.1.1)⁻¹ * (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) * Matrix.of x.2.1 =
      (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 * Matrix.of x.2.1 := by
    have e : (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) = (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 := by
      rw [Matrix.mul_inv_rev]
      calc (Matrix.of x.1.2)⁻¹ * a⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2)
          = (Matrix.of x.1.2)⁻¹ * (a⁻¹ * (g * g⁻¹) * a) * g * Matrix.of x.2.2 := by simp only [Matrix.mul_assoc]
        _ = (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 := by
          rw [Matrix.mul_nonsing_inv g hdg, Matrix.mul_one, Matrix.nonsing_inv_mul a hda, Matrix.mul_one]
    calc _ = (Matrix.of x.1.1)⁻¹ * ((a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2)) * Matrix.of x.2.1 := by
          simp only [Matrix.mul_assoc]
      _ = (Matrix.of x.1.1)⁻¹ * ((Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2) * Matrix.of x.2.1 := by rw [e]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hz := L.hz.1
  have hz' := L.hz'.1
  have hchar : psi (k0 + 1) r L.z L.c (a * Matrix.of x.1.2) *
      star (psi (k0 + 1) r L.z' L.c (g⁻¹ * a * g * Matrix.of x.2.2)) =
      psi (k0 + 1) r L.z L.c (Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of x.2.2)) := by
    rw [(Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).1 _ h2, (Formalism.QuantumDeterminants.psiChar _ _ L.z' L.c hz' _ ha.2).1 _ h4,
      ← hrel a ha, star_mul]
    have hn : star (psi (k0 + 1) r L.z L.c a) * psi (k0 + 1) r L.z L.c a = 1 := by
      have h := (Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).2
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
      simp
    calc _ = (star (psi (k0 + 1) r L.z L.c a) * psi (k0 + 1) r L.z L.c a) *
          (psi (k0 + 1) r L.z L.c (Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of x.2.2))) := by ring
      _ = _ := by rw [hn, one_mul]
  have hs11 : Matrix.of (stabAct g a x).1.1 = Matrix.of x.1.1 := rfl
  have hs12 : Matrix.of (stabAct g a x).1.2 = a * Matrix.of x.1.2 := rfl
  have hs21 : Matrix.of (stabAct g a x).2.1 = Matrix.of x.2.1 := rfl
  have hs22 : Matrix.of (stabAct g a x).2.2 = g⁻¹ * a * g * Matrix.of x.2.2 := rfl
  simp only [besselIntg, hs11, hs12, hs21, hs22, harg, hchar]

theorem pairSp_borel (k r : ℕ) : BorelSpace (PairSp k r) := by
  have : SecondCountableTopology (Mt k r × Mt k r) := inferInstance
  have : SecondCountableTopologyEither (Mt k r × Mt k r) (Mt k r × Mt k r) := inferInstance
  have : BorelSpace (Mt k r × Mt k r) := inferInstance
  exact Prod.borelSpace

attribute [local instance] pairSp_borel

theorem pairSpMt_borel (k r : ℕ) : BorelSpace (PairSp k r × Mt k r) := by
  have : SecondCountableTopology (PairSp k r) := inferInstance
  have : SecondCountableTopologyEither (PairSp k r) (Mt k r) := inferInstance
  exact Prod.borelSpace

attribute [local instance] pairSpMt_borel

theorem cont_act {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (fun q : Mt k r × PairSp k r => stabAct g (Matrix.of q.1) q.2) := by
  unfold stabAct
  fun_prop

theorem meas_act {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun q : PairSp k r × Mt k r => stabAct g (Matrix.of q.2) q.1) := by
  have h := (cont_act g).comp continuous_swap
  exact h.measurable

theorem meas_act' {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : PairSp k r) :
    Measurable (fun a : Mt k r => stabAct g (Matrix.of a) x) :=
  (meas_act g).comp (measurable_const.prodMk measurable_id)

theorem enorm_split (y : ℝ) : ‖y‖ₑ = ENNReal.ofReal y + ENNReal.ofReal (-y) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 y with h | h
  · simp [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h)]
  · simp [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]

theorem weil_real {k r : ℕ} (P : Measure (PairSp k r)) (μR : Measure (Mt k r)) [SFinite μR]
    (ν : Measure (PairSp k r)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ f : PairSp k r → ENNReal, Measurable f →
      ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν)
    (u : PairSp k r → ℝ) (hu : Measurable u) (hi : Integrable u P) :
    (∀ᵐ x ∂ν, Integrable (fun a => u (stabAct g (Matrix.of a) x)) μR) ∧
      Integrable (fun x => ∫ a, u (stabAct g (Matrix.of a) x) ∂μR) ν ∧
      ∫ x, u x ∂P = ∫ x, (∫ a, u (stabAct g (Matrix.of a) x) ∂μR) ∂ν := by
  have hm : ∀ w : PairSp k r → ENNReal, Measurable w →
      Measurable fun x => ∫⁻ a, w (stabAct g (Matrix.of a) x) ∂μR := fun w hw =>
    Measurable.lintegral_prod_right' (hw.comp (meas_act g))
  have hmp : Measurable fun p => ENNReal.ofReal (u p) := ENNReal.measurable_ofReal.comp hu
  have hmm : Measurable fun p => ENNReal.ofReal (-u p) := ENNReal.measurable_ofReal.comp hu.neg
  have eP := hq _ hmp
  have eM := hq _ hmm
  have hle1 : ∀ p, ENNReal.ofReal (u p) ≤ ‖u p‖ₑ := fun p => by rw [enorm_split]; exact le_self_add
  have hle2 : ∀ p, ENNReal.ofReal (-u p) ≤ ‖u p‖ₑ := fun p => by rw [enorm_split]; exact le_add_self
  have hfinP : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≠ ⊤ := ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle1)
  have hfinM : ∫⁻ x, ENNReal.ofReal (-u x) ∂P ≠ ⊤ := ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle2)
  have hApm := hm _ hmp
  have hAmm := hm _ hmm
  have hfinP' := hfinP
  have hfinM' := hfinM
  rw [eP] at hfinP'
  rw [eM] at hfinM'
  have hApfin := ae_lt_top hApm hfinP'
  have hAmfin := ae_lt_top hAmm hfinM'
  have hInt : ∀ᵐ x ∂ν, Integrable (fun a => u (stabAct g (Matrix.of a) x)) μR := by
    filter_upwards [hApfin, hAmfin] with x h1 h2
    refine ⟨(hu.comp (meas_act' g x)).aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖u (stabAct g (Matrix.of a) x)‖ₑ ∂μR < ⊤
    simp_rw [enorm_split]
    have hmeas : Measurable (fun a => ENNReal.ofReal (u (stabAct g (Matrix.of a) x))) := hmp.comp (meas_act' g x)
    rw [lintegral_add_left hmeas]
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  have hinner : ∀ᵐ x ∂ν, ∫ a, u (stabAct g (Matrix.of a) x) ∂μR =
      (∫⁻ a, ENNReal.ofReal (u (stabAct g (Matrix.of a) x)) ∂μR).toReal -
        (∫⁻ a, ENNReal.ofReal (-u (stabAct g (Matrix.of a) x)) ∂μR).toReal := by
    filter_upwards [hInt] with x hx
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx
  have iP := integrable_toReal_of_lintegral_ne_top hApm.aemeasurable hfinP'
  have iM := integrable_toReal_of_lintegral_ne_top hAmm.aemeasurable hfinM'
  refine ⟨hInt, (iP.sub iM).congr (hinner.mono fun x hx => hx.symm), ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, eP, eM, integral_congr_ae hinner,
    integral_sub iP iM, integral_toReal hApm.aemeasurable hApfin, integral_toReal hAmm.aemeasurable hAmfin]

theorem weil_vec {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : Measure (PairSp k r)) (μR : Measure (Mt k r)) [SFinite μR]
    (ν : Measure (PairSp k r)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ f : PairSp k r → ENNReal, Measurable f →
      ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν)
    (h : PairSp k r → E) (hh : StronglyMeasurable h) (hi : Integrable h P) :
    (∀ᵐ x ∂ν, Integrable (fun a => h (stabAct g (Matrix.of a) x)) μR) ∧
      ∫ x, h x ∂P = ∫ x, (∫ a, h (stabAct g (Matrix.of a) x) ∂μR) ∂ν := by
  obtain ⟨hn1, hn2, -⟩ := weil_real P μR ν g hq (fun p => ‖h p‖) hh.norm.measurable hi.norm
  have hInt : ∀ᵐ x ∂ν, Integrable (fun a => h (stabAct g (Matrix.of a) x)) μR := by
    filter_upwards [hn1] with x hx
    exact (integrable_norm_iff ((hh.comp_measurable (meas_act' g x)).aestronglyMeasurable)).1 hx
  refine ⟨hInt, ?_⟩
  have hHm : StronglyMeasurable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR) := by
    have : StronglyMeasurable (Function.uncurry fun x (a : Mt k r) => h (stabAct g (Matrix.of a) x)) :=
      hh.comp_measurable (meas_act g)
    exact this.integral_prod_right'
  have hHi : Integrable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR) ν :=
    Integrable.mono' hn2 hHm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => norm_integral_le_integral_norm _)
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) (sub_ne_zero.2 hne)
  apply hℓ
  rw [map_sub, sub_eq_zero, ← ℓ.integral_comp_comm hi, ← ℓ.integral_comp_comm hHi]
  have hr := (weil_real P μR ν g hq (fun p => ℓ (h p)) (ℓ.continuous.comp_stronglyMeasurable hh).measurable
    (ℓ.integrable_comp hi)).2.2
  rw [hr]
  refine integral_congr_ae ?_
  filter_upwards [hInt] with x hx
  exact ℓ.integral_comp_comm hx

theorem nu_inPair_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ}
    {μR : Measure (Mt (k0 + 1) r)} {ν : Measure (PairSp (k0 + 1) r)}
    (hconc : μR {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μR ≠ 0) (hq : IsOrbQuot L g μR ν) :
    ∀ᵐ x ∂ν, InPair L x := by
  have hW := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z).closed
  have hW' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z').closed
  have hNc := (Formalism.FourierDecayAlt.P.unipotent_radical_closed (k0 + 1) r).closed
  have hcl : IsClosed {p : PairSp (k0 + 1) r | InPair L p} := by
    have := ((hW.preimage (continuous_fst.comp continuous_fst)).inter
      (hNc.preimage (continuous_snd.comp continuous_fst))).inter
      ((hW'.preimage (continuous_fst.comp continuous_snd)).inter (hNc.preimage (continuous_snd.comp continuous_snd)))
    have hset : {p : PairSp (k0 + 1) r | InPair L p} =
        (Prod.fst ∘ Prod.fst ⁻¹' UWset (k0 + 1) r L.z ∩ Prod.snd ∘ Prod.fst ⁻¹' Nset (k0 + 1) r ∩
          (Prod.fst ∘ Prod.snd ⁻¹' UWset (k0 + 1) r L.z' ∩ Prod.snd ∘ Prod.snd ⁻¹' Nset (k0 + 1) r)) := by
      ext p
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨a, b⟩, c, d⟩
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨a, b, c, d⟩
    rw [hset]
    exact this
  have hS : MeasurableSet {p : PairSp (k0 + 1) r | ¬ InPair L p} := hcl.measurableSet.compl
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0 := L.hμW.1.2.2.1
  have n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0 := hNH.2.2.1
  have n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0 := L.hμW'.1.2.2.1
  have hP0 : pairMeas L {p | ¬ InPair L p} = 0 := by
    have hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆
        ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪
        ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪
          (Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}))) := by
      intro p hp
      simp only [Set.mem_setOf_eq, InPair, not_and_or] at hp
      rcases hp with h | h | h | h <;> simp [h]
    refine measure_mono_null hsub ?_
    simp only [pairMeas]
    refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
      rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]
  have h := hq ({p | ¬ InPair L p}.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS, hP0] at h
  have hμR : μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hne
  have hae_a : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g := by
    rw [ae_iff]
    simpa using hconc
  have hlow : ∀ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ≤
      ∫⁻ a, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator 1 (stabAct g (Matrix.of a) x) ∂μR := by
    intro x
    by_cases hx : x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p}
    · rw [Set.indicator_of_mem hx]
      calc μR Set.univ = ∫⁻ _a, (1 : ENNReal) ∂μR := by simp
        _ ≤ _ := lintegral_mono_ae (hae_a.mono fun a ha => by
              have hm : stabAct g (Matrix.of a) x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p} :=
                fun hin => hx ((inPair_act_iff L ha x).1 hin)
              simp [Set.indicator_of_mem hm])
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have h2 : ∫⁻ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ∂ν = 0 :=
    le_antisymm ((lintegral_mono hlow).trans h.symm.le) zero_le
  rw [lintegral_indicator_const hS] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hμR
  · exact ae_iff.2 h3

theorem weil_L_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ}
    {μR : Measure (Mt (k0 + 1) r)} [SFinite μR] {ν : Measure (PairSp (k0 + 1) r)}
    (hg : g ∈ UH (Hpk (k0 + 1) r)) (hrel : IsRelStab L g)
    (hconc : μR {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μR ≠ 0) (hq : IsOrbQuot L g μR ν)
    (F : GramWordSpace.GFn L) (θ : PairSp (k0 + 1) r → ℝ)
    (hθ1 : ∀ p, InPair L p → ∫ x, θ (stabAct g (Matrix.of x) p) ∂μR = 1)
    (hint : Integrable (fun p => θ p • besselIntg L F g p) (pairMeas L)) :
    ∫ p, θ p • besselIntg L F g p ∂(pairMeas L) = OrbInt L F g ν := by
  have : CompleteSpace L.Wp := FiniteDimensional.complete ℂ L.Wp
  set f := fun p => θ p • besselIntg L F g p with hfdef
  set h := hint.aestronglyMeasurable.mk f with hhdef
  have hh : StronglyMeasurable h := hint.aestronglyMeasurable.stronglyMeasurable_mk
  have hfh : f =ᵐ[pairMeas L] h := hint.aestronglyMeasurable.ae_eq_mk
  have hhi : Integrable h (pairMeas L) := hint.congr hfh
  obtain ⟨-, hW⟩ := weil_vec (pairMeas L) μR ν g hq h hh hhi
  set N1 := toMeasurable (pairMeas L) {p | f p ≠ h p} with hN1def
  have hN1m : MeasurableSet N1 := measurableSet_toMeasurable _ _
  have hN1 : pairMeas L N1 = 0 := by
    rw [measure_toMeasurable]
    exact hfh
  have hq1 := hq (N1.indicator 1) (measurable_one.indicator hN1m)
  rw [lintegral_indicator_one hN1m, hN1] at hq1
  have hmeasI : Measurable (fun x => ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR) :=
    Measurable.lintegral_prod_right' ((measurable_one.indicator hN1m).comp (meas_act g))
  have hae1 : ∀ᵐ x ∂ν, ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR = 0 :=
    (lintegral_eq_zero_iff hmeasI).1 hq1.symm
  have hνS := nu_inPair_gen L hκ0 hκ1 hconc hne hq
  have hroot_ae : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g := by
    rw [ae_iff]
    simpa using hconc
  have key : ∀ᵐ x ∂ν, ∫ a, h (stabAct g (Matrix.of a) x) ∂μR = besselIntg L F g x := by
    filter_upwards [hae1, hνS] with x hx1 hx2
    have hnot : ∀ᵐ a ∂μR, stabAct g (Matrix.of a) x ∉ N1 := by
      have h0 := (lintegral_eq_zero_iff ((measurable_one.indicator hN1m).comp (meas_act' g x))).1 hx1
      filter_upwards [h0] with a ha hmem
      simp [Function.comp, Set.indicator_of_mem hmem] at ha
    have heq : ∀ᵐ a ∂μR, h (stabAct g (Matrix.of a) x) = θ (stabAct g (Matrix.of a) x) • besselIntg L F g x := by
      filter_upwards [hnot, hroot_ae] with a ha1 ha2
      have hfh' : f (stabAct g (Matrix.of a) x) = h (stabAct g (Matrix.of a) x) := by
        by_contra hne
        exact ha1 (subset_toMeasurable _ _ hne)
      rw [← hfh', hfdef]
      simp only
      rw [besselIntg_act L hc F hg hrel ha2 x hx2]
    rw [integral_congr_ae heq, integral_smul_const, hθ1 x hx2, one_smul]
  rw [integral_congr_ae hfh, hW]
  exact integral_congr_ae key

theorem integrand_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (hc : L.c = cStd) (hz : D.z = L.z) (hz' : D.z' = L.z') (hπ : D.π = L.π) (hπ' : D.π' = L.π') (F : GramWordSpace.GFn L)
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (p : PairSp (k0 + 1) r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) p • Formalism.FourierDecayAlt.B.rho D p F g = besselIntg L F g p := by
  have hxi : Formalism.FourierDecayAlt.B.xiTau D (1, 1) p =
      psi (k0 + 1) r L.z L.c (Matrix.of p.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of p.2.2)) := by
    simp only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, hz, hz', hc, one_mul]
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [besselIntg, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hxi, hπ, hπ']

def RootHaar : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r)),
    L.c = cStd → 0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset g) μR

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def CellRepl : Prop :=
  ∀ (D : D7) (k0 : ℕ), k0 + 1 = D.R.k → ∀ (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ, ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∃ F' : GramWordSpace.GFn L,
          (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - dP - 3 * ((D.R.rS : ℝ) + 1) * ((mm : ℝ) + o)) mm F') ∧
          SuppGe (GramWordSpace.levOf L μsec) ε F' ∧
          (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
            Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
            L.J F' (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ (g : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ)
            (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
            0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
            IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
              OrbInt L (Θ F) g ν = OrbInt L F' g ν

def LevelOneA (D : D7) (CB : ℝ) : Prop := D.R.rS = 0 → OnePlaceEstimates.FrameIntegrationFormula D CB

def TieForms : Prop :=
  ∃ C₀ : ℝ, ∀ (D : D7) (k0 : ℕ) (X : GramWordSpace.Dat D k0) (CB : ℝ), C₀ ≤ CB → OnePlaceEstimates.StdShort X CB →
    (∀ v, (X.B v).κN ≠ 0 ∧ (X.B v).κN ≠ ⊤) → ∀ v : D.what₂.Tau,
    ∃ (T : Formalism.FourierDecayAlt.D.LevTower (k0 + 1) D.R.rS (X.B v).Wp (X.B v).Wq) (ω : ∀ j : ℕ, Point ℂ j → ℝ),
      Formalism.FourierDecayAlt.D.TowerNormalised T ∧ T.base.z = (X.B v).z ∧ T.base.z' = (X.B v).z' ∧ T.base.π = (X.B v).π ∧
      T.base.π' = (X.B v).π' ∧ T.base.μsec = X.μsec v ∧ (∀ j p, 0 < ω j p) ∧
      ∀ (χ : ℝ → ℝ), IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), w.length ≤ OnePlaceEstimates.NS D → ∀ (p p' : Point ℂ j),
        X.gramLow v j hj w (X.Fv χ ε v) p p' =
          ((ω j p * ω j p' : ℝ) : ℂ) * Formalism.FourierDecayAlt.D.RRplace T ((X.sg v : ℝ) : ℂ) (fun _ => 0) 1 (fun _ _ _ _ => 0)
            (X.Fv χ ε v) j w (p.1.map Prod.swap) (p'.1.map Prod.swap)

def FirstAdmissibilityFiniteKappa (D : D7) (CV : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ,
        (D.R.rS : ℝ) * (CV * ((D.R.rS : ℝ) ^ 3 * D.R.r + (D.R.r : ℝ) ^ 2 + (D.R.rS : ℝ) ^ 4)) ≤
          A - dP - 3 * ((D.R.rS : ℝ) + 1) * (CV * ((D.R.rS : ℝ) ^ 2 + 1) + o) →
        CV * ((D.R.rS : ℝ) + 1) ^ 2 * ((o : ℝ) + (D.R.rS : ℝ) * D.R.r + 1) ≤ A - 3 * ((D.R.rS : ℝ) + 1) * o →
        ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
          SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∀ (g : ThB.Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
          0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
          IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L (Θ F) g ν = 0

def SecondAdmissibilityFiniteKappa (D : D7) (CB : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (A : ℝ) (mm : ℕ), Big CB (GramWordSpace.levOf L μsec) 0 A mm →
    ∀ F : GramWordSpace.GFn L, IsCC (k0 + 1) D.R.rS A mm F → ∀ ε : ℝ, 0 < ε → SuppGe (GramWordSpace.levOf L μsec) ε F →
      (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
        Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
        L.J F (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) →
      ∀ (γ : Point ℂ (D.R.rS + 1)) (g : ThB.Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS))
        (ν : Measure (PairSp (k0 + 1) D.R.rS)),
        0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
        IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

def c3 : ℝ := Classical.choose Formalism.FourierDecayAlt.P.orbital_integral_converges

def A0 (k r : ℕ) : ℝ := c3 * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)

def TopLevelBesselStatement : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
    ∃ c : List ℕ → ℝ, (∀ s, 0 < c s) ∧
      ∀ (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
        0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        ThB.orbSq L F γ = ENNReal.ofReal (c (γ.1.map Prod.snd) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

theorem ptEntry_swap (l : List (ℂ × ℕ)) (a b : ℕ) :
    Formalism.FourierDecayAlt.D.ptEntry (l.map Prod.swap) a b = ptEntry l a b := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.D.ptEntry, ptEntry, ih]

theorem ptMatN_swap {r : ℕ} (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) = ptMat γ := by
  ext a b
  simp [Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]

theorem isLocPt_swap {r : ℕ} (γ : Point ℂ (r + 1)) : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := by
  obtain ⟨l, hl, hs⟩ := γ
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact ⟨(hl x hx).2, (hl x hx).1⟩
  · simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_map]
    have e : (Prod.fst ∘ Prod.swap : ℂ × ℕ → ℕ) = Prod.snd := rfl
    rw [e]
    exact hs

theorem ptG_eq_GPoint {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptG (T * T') r (γ.1.map Prod.swap) = ThB.Gpt T T' γ := by
  unfold Formalism.FourierDecayAlt.D.ptG ThB.Gpt leadMinor
  rw [ptMatN_swap]
  congr 3
  congr 1
  ext a b
  simp [Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]

def bI : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: ss, p => if p < s then 0 else 1 + bI ss (p - s)

theorem blockIdx_eq (l : List (ℂ × ℕ)) (p : ℕ) : blockIdx l p = bI (l.map Prod.snd) p := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [blockIdx, bI, List.map_cons, ih]

def pc (r : ℕ) (s : List ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (r + 1) × Fin (r + 1))).filter fun q => q.1 < q.2 ∧ bI s q.1.val = bI s q.2.val).card

theorem card_rootPat {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ).card = pc r (γ.1.map Prod.snd) := by
  unfold rootPat pc
  simp only [blockIdx_eq]

theorem hsInner_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsInner A B = Formalism.FourierDecayAlt.B.hsInner A B := by
  simp [hsInner, Formalism.FourierDecayAlt.B.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]

theorem hsNormSq_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℝ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = t ^ 2 * hsNormSq A := by
  rw [show t • A = (t : ℂ) • A from (Complex.coe_smul t A).symm]
  simp only [hsNormSq, hsInner, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, ← Finset.mul_sum]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem isOrbQuot_rescale {k r : ℕ} (L : LocBessel k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μ : Measure (Mt k r)} {ν : Measure (PairSp k r)} (a : ENNReal) (ha1 : a ≠ ⊤)
    (h : IsOrbQuot L g (a • μ) ν) : IsOrbQuot L g μ (a • ν) := by
  intro f hf
  rw [h f hf, lintegral_smul_measure]
  simp_rw [lintegral_smul_measure]
  exact lintegral_const_mul' a _ ha1

theorem orbJ_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (hc : L.c = cStd) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤) (hz : Ds.z = L.z) (hz' : Ds.z' = L.z')
    (hπ : Ds.π = L.π) (hπ' : Ds.π' = L.π') (hW : Ds.μW = L.μW) (hN : Ds.μN = L.μN) (hW' : Ds.μW' = L.μW')
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (hg : g ∈ UH (Hpk (k0 + 1) r))
    (hrel : IsRelStab L g) {μ : Measure (Mt (k0 + 1) r)} [SFinite μ]
    (hconc : μ {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μ ≠ 0) {ν : Measure (PairSp (k0 + 1) r)}
    (hq : IsOrbQuot L g μ ν) (F : GramWordSpace.GFn L)
    (hcut : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p) Ds.μSS) :
    Formalism.FourierDecayAlt.D.orbJ Ds g μ F = OrbInt L F g ν := by
  unfold Formalism.FourierDecayAlt.D.orbJ
  rw [dif_pos hcut]
  obtain ⟨⟨_, _, hθ1⟩, hint⟩ := hcut.choose_spec
  generalize hcut.choose = θ at hθ1 hint ⊢
  have hμS : Ds.μSS = pairMeas L := by
    simp only [Formalism.FourierDecayAlt.B.RealPlaceData.μSS, pairMeas, hW, hN, hW']
  have hI : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p) =
      fun p => θ p • besselIntg L F g p := by
    funext p
    rw [show Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p = Formalism.FourierDecayAlt.B.xiTau Ds (1, 1) p • Formalism.FourierDecayAlt.B.rho Ds p F g from rfl,
      integrand_eq L Ds hc hz hz' hπ hπ' F g p]
  rw [hI, hμS] at hint ⊢
  refine weil_L_gen L hc hκ0 hκ1 hg hrel hconc hne hq F _ (fun p hp => hθ1 p ?_) hint
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.inSS
  rw [hz, hz']
  exact hp

theorem orbSq_eq_of {k r : ℕ} (L : LocBessel k r) (F : ThB.Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) (v : ℝ)
    (hall : ∀ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν →
      hsNormSq (OrbInt L F g ν) = v)
    (hex : ∃ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν) :
    ThB.orbSq L F γ = ENNReal.ofReal v := by
  unfold ThB.orbSq
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    rw [hall g μR ν h]
  · obtain ⟨g, μR, ν, h⟩ := hex
    refine le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le h ?_)))
    rw [hall g μR ν h]

def RootMeasOfMuR : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (γ : Point ℂ (r + 1))
    (g : ThB.Mx (k0 + 1) r) (hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1)),
    L.c = cStd → Ds.z = L.z → Ds.z' = L.z' → g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r →
    Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) →
    IsRootMeas L γ g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) •
      Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)))

def QuotExists : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1)) (g : ThB.Mx (k0 + 1) r) (μR : Measure (Mt (k0 + 1) r)),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
    ∃ ν : Measure (PairSp (k0 + 1) r), IsOrbQuot L g μR ν

def CutKFin : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (γ : Point ℂ (r + 1))
    (g : ThB.Mx (k0 + 1) r) (hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1))
    (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)),
    L.c = cStd → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' → Ds.μW = L.μW → Ds.μN = L.μN →
    Ds.μW' = L.μW' → IsKFinCoefH L.σ F → Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
    0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
    g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r → Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) →
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F q) Ds.μSS

def RepIndep : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' → Ds.μW = L.μW →
    Ds.μN = L.μN → Ds.μW' = L.μW' → IsKFinCoefH L.σ F →
    Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
    0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
    ∀ (g₁ : ThB.Mx (k0 + 1) r) (μ₁ : Measure (Mt (k0 + 1) r)) (ν₁ : Measure (PairSp (k0 + 1) r))
      (g₂ : ThB.Mx (k0 + 1) r) (μ₂ : Measure (Mt (k0 + 1) r)) (ν₂ : Measure (PairSp (k0 + 1) r)),
      (IsPtRep L γ g₁ ∧ IsRelStab L g₁ ∧ IsRootMeas L γ g₁ μ₁ ∧ IsOrbQuot L g₁ μ₁ ν₁) →
      (IsPtRep L γ g₂ ∧ IsRelStab L g₂ ∧ IsRootMeas L γ g₂ μ₂ ∧ IsOrbQuot L g₂ μ₂ ν₂) →
      hsNormSq (OrbInt L F g₁ ν₁) = hsNormSq (OrbInt L F g₂ ν₂)

def bD : List (ℕ × ℂ) → ℕ → ℕ
  | [], _ => 0
  | (s, _) :: rest, p => if p < s then 0 else 1 + bD rest (p - s)

def GoodL (l : List (ℕ × ℂ)) : Prop := ∀ b ∈ l, 1 ≤ b.1 ∧ b.2 ≠ 0

theorem goodL_tail {x : ℕ × ℂ} {l : List (ℕ × ℂ)} (h : GoodL (x :: l)) : GoodL l :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem partner_partner (l : List (ℕ × ℂ)) (a : ℕ) (ha : a < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptPartner l (Formalism.FourierDecayAlt.D.ptPartner l a) = a := by
  induction l generalizing a with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at ha
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at ha
    simp only [Formalism.FourierDecayAlt.D.ptPartner]
    by_cases h : a < s
    · simp only [if_pos h]
      rw [if_pos (show s - 1 - a < s by omega)]
      omega
    · simp only [if_neg h]
      rw [if_neg (show ¬ (s + Formalism.FourierDecayAlt.D.ptPartner l (a - s) < s) by omega), Nat.add_sub_cancel_left,
        ih (a - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]
      omega

theorem partner_order (l : List (ℕ × ℂ)) (hl : GoodL l) (a b : ℕ) (hab : a < b)
    (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    (bD l a = bD l b ↔ Formalism.FourierDecayAlt.D.ptPartner l b < Formalism.FourierDecayAlt.D.ptPartner l a) := by
  induction l generalizing a b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    have hs := (hl (s, t) (List.mem_cons_self)).1
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [bD, Formalism.FourierDecayAlt.D.ptPartner]
    by_cases hbs : b < s
    · have has : a < s := by omega
      simp only [if_pos hbs, if_pos has]
      constructor
      · intro _; omega
      · intro _; trivial
    · by_cases has : a < s
      · simp only [if_pos has, if_neg hbs]
        constructor
        · intro h; omega
        · intro h; omega
      · simp only [if_neg has, if_neg hbs]
        have := ih (goodL_tail hl) (a - s) (b - s) (by omega) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)
        constructor
        · intro h
          have h' : bD l (a - s) = bD l (b - s) := by omega
          have := this.1 h'
          omega
        · intro h
          have h' : Formalism.FourierDecayAlt.D.ptPartner l (b - s) < Formalism.FourierDecayAlt.D.ptPartner l (a - s) := by omega
          have := this.2 h'
          omega

theorem ptEntry_partner (l : List (ℕ × ℂ)) (a b : ℕ) (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptEntry l a b = if a = Formalism.FourierDecayAlt.D.ptPartner l b then Formalism.FourierDecayAlt.D.ptScal l b else 0 := by
  induction l generalizing a b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [Formalism.FourierDecayAlt.D.ptEntry, Formalism.FourierDecayAlt.D.ptPartner, Formalism.FourierDecayAlt.D.ptScal]
    by_cases hbs : b < s
    · simp only [if_pos hbs]
      by_cases has : a < s
      · rw [if_pos ⟨has, hbs⟩]
        by_cases e : a + b + 1 = s
        · rw [if_pos e, if_pos (show a = s - 1 - b by omega)]
        · rw [if_neg e, if_neg (show ¬ a = s - 1 - b by omega)]
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega),
          if_neg (show ¬ a = s - 1 - b by omega)]
    · simp only [if_neg hbs]
      by_cases has : a < s
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega),
          if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_pos (show s ≤ a ∧ s ≤ b by omega),
          ih (a - s) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]
        by_cases e : a - s = Formalism.FourierDecayAlt.D.ptPartner l (b - s)
        · rw [if_pos e, if_pos (show a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]
        · rw [if_neg e, if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]

theorem ptScal_ne (l : List (ℕ × ℂ)) (hl : GoodL l) (b : ℕ) (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptScal l b ≠ 0 := by
  induction l generalizing b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [Formalism.FourierDecayAlt.D.ptScal]
    split_ifs with h
    · exact (hl (s, t) List.mem_cons_self).2
    · exact ih (goodL_tail hl) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)

theorem blockIdx_bD (l : List (ℂ × ℕ)) (p : ℕ) : blockIdx l p = bD (l.map Prod.swap) p := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [blockIdx, bD, List.map_cons, Prod.swap_prod_mk, ih]

theorem cast_perm_val {n m : ℕ} (h : n = m) (e : Equiv.Perm (Fin n)) (x : Fin m) :
    ((h ▸ e) x).val = (e ⟨x.val, h ▸ x.isLt⟩).val := by
  subst h
  rfl

theorem goodL_swap {r : ℕ} (γ : Point ℂ (r + 1)) : GoodL (γ.1.map Prod.swap) := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  exact ⟨(γ.2.1 x hx).2, (γ.2.1 x hx).1⟩

def wPt {r : ℕ} (γ : Point ℂ (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  (isLocPt_swap γ).2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)

def dPt {r : ℕ} (γ : Point ℂ (r + 1)) : Fin (r + 1) → ℂ := fun a => Formalism.FourierDecayAlt.D.ptScal (γ.1.map Prod.swap) a.val

theorem wPt_val {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) :
    (wPt γ x).val = Formalism.FourierDecayAlt.D.ptPartner (γ.1.map Prod.swap) x.val := by
  unfold wPt
  rw [cast_perm_val]
  exact (Formalism.FourierDecayAlt.P.ptPerm_spec _ (r + 1) (isLocPt_swap γ)).1 _

theorem wPt_invol {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) : wPt γ (wPt γ x) = x := by
  apply Fin.ext
  rw [wPt_val, wPt_val]
  exact partner_partner _ _ (by rw [(isLocPt_swap γ).2]; exact x.isLt)

theorem wPt_symm {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) : (wPt γ).symm x = wPt γ x :=
  (wPt γ).symm_apply_eq.mpr (wPt_invol γ x).symm

theorem dPt_ne {r : ℕ} (γ : Point ℂ (r + 1)) (a : Fin (r + 1)) : dPt γ a ≠ 0 :=
  ptScal_ne _ (goodL_swap γ) _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)

theorem ptMatN_mono {r : ℕ} (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
  ext i a
  simp only [Formalism.FourierDecayAlt.D.ptMatN, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
  rw [ptEntry_partner _ _ _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)]
  have : (i = wPt γ a) ↔ (i.val = Formalism.FourierDecayAlt.D.ptPartner (γ.1.map Prod.swap) a.val) := by
    rw [Fin.ext_iff, wPt_val]
  by_cases h : i = wPt γ a
  · rw [if_pos (this.1 h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (this.2 h')), if_neg h]

theorem root_iff {r : ℕ} (γ : Point ℂ (r + 1)) (a b : Fin (r + 1)) (hab : a < b) :
    blockIdx γ.1 a.val = blockIdx γ.1 b.val ↔ (wPt γ).symm b < (wPt γ).symm a := by
  rw [blockIdx_bD, blockIdx_bD, wPt_symm, wPt_symm, Fin.lt_def, wPt_val, wPt_val]
  exact partner_order _ (goodL_swap γ) a.val b.val hab (by rw [(isLocPt_swap γ).2]; exact b.isLt)

def eRoot {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ) ≃ Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) where
  toFun p := ⟨(p.1.2, p.1.1), by
    have hp := p.2
    simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨hp.1, (root_iff γ _ _ hp.1).1 hp.2⟩⟩
  invFun q := ⟨(q.1.2, q.1.1), by
    simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q.2.1, (root_iff γ _ _ q.2.1).2 q.2.2⟩⟩
  left_inv p := by rfl
  right_inv q := by rfl

theorem hpk_esI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  unfold herm bvec
  simp only [dotProduct, Pi.star_apply, Pi.single_apply, apply_ite star, star_one, star_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, hpk_esI, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem flag_eq_uMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin (r + 1)) (ha : a.val < r) : flagMat k r z ρ a b = Formalism.FourierDecayAlt.C2.uMap k r z ρ a b := by
  unfold flagMat Formalism.FourierDecayAlt.C2.uMap
  rw [dif_pos ha, dif_pos ha, herm_esI]

def Tmap {r : ℕ} (γ : Point ℂ (r + 1)) (x : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ) : (rootPat γ) → ℂ :=
  fun p => (starRingEnd ℂ) (x (eRoot γ p))

def Tinv {r : ℕ} (γ : Point ℂ (r + 1)) (y : (rootPat γ) → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ :=
  fun q => (starRingEnd ℂ) (y ((eRoot γ).symm q))

theorem Tinv_Tmap {r : ℕ} (γ : Point ℂ (r + 1)) (x : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ) : Tinv γ (Tmap γ x) = x := by
  funext q
  simp [Tinv, Tmap]

theorem Tmap_mp {r : ℕ} (γ : Point ℂ (r + 1)) : MeasurePreserving (Tmap γ) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : (rootPat γ) => ℂ) (eRoot γ).symm
  have h2 : MeasurePreserving (fun (y : (rootPat γ) → ℂ) (p : rootPat γ) => (Complex.conjLIE : ℂ → ℂ) (y p)) volume volume :=
    volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have h3 := h2.comp h1
  convert h3 using 1
  funext x p
  simp [Tmap, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem Tinv_mp {r : ℕ} (γ : Point ℂ (r + 1)) : MeasurePreserving (Tinv γ) volume volume := by
  have hT := Tmap_mp γ
  have hmT : Measurable (Tinv γ) := by
    unfold Tinv
    fun_prop
  refine ⟨hmT, ?_⟩
  rw [← hT.map_eq, Measure.map_map hmT hT.measurable]
  have : Tinv γ ∘ Tmap γ = id := funext (Tinv_Tmap γ)
  rw [this, Measure.map_id]

theorem good_of {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {γ : Formalism.FourierDecayAlt.B.Mat k r}
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hγ : γ ∈ Formalism.FourierDecayAlt.B.GV k r) (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r D.z D.z' γ = Formalism.FourierDecayAlt.C2.monoP w d) : Formalism.FourierDecayAlt.P.Dx2.Rad.Good D γ w d := by
  by_cases hB : w (Fin.last r) = Fin.last r
  · exact ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.ex_degen D hγ hd hZ hB, Formalism.FourierDecayAlt.P.Dx2.Rad.inj_degen D hγ hd hZ hB,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.lst_gen D hγ hd hZ hρ⟩
  · have hpos := Formalism.FourierDecayAlt.P.Dx2.Rad.pos_of_w D hd hZ hB
    exact ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho D hγ hpos hd hZ, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj D hγ hpos hd hZ,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩

theorem isHaarOn_smul {k r : ℕ} {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ)
    {c : ENNReal} (h0 : c ≠ 0) (h1 : c ≠ ⊤) : Formalism.FourierDecayAlt.B.IsHaarOn U (c • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h'
    apply h.ne_zero
    rw [← Measure.measure_univ_eq_zero]
    have := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h'
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left h0

theorem meas_rootCoords {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z γ) := by
  refine Continuous.measurable (continuous_pi fun p => ?_)
  unfold rootCoords flagMat
  split_ifs <;> first | exact continuous_const | fun_prop

section root
variable {k0 r : ℕ} (L : LocBessel (k0 + 1) r) {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp' Wq')
  (hz : Ds.z = L.z) (γ : Point ℂ (r + 1)) {g : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r)
  (hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ))
include hz hg hZ

theorem rootCoords_psi (y : (rootPat γ) → ℂ) :
    rootCoords (k0 + 1) r L.z γ (Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) = y := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hs := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG (Tinv γ y)).2
  funext p
  have hp := p.2
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have ha : p.1.1.val < r := by
    have h1 := p.1.2.isLt
    have h2 := Fin.lt_def.1 hp.1
    omega
  simp only [rootCoords, Equiv.apply_symm_apply]
  rw [flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]
  have hc := Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)
  simp only [eRoot, Equiv.coe_fn_mk] at hc
  rw [hc]
  simp [Tinv, eRoot]

theorem psi_rootCoords (x : Mt (k0 + 1) r) (hx : Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g) :
    Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r L.z γ x))) = x := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hu := Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg (dPt_ne γ) hG (ρ := Matrix.of x) hx
  have hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) =
      Tinv γ (rootCoords (k0 + 1) r L.z γ x) := by
    funext q
    have hb : q.1.2.val < r := by
      have h1 := q.1.1.isLt
      have h2 := Fin.lt_def.1 q.2.1
      omega
    simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]
    rw [flag_eq_uMap _ _ _ _ _ _ hb, hz]
  have hρ := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg (dPt_ne γ) hG (Tinv γ (rootCoords (k0 + 1) r L.z γ x)) hx
    (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])
  rw [← hρ]
  rfl

theorem muR_map_root :
    (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)).map (rootCoords (k0 + 1) r L.z γ) = volume := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _
  rw [Measure.map_map (meas_rootCoords _ γ) hm]
  have e : (rootCoords (k0 + 1) r L.z γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ := by
    funext x
    have := rootCoords_psi L Ds hz γ hg hZ (Tmap γ x)
    rw [Tinv_Tmap] at this
    exact this
  rw [e]
  exact (Tmap_mp γ).map_eq

theorem muR_conc : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  have hcl : IsClosed {x : Mt (k0 + 1) r | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g} :=
    (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.Rad.isUnit_G hg)).closed
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) _ = 0
  rw [show {x : Mt (k0 + 1) r | Matrix.of x ∉ RStab (k0 + 1) r g} = {x | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g}ᶜ from rfl,
    Measure.map_apply hm hcl.measurableSet.compl]
  convert measure_empty (μ := (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ)))
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Equiv.apply_symm_apply, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG x).1

theorem rootMeas_unique (hc : L.c = cStd) (μ : Measure (Mt (k0 + 1) r)) (hμ : IsRootMeas L γ g μ) :
    μ = ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  have hψ : Measurable fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y)) :=
    hm.comp (Tinv_mp γ).measurable
  have hae : ∀ᵐ x ∂μ, Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r L.z γ x))) = x := by
    have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ RStab (k0 + 1) r g := by
      rw [ae_iff]
      simpa using hμ.1
    filter_upwards [h1] with x hx using psi_rootCoords L Ds hz γ hg hZ x hx
  have hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card := by
    rw [hc, ucStd]
    congr 1
    field_simp
  calc μ = μ.map id := Measure.map_id.symm
    _ = μ.map ((fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) ∘ rootCoords (k0 + 1) r L.z γ) :=
        Measure.map_congr (hae.mono fun x hx => hx.symm)
    _ = (μ.map (rootCoords (k0 + 1) r L.z γ)).map (fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) :=
        (Measure.map_map hψ (meas_rootCoords _ γ)).symm
    _ = ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) := by
        rw [hμ.2, hcst, Measure.map_smul]
        congr 1
        show _ = volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)
        rw [← (Tinv_mp γ).map_eq, Measure.map_map hm (Tinv_mp γ).measurable]
        rfl

end root

theorem root_measure_of_mu_R : RootMeasOfMuR := by
  intro k0 r L Ds γ g hp hc hz hz' hg hZ'
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
    rw [hZ', ptMatN_mono]
  show IsRootMeas L γ g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ))
  have hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card := by
    rw [hc, ucStd]
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  · rw [Measure.smul_apply, muR_conc L Ds hz γ hg hZ, smul_zero]
  · rw [Measure.map_smul, muR_map_root L Ds hz γ hg hZ, hcst]

theorem pair_inPair {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤) :
    ∀ᵐ p ∂(pairMeas L), InPair L p := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0 := L.hμW.1.2.2.1
  have n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0 := hNH.2.2.1
  have n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0 := L.hμW'.1.2.2.1
  rw [ae_iff]
  have hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆
      ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪
        ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪
      ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪
        (Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}))) := by
    intro p hp
    simp only [Set.mem_setOf_eq, InPair, not_and_or] at hp
    rcases hp with h | h | h | h <;> simp [h]
  refine measure_mono_null hsub ?_
  simp only [pairMeas]
  refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
    rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]

theorem mp_stab {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (ha : a ∈ RStab (k0 + 1) r g) :
    MeasurePreserving (stabAct g a) (pairMeas L) (pairMeas L) := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have hl : ∀ b ∈ Nset (k0 + 1) r, MeasurePreserving (lmulM (k := k0 + 1) (r := r) b) L.μN L.μN := fun b hb =>
    ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.contL b |>.measurable, hNH.2.2.2 b hb⟩
  have e : stabAct g a =
      Prod.map (Prod.map id (lmulM (k := k0 + 1) (r := r) a)) (Prod.map id (lmulM (k := k0 + 1) (r := r) (g⁻¹ * a * g))) := by
    funext p
    rfl
  rw [e]
  unfold pairMeas
  exact ((MeasurePreserving.id _).prod (hl a ha.1)).prod ((MeasurePreserving.id _).prod (hl _ ha.2))

theorem rootHaar_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r))
    (hc : L.c = cStd) (hrep : IsPtRep L γ g) (hroot : IsRootMeas L γ g μR) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset g) μR ∧
      ∀ M : ℝ, 2 * ((r : ℝ) + 1) ^ 2 < M → Integrable (fun x : Mt (k0 + 1) r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-M)) μR := by
  obtain ⟨p1, p2, p3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  obtain ⟨q1, q2, q3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  obtain ⟨Ds, hz, hz', -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists (k0 + 1) r L.Wp L.Wq L.z L.z' L.π L.π' (by omega)
    L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 p1 q1 p2 q2 p3 q3
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
    rw [hz, hz', hrep.2, ← ptMatN_swap, ptMatN_mono]
  have hG := good_of Ds hrep.1 (dPt_ne γ) hZ
  rw [rootMeas_unique L Ds hz γ hrep.1 hZ hc μR hroot]
  refine ⟨isHaarOn_smul (Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Ds hrep.1 (dPt_ne γ) hG)
    (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top, fun M hM => ?_⟩
  exact (Formalism.FourierDecayAlt.P.Dx3.intR Ds hrep.1 (dPt_ne γ) hG hM).smul_measure ENNReal.ofReal_ne_top

set_option maxHeartbeats 1000000 in
theorem quotient_exists : QuotExists := by
  intro k0 r L γ g μR hc hκ0 hκ1 hrep hrel hroot
  obtain ⟨hH, hI⟩ := rootHaar_gen L γ g μR hc hrep hroot
  have : SigmaFinite μR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SigmaFinite L.μN := (Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1).1
  have hgu : IsUnit g.det := det_unit_of_UH hrep.1
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  set M : ℝ := 2 * ((r : ℝ) + 1) ^ 2 + 1 with hMdef
  have hM : 2 * ((r : ℝ) + 1) ^ 2 < M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  set θ := Formalism.FourierDecayAlt.P.Dx3.cut μR M with hθdef
  have hθm : Measurable θ := Formalism.FourierDecayAlt.P.Dx3.cut_meas M
  have hθ0 : ∀ p, 0 ≤ θ p := Formalism.FourierDecayAlt.P.Dx3.cut_nonneg μR M
  have hθ1 : ∀ p : PairSp (k0 + 1) r, InPair L p → ∫ x, θ (stabAct g (Matrix.of x) p) ∂μR = 1 :=
    fun p hp => Formalism.FourierDecayAlt.P.Dx3.cut_norm hH hM0 (hI M hM) p hp.2.1
  refine ⟨(pairMeas L).withDensity (fun p => ENNReal.ofReal (θ p)), ?_⟩
  intro f hf
  have hdens : Measurable fun p => ENNReal.ofReal (θ p) := ENNReal.measurable_ofReal.comp hθm
  have hinner : Measurable fun x => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR :=
    Measurable.lintegral_prod_right' (hf.comp (meas_act g))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  simp only [Pi.mul_apply]
  have e1 : ∀ x, ENNReal.ofReal (θ x) * ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR =
      ∫⁻ a, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂μR := fun x =>
    (lintegral_const_mul _ (hf.comp (meas_act' g x))).symm
  simp_rw [e1]
  have hm2 : Measurable (Function.uncurry fun (x : PairSp (k0 + 1) r) (a : Mt (k0 + 1) r) =>
      ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x)) :=
    (hdens.comp measurable_fst).mul (hf.comp (meas_act g))
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hinv : μR.map Formalism.FourierDecayAlt.B2.invM = μR :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion (k0 + 1) r _ μR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR hgu) hH
  have haem : AEMeasurable Formalism.FourierDecayAlt.B2.invM μR := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hinv] at h0
    exact hH.ne_zero h0
  set G : Mt (k0 + 1) r → PairSp (k0 + 1) r → ENNReal :=
    fun a y => ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) * f y with hGdef
  have e2 : ∀ᵐ a ∂μR, ∫⁻ x, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂(pairMeas L) =
      ∫⁻ y, G a y ∂(pairMeas L) := by
    filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hH] with a ha
    have hmp := mp_stab L hκ0 hκ1 (g := g) (a := Matrix.of a) ha
    have hau : IsUnit (Matrix.of a : Matrix _ _ ℂ).det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N ha.1
    have hGm : Measurable (G a) :=
      (ENNReal.measurable_ofReal.comp (hθm.comp ((meas_act g).comp (measurable_id.prodMk measurable_const)))).mul hf
    rw [← hmp.lintegral_comp hGm]
    refine lintegral_congr fun x => ?_
    have hx : stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) (stabAct g (Matrix.of a) x) = x :=
      Formalism.FourierDecayAlt.P.Dx2.OrbJ.act_act g hgu hau x
    simp only [hGdef, hx]
  rw [lintegral_congr_ae e2]
  have hm3 : AEMeasurable (Function.uncurry G) (μR.prod (pairMeas L)) := by
    have h1 : AEMeasurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r => (Formalism.FourierDecayAlt.B2.invM q.1, q.2))
        (μR.prod (pairMeas L)) :=
      (haem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
    have h2 : Measurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r =>
        ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2) :=
      (ENNReal.measurable_ofReal.comp (hθm.comp (cont_act g).measurable)).mul (hf.comp measurable_snd)
    have e : Function.uncurry G = (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r =>
        ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2) ∘ (fun q => (Formalism.FourierDecayAlt.B2.invM q.1, q.2)) := by
      funext q
      simp only [Function.uncurry, Function.comp_apply, hGdef]
    rw [e]
    exact h2.comp_aemeasurable h1
  rw [lintegral_lintegral_swap hm3]
  refine lintegral_congr_ae ?_
  filter_upwards [pair_inPair L hκ0 hκ1] with y hy
  simp only [hGdef]
  have ham : AEMeasurable (fun b : Mt (k0 + 1) r => ENNReal.ofReal (θ (stabAct g (Matrix.of b) y))) μR :=
    (ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).aemeasurable
  rw [lintegral_mul_const'' _ (by
    have := (ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).comp_aemeasurable haem
    exact this)]
  have e3 : ∫⁻ a, ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) ∂μR =
      ∫⁻ b, ENNReal.ofReal (θ (stabAct g (Matrix.of b) y)) ∂μR := by
    calc ∫⁻ a, ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) ∂μR
        = ∫⁻ b, ENNReal.ofReal (θ (stabAct g (Matrix.of b) y)) ∂(μR.map Formalism.FourierDecayAlt.B2.invM) :=
          (lintegral_map' (by rw [hinv]; exact ham) haem).symm
      _ = _ := by rw [hinv]
  have hint : Integrable (fun b : Mt (k0 + 1) r => θ (stabAct g (Matrix.of b) y)) μR := by
    by_contra h
    have h1 := hθ1 y hy
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  rw [e3, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun b => hθ0 _), hθ1 y hy,
    ENNReal.ofReal_one, one_mul]

def OrbJNormIndep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (p : Formalism.FourierDecayAlt.C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1))
    (g₁ g₂ : Formalism.FourierDecayAlt.B.Mat k r), g₁ ∈ Formalism.FourierDecayAlt.B.GV k r → g₂ ∈ Formalism.FourierDecayAlt.B.GV k r →
    Zhat k r D.z D.z' g₁ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) → Zhat k r D.z D.z' g₂ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) →
    0 < Formalism.FourierDecayAlt.D.ptG (Tz k r D.z * Tz k r D.z') r p →
    (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand D g₁ F q) D.μSS) →
    (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand D g₂ F q) D.μSS) →
    (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)
      (Formalism.FourierDecayAlt.D.orbJ D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)).re =
    (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)
      (Formalism.FourierDecayAlt.D.orbJ D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)).re

theorem repIndep_of (hCut : CutKFin) (hON : OrbJNormIndep) : RepIndep := by
  intro k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g₁ μ₁ ν₁ g₂ μ₂ ν₂ h₁ h₂
  have hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := isLocPt_swap γ
  have hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
  set t : ℝ := (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal with ht
  have htpos : 0 < t := by rw [ht, ENNReal.toReal_ofReal hcard_pos.le]; exact hcard_pos
  have hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hcard_pos
  have key : ∀ (g : ThB.Mx (k0 + 1) r) (μ : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      (IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μ ∧ IsOrbQuot L g μ ν) →
      Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) ∧
      (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) θ ∧
        Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F q) Ds.μSS) ∧
      (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) F)
        (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) F)).re =
        t ^ 2 * hsNormSq (OrbInt L F g ν) := by
    intro g μ ν ⟨hrep, hrel, hroot, hq⟩
    have hZ' : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) := by
      rw [hz, hz', hrep.2, ptMatN_swap]
    have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by rw [hZ', ptMatN_mono]
    have hμ := rootMeas_unique L Ds hz γ hrep.1 hZ hc μ hroot
    rw [hμ] at hq hroot
    have hq' := isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq
    have hconc : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := muR_conc L Ds hz γ hrep.1 hZ
    have hne : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) ≠ 0 := by
      intro h0
      apply muR_ne_zero L hc γ g _ hroot
      rw [h0, smul_zero]
    have : SFinite (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) := by
      unfold Formalism.FourierDecayAlt.D.muR
      infer_instance
    have hcut := hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hrep.1 hZ'
    have hJ := orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hrep.1 hrel hconc hne hq' F hcut
    refine ⟨hZ', hcut, ?_⟩
    have hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) = t • OrbInt L F g ν := by
      unfold OrbInt
      rw [integral_smul_measure]
    show (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F)
      (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F)).re = _
    rw [hJ, hsm, ← hsInner_eq, ← hsNormSq, hsNormSq_smul]
  obtain ⟨hZ1, hc1, e1⟩ := key g₁ μ₁ ν₁ h₁
  obtain ⟨hZ2, hc2, e2⟩ := key g₂ μ₂ ν₂ h₂
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap) := by
    rw [ptG_eq_GPoint, hz, hz']
    exact hpos
  have hEq := hON (k0 + 1) r L.Wp L.Wq Ds F (γ.1.map Prod.swap) hp g₁ g₂ h₁.1.1 h₂.1.1 hZ1 hZ2 hG hc1 hc2
  rw [e1, e2] at hEq
  have ht2 : t ^ 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ ht2 hEq

section HSinv
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem hsNormSq_eq_sum (A : V →L[ℂ] W) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_isom_comp (U : W →L[ℂ] W) (hU : ∀ x, ‖U x‖ = ‖x‖) (A : V →L[ℂ] W) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply, hU]

theorem sum_norm_sq_basis [FiniteDimensional ℂ W] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (c : OrthonormalBasis κ ℂ W) (A : V →L[ℂ] W) :
    haveI := FiniteDimensional.complete ℂ V
    haveI := FiniteDimensional.complete ℂ W
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2 := by
  have := FiniteDimensional.complete ℂ V
  have := FiniteDimensional.complete ℂ W
  calc ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ∑ j, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := by
        simp_rw [c.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖⟪(ContinuousLinearMap.adjoint A) (c j), b i⟫_ℂ‖ ^ 2 := by
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
    _ = _ := by simp_rw [b.sum_sq_norm_inner_left]

theorem hsNormSq_comp_isom [FiniteDimensional ℂ W] (A : V →L[ℂ] W) (U : V →L[ℂ] V)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : hsNormSq (A.comp U) = hsNormSq A := by
  let li : V →ₗᵢ[ℂ] V := ⟨U.toLinearMap, hU⟩
  let e : V ≃ₗᵢ[ℂ] V := li.toLinearIsometryEquiv rfl
  have he : ∀ x, e x = U x := fun x => rfl
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum]
  have h1 := sum_norm_sq_basis ((stdOrthonormalBasis ℂ V).map e) (stdOrthonormalBasis ℂ W) A
  have h2 := sum_norm_sq_basis (stdOrthonormalBasis ℂ V) (stdOrthonormalBasis ℂ W) A
  rw [h2, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [he]

end HSinv

theorem orbital_norm_independence : OrbJNormIndep := by
  intro k r Wp Wq _ _ _ _ _ _ D F p hp g₁ g₂ hg₁ hg₂ hZ₁ hZ₂ hG _ _
  have hpos₁ : 0 < Gf k r D.z D.z' g₁ := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k r D.z D.z' p g₁ hp hZ₁]
    exact hG
  obtain ⟨s, hs, s', hs', he⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description k r D.z D.z' (Formalism.FourierDecayAlt.P.Dx2.Rad.std D) g₁ hg₁ g₂ hg₂
    hpos₁ (by rw [hZ₁, hZ₂])
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z D) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime D) hs'
  have key := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt D p hp hg₁ hZ₁ hpos₁ hhA hnA hfA hhB hnB hfB F
  subst he
  rw [← key, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, ← hsInner_eq, ← hsInner_eq, ← hsNormSq, ← hsNormSq]
  unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
  rw [hsNormSq_isom_comp _ (D.π_unitary hA hhA), hsNormSq_comp_isom _ _ (D.π'_unitary _ (uw_inv hhB))]

theorem K_finite_decay : CutKFin := by
  intro k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hg hZ'
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by rw [hZ', ptMatN_mono]
  have hG : 0 < Gf (k0 + 1) r Ds.z Ds.z' g := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec (k0 + 1) r Ds.z Ds.z' _ g hp hZ', ptG_eq_GPoint, hz, hz']
    exact hpos
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds (k0 + 1) r L.Wp L.Wq Ds _ g hp hg hZ'
  exact Classical.choose_spec Formalism.FourierDecayAlt.P.orbital_integral_converges (k0 + 1) r L.Wp L.Wq Ds g (wPt γ) (dPt γ) (A0 (k0 + 1) r) F hg
    hrel (dPt_ne γ) hZ hG le_rfl hdec

def chi0 (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

def chiE (Lt : Lev) (E : List ℕ) (δ : ℝ) (g : Mat Lt.k0 Lt.r) : ℝ :=
  (E.map fun l => if hl : l < Lt.r + 2 then
    chi0 (Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩) / δ) else 1).prod

open Classical in

def cellF (Lt : Lev) (E : List ℕ) {N : ℕ}
    (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)) (δ : ℝ) (F : Lt.GF) : Lt.GF := fun g =>
  if g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ g ∈ OnePlaceEstimates.minorsNe Lt E ∧ 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g then
    ∑ n, a n g (Lt.Eword (ws n) (fun y => ((chiE Lt E δ y : ℝ) : ℂ) • F y) g)
  else 0

open scoped ContDiff in

def CellBudget : Prop :=
  ∀ (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (N : ℕ)
    (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, (ws n).length ≤ o) →
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ OnePlaceEstimates.minorsNe Lt E ∩ {g | 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) →
    (∀ n, ∀ w : List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)), ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), ε ≤ Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g →
        (∀ l ∈ E, ∀ hl : l < Lt.r + 2, δ ≤ Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩)) →
        ‖Lt.EwordV w (a n) g‖ ≤ C * (1 + Lev.matNorm g) ^ (dP + 3 * ((Lt.r : ℝ) + 1) * w.length)) →
    ∀ (A : ℝ) (F : Lt.GF), (∀ mm : ℕ, IsCC (Lt.k0 + 1) Lt.r (A - 3 * ((Lt.r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε → SuppGe Lt ε F →
    ∀ δ : ℝ, 0 < δ → ∀ mm : ℕ,
      IsCC (Lt.k0 + 1) Lt.r (A - dP - 3 * ((Lt.r : ℝ) + 1) * ((mm : ℝ) + o)) mm (cellF Lt E ws a δ F)

def cJ : ℝ := 12

section jc12
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end jc12

open scoped ContDiff in

def CellVanish : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ →
    IsSection (k0 + 1) r L.z L.z' μsec →
    ∀ (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L) (N : ℕ)
      (ws : Fin N → List (Fin (2 * r + (k0 + 1) + 1) × Fin (2 * r + (k0 + 1) + 1)))
      (a : Fin N → Mat k0 r → ((L.Wq →L[ℂ] L.Wp) →L[ℂ] (L.Wq →L[ℂ] L.Wp))),
      GramWordSpace.IsInvC (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) Θ → (∀ n, (ws n).length ≤ o) →
      (∀ n, ∃ U : Set (Mat k0 r), IsOpen U ∧
        UH (Hpk (k0 + 1) r) ∩ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E ∩ {g | 0 < Gf (k0 + 1) r L.z L.z' g} ⊆ U ∧
        ContDiffOn ℝ ∞ (a n) U) →
      (∀ F : GramWordSpace.GFn L, ∀ g ∈ UH (Hpk (k0 + 1) r),
        g ∈ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E → 0 < Gf (k0 + 1) r L.z L.z' g →
        GramWordSpace.CkAt (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g →
        Θ F g = ∑ n, a n g ((GramWordSpace.levOf L μsec).Eword (ws n) F g)) →
      GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ (A : ℝ) (F : GramWordSpace.GFn L), (∀ mm : ℕ, IsCC (k0 + 1) r (A - 3 * ((r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        cJ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + (r : ℝ) * ((2 * r + (k0 + 1) + 1 : ℕ) : ℝ) + 1) +
          5 * ((r : ℝ) + 1) * ((o : ℝ) + 1) ≤ A →
        ∀ δ : ℝ, 0 < δ →
        ∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz (k0 + 1) r L.z * Tz (k0 + 1) r L.z' < Complex.normSq q.2 →
          L.J (cellF (GramWordSpace.levOf L μsec) E ws a δ F) (bigCell (k0 + 1) r q.1 (μsec q.2)) = 0

def deltaPt {r : ℕ} (γ : Point ℂ (r + 1)) : ℝ :=
  (1 / 2) * ((OnePlaceEstimates.endsC 0 γ.1).map fun e => if h : e ≤ r + 1 then
    min 1 (Complex.normSq ((ptMat γ).submatrix (Fin.castLE h) (Fin.castLE h)).det) else 1).prod

theorem prod_le_one' (l : List ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h1 : ∀ x ∈ l, x ≤ 1) : l.prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons]
    have hx0 := h0 x List.mem_cons_self
    have hx1 := h1 x List.mem_cons_self
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun z hz => h0 z (List.mem_cons_of_mem _ hz)
    have := ih (fun z hz => h0 z (List.mem_cons_of_mem _ hz)) (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
    nlinarith

def CellReplT : Prop :=
  ∀ (D : D7) (k0 : ℕ), k0 + 1 = D.R.k → ∀ (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ, cJ * ((D.R.rS : ℝ) + 1) ^ 2 * ((o : ℝ) + (D.R.rS : ℝ) * D.R.r + 1) +
        5 * ((D.R.rS : ℝ) + 1) * ((o : ℝ) + 1) ≤ A → ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∃ F' : GramWordSpace.GFn L,
          (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - dP - 3 * ((D.R.rS : ℝ) + 1) * ((mm : ℝ) + o)) mm F') ∧
          SuppGe (GramWordSpace.levOf L μsec) ε F' ∧
          (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
            Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
            L.J F' (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ (g : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ)
            (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
            0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
            IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
              OrbInt L (Θ F) g ν = OrbInt L F' g ν

section HSadj
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun A := WithLp.toLp 2 fun i => A (stdOrthonormalBasis ℂ Wq i)
  invFun v := LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => (WithLp.ofLp v) i))
  map_add' A B := by ext i; simp
  map_smul' c A := by ext i; simp
  left_inv A := by
    apply ContinuousLinearMap.coe_injective
    refine (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => ?_
    simp
  right_inv v := by
    ext i
    simp

theorem hsInner_hsE (A B : Wq →L[ℂ] Wp) : Formalism.FourierDecayAlt.B.hsInner A B = ⟪hsE B, hsE A⟫_ℂ := rfl

def adjHS (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap ((hsE.symm.toLinearMap) ∘ₗ
    (LinearMap.adjoint (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)) ∘ₗ hsE.toLinearMap)

theorem adjHS_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsInner (T A) B = Formalism.FourierDecayAlt.B.hsInner A (adjHS T B) := by
  rw [hsInner_hsE, hsInner_hsE]
  have e1 : hsE (T A) = (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE A) := by simp
  have e2 : hsE (adjHS T B) = LinearMap.adjoint (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE B) := by
    simp [adjHS]
  rw [e1, e2, LinearMap.adjoint_inner_left]

end HSadj

section HSadj2
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem adjHS_add (T₁ T₂ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjHS (T₁ + T₂) = adjHS T₁ + adjHS T₂ := by
  apply ContinuousLinearMap.coe_injective
  simp [adjHS, LinearMap.comp_add, LinearMap.add_comp, map_add]

theorem adjHS_smul (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjHS (c • T) = (starRingEnd ℂ c) • adjHS T := by
  apply ContinuousLinearMap.coe_injective
  have e : (hsE.toLinearMap ∘ₗ (c • T).toLinearMap ∘ₗ hsE.symm.toLinearMap : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →ₗ[ℂ] _) =
      c • (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) := by
    ext v
    simp
  simp only [adjHS, LinearMap.coe_toContinuousLinearMap']
  rw [e, LinearMap.adjoint.map_smulₛₗ]
  ext x
  simp

def adjHSR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →ₗ[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) where
  toFun := adjHS
  map_add' := adjHS_add
  map_smul' c T := by
    have h1 : c • T = ((c : ℂ)) • T := (Complex.coe_smul c T).symm
    have h2 : c • adjHS T = ((c : ℂ)) • adjHS T := (Complex.coe_smul c (adjHS T)).symm
    simp only [RingHom.id_apply]
    rw [h1, h2, adjHS_smul, Complex.conj_ofReal]

end HSadj2

section cellOp
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def cellTerms (w : List (Formalism.MainNotions.BridgeLemma₃.cal_Ix k r)) (a : Formalism.FourierDecayAlt.B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) :
    List (Formalism.FourierDecayAlt.B.DTerm k r Wp Wq) :=
  (Formalism.MainNotions.BridgeLemma₃.cal_expE w).attach.map fun cv =>
    { coef := fun g => cv.1.1 • a g
      coefAdj := fun g => adjHS (cv.1.1 • a g)
      word := cv.1.2
      word_lie := fun X hX => Formalism.MainNotions.BridgeLemma₃.cal_expE_lie w cv.1 cv.2 X hX
      adj_id := by
        intro x A B
        exact adjHS_spec (cv.1.1 • a x) A B }

def cellOp {N : ℕ} (ws : Fin N → List (Formalism.MainNotions.BridgeLemma₃.cal_Ix k r))
    (a : Fin N → Formalism.FourierDecayAlt.B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) : Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq :=
  (List.finRange N).flatMap fun n => cellTerms (ws n) (a n)

end cellOp

section cellOp2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cellOp2

section cellOp3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cellOp3

def CkAtE (Lt : Lev) (o : ℕ) (F : Lt.GF) (g₀ : Mat Lt.k0 Lt.r) : Prop :=
  ∃ (U : Set (Mat Lt.k0 Lt.r)) (F' : Lt.GF), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ o F' U ∧
    ∀ g ∈ U, g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) → F g = F' g

theorem xi_eq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) := by
  simp only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, one_mul]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem act_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0)
    (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (hz : D.z = L.z) (hz' : D.z' = L.z') (hπ : D.π = L.π)
    (hπ' : D.π' = L.π') (p : Formalism.FourierDecayAlt.B.SS (k0 + 1) r) (J : GramWordSpace.GFn L) (g : Mat k0 r) :
    (GramWordSpace.levOf L μsec).act (Matrix.of p.1.1) (Matrix.of p.1.2) (Matrix.of p.2.1) (Matrix.of p.2.2) J g =
      Formalism.FourierDecayAlt.B.xiTau D (1, 1) p • Formalism.FourierDecayAlt.B.rho D p J g := by
  rw [xi_eq, hz, hz']
  simp only [Lev.act, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hπ, hπ']
  rfl

section zeroOp
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def zeroOp (o : ℕ) : Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq :=
  [{ coef := fun _ => 0
     coefAdj := fun _ => 0
     word := List.replicate o 0
     word_lie := fun X hX => by
       rw [List.eq_of_mem_replicate hX]
       simp [Formalism.FourierDecayAlt.B.inLie]
     adj_id := fun x A B => by simp [hsInner_hsE] }]

end zeroOp

def bigPosE (Lt : Lev) : Set (Mat Lt.k0 Lt.r) :=
  {g | g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ (∀ l : Fin (Lt.r + 2), Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g l ≠ 0) ∧
    0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g}

open scoped ContDiff in

def CellVanishE : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ →
    IsSection (k0 + 1) r L.z L.z' μsec →
    ∀ (E : List ℕ) (o : ℕ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L) (N : ℕ)
      (ws : Fin N → List (Fin (2 * r + (k0 + 1) + 1) × Fin (2 * r + (k0 + 1) + 1)))
      (a : Fin N → Mat k0 r → ((L.Wq →L[ℂ] L.Wp) →L[ℂ] (L.Wq →L[ℂ] L.Wp))),
      (∀ h ∈ UWset (k0 + 1) r L.z, ∀ n ∈ Nset (k0 + 1) r, ∀ h' ∈ UWset (k0 + 1) r L.z', ∀ n' ∈ Nset (k0 + 1) r,
        ∀ F : GramWordSpace.GFn L,
        (∀ g ∈ UH (Hpk (k0 + 1) r), CkAtE (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g) →
        ∀ g ∈ UH (Hpk (k0 + 1) r), Θ ((GramWordSpace.levOf L μsec).act h n h' n' F) g =
          (GramWordSpace.levOf L μsec).act h n h' n' (Θ F) g) →
      (∀ n, (ws n).length ≤ o) →
      (∀ n, ∃ U : Set (Mat k0 r), IsOpen U ∧
        UH (Hpk (k0 + 1) r) ∩ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E ∩ {g | 0 < Gf (k0 + 1) r L.z L.z' g} ⊆ U ∧
        ContDiffOn ℝ ∞ (a n) U) →
      (∀ F : GramWordSpace.GFn L, ∀ g ∈ UH (Hpk (k0 + 1) r),
        g ∈ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E → 0 < Gf (k0 + 1) r L.z L.z' g →
        CkAtE (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g →
        Θ F g = ∑ n, a n g ((GramWordSpace.levOf L μsec).Eword (ws n) F g)) →
      (∀ J : GramWordSpace.GFn L, (∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), CkAtE (GramWordSpace.levOf L μsec) o J g) →
        (∀ h ∈ UWset (k0 + 1) r L.z, ∀ n ∈ Nset (k0 + 1) r, ∀ h' ∈ UWset (k0 + 1) r L.z', ∀ n' ∈ Nset (k0 + 1) r,
          ∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), (GramWordSpace.levOf L μsec).act h n h' n' J g = J g) →
        ∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), Θ J g = 0) →
      ∀ (A : ℝ) (F : GramWordSpace.GFn L), (∀ mm : ℕ, IsCC (k0 + 1) r (A - 3 * ((r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        cJ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + (r : ℝ) * ((2 * r + (k0 + 1) + 1 : ℕ) : ℝ) + 1) +
          5 * ((r : ℝ) + 1) * ((o : ℝ) + 1) ≤ A →
        ∀ δ : ℝ, 0 < δ →
        ∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz (k0 + 1) r L.z * Tz (k0 + 1) r L.z' < Complex.normSq q.2 →
          L.J (cellF (GramWordSpace.levOf L μsec) E ws a δ F) (bigCell (k0 + 1) r q.1 (μsec q.2)) = 0

end Formalism.MainNotions.BigCellDensity
