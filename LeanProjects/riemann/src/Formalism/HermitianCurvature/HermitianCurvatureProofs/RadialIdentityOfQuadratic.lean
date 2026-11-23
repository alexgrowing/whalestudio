import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentOfAB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Q

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RDRadIdPropQ (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → ∀ q ∈ JF.QDom k r D.z D.z',
    s • B.JF D (wvG D.z D.z' s F) (B.gq D q) =
      B.JF D (B.opAdj (Θ 0) (wvG D.z D.z' s (B.opApply (Θ 1) F))) (B.gq D q) -
        B.JF D (B.opAdj (Θ 2) (wvG D.z D.z' s (B.opApply (Θ 3) F))) (B.gq D q)

end Q

def RDIdentABQ : Prop :=
  RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∃ Θ : Fin 4 → B.DiffOp k r Wp Wq, RDOpsProp D Θ ∧ RDRadIdPropQ D Θ

section LinQ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem beta_lin_rdQ (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (F0 F1 F2 F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (h1 : ∀ (A : ℝ) (m : ℕ), B.InCC A m F1) (h2 : ∀ (A : ℝ) (m : ℕ), B.InCC A m F2)
    (h' : ∀ (A : ℝ) (m : ℕ), B.InCC A m F')
    (h : ∀ q ∈ JF.QDom k r D.z D.z', s • B.JF D F0 (B.gq D q) = B.JF D F1 (B.gq D q) - B.JF D F2 (B.gq D q)) :
    s * B.beta D F0 F' = B.beta D F1 F' - B.beta D F2 F' := by
  have hb : ∀ F, B.beta D F F' = ∫ q, (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q))) := fun F => rfl
  rw [hb, hb, hb, ← integral_sub (Formalism.FourierDecayAlt.P.JCx2.rb_int_pair D F1 F' h1 h')
    (Formalism.FourierDecayAlt.P.JCx2.rb_int_pair D F2 F' h2 h'), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with hq | hw
  · rw [← mul_sub, ← inner_sub_right, ← hsVec_sub_rd, ← h q hq, hsVec_smul_rd, inner_smul_right]
    ring
  · simp [hw]

end LinQ

theorem radial_identity_of_quadratic (hAB : RDIdentABQ) : RDIdent := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨Θ, hOps, hRad⟩ := hAB Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨c, -, -, -, -, -, hP⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq D (B.AB P.k P.r) le_rfl
  have ccAll : ∀ F, NiceAll D F → ∀ (A : ℝ) (m : ℕ), B.InCC A m F := fun F ⟨_, _, _, h, _⟩ => h
  have wvNice : ∀ s F, NiceAll D F → NiceAll D (wvG D.z D.z' s F) := fun s F ⟨ε, hε, h⟩ =>
    ⟨ε, hε, (radial_wave_identity P.k P.r Wp Wq D hr ε s F).1 h⟩
  have swap : ∀ j X F', NiceAll D X → NiceAll D F' →
      B.beta D (B.opAdj (Θ j) X) F' = B.beta D X (B.opApply (Θ j) F') := by
    intro j X F' ⟨ε1, hε1, hX⟩ ⟨ε2, hε2, hF'⟩
    obtain ⟨hS, hC, hPC, -⟩ := hOps j
    obtain ⟨d, hd, hpc⟩ := hPC (min ε1 ε2) (lt_min hε1 hε2)
    have h := hP (Θ j) (min ε1 ε2) d (lt_min hε1 hε2) hd hS hC hpc F' X (hF'.2.1 _ _) (hX.2.1 _ _)
      (fun g hg hne => (min_le_right _ _).trans (hF'.2.2 g hg hne))
      (fun g hg hne => (min_le_left _ _).trans (hX.2.2 g hg hne))
    rw [beta_conj_rd D (B.opAdj (Θ j) X) F', ← h, ← beta_conj_rd]
  refine ⟨fun j => B.opApply (Θ j), fun j F hF => ((hOps j).2.2.2 F hF).1, fun s F F' hF hF' => ?_⟩
  have hW1 := wvNice s _ ((hOps 1).2.2.2 F hF).1
  have hW3 := wvNice s _ ((hOps 3).2.2.2 F hF).1
  have hA := ((hOps 0).2.2.2 _ hW1).2
  have hB := ((hOps 2).2.2.2 _ hW3).2
  rw [beta_lin_rdQ D s _ _ _ F' (ccAll _ hA) (ccAll _ hB) (ccAll _ hF') (hRad s F hF), swap 0 _ F' hW1 hF',
    swap 2 _ F' hW3 hF']

theorem radDecay_of_ABQ (h : RDIdentABQ) : RadDecay := radDecay_of_cut (radial_identity_of_quadratic h)

section Alg

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

def StarCoords (L : R.LevelData A r) : Prop :=
  ∀ l, star (L.p l) = -L.pb l ∧ star (L.pb l) = -L.p l ∧ star (L.c l) = L.cb l ∧ star (L.cb l) = L.c l ∧
    star (L.ci l) = L.cbi l ∧ star (L.cbi l) = L.ci l

def coordOps (L : R.LevelData A r) (l : Fin r) : Set A := {L.p l, L.pb l, L.c l, L.ci l, L.cb l, L.cbi l}

def StartCoord (L : R.LevelData A r) (st : Fr.Start A) : Prop :=
  ∀ (Y : ℂ) (a b : Fin 2) (l : Fin r), ∀ x ∈ coordOps L l, Commute (st.QQ Y a b) x

def WaveAtSite (L : R.LevelData A r) (st : Fr.Start A) (l₀ : Fin r) (s : ℂ) (f fi : A) : Prop :=
  IsWave f fi ∧ Commute f (L.c l₀) ∧ Commute f (L.ci l₀) ∧ Commute f (L.cb l₀) ∧ Commute f (L.cbi l₀) ∧
    L.p l₀ * f = f * L.p l₀ + algebraMap ℂ A s * f * L.c l₀ ∧
    L.pb l₀ * f = f * L.pb l₀ - algebraMap ℂ A (starRingEnd ℂ s) * f * L.cb l₀ ∧
    (∀ l, l ≠ l₀ → ∀ x ∈ coordOps L l, Commute f x) ∧ (∀ x ∈ Fr.zfns L, Commute f x) ∧
    ∀ (Y : ℂ) (a b : Fin 2), Commute f (st.QQ Y a b)

def RhR (L : R.LevelData A r) (st : Fr.Start A) (Y : ℂ) : A :=
  L.Drb * (st.QQ Y 1 0 * L.Ar Y + st.QQ Y 1 1 * L.Br Y)

def RhvR (L : R.LevelData A r) (st : Fr.Start A) (Y : ℂ) : A :=
  L.Dr * (st.QQ Y 0 1 * L.Avr Y + st.QQ Y 1 1 * L.Bvr Y)

def GiR (L : R.LevelData A r) : A := L.Dri * L.Drbi * L.GGi

def thR (L : R.LevelData A r) (st : Fr.Start A) (Y : ℂ) : Fin 4 → A :=
  ![L.Ahatv (Y + 1), GiR L * st.xi Y * RhR L st Y, GiR L * st.xi (Y + 1) * RhvR L st (Y + 1), L.Ahat Y]

end Alg

def RDCollapse : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (hr : 0 < r) (L : R.LevelData A r) (st : Fr.Start A) (s Y : ℂ) (f fi : A),
    StarCoords L → WaveAtSite L st ⟨0, hr⟩ s f fi → star Y = Y →
    star (L.Avr (Y + 1)) * f * L.Br Y - star (L.Bvr (Y + 1)) * f * L.Ar Y = algebraMap ℂ A s * f

def RadialGaugeAdjointRelation : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (L : R.LevelData A r) (st : Fr.Start A) (Y : ℂ),
    Fr.IsStarLevel L → StarCoords L → Fr.IsLevelStart L st → star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv →
    star (st.xi Y * L.GGi * st.QQ Y 1 0) = st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1

def RDRearr : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (hr : 0 < r) (L : R.LevelData A r) (st : Fr.Start A) (s Y : ℂ) (f fi : A),
    StarCoords L → Fr.IsStarLevel L → Fr.IsLevelStart L st → StartCoord L st → WaveAtSite L st ⟨0, hr⟩ s f fi →
    star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv →
    star (st.xi Y * L.GGi * st.QQ Y 1 0) = st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1 →
    star (thR L st Y 0) * f * thR L st Y 1 - star (thR L st Y 2) * f * thR L st Y 3 =
      star (L.Avr (Y + 1)) * f * L.Br Y - star (L.Bvr (Y + 1)) * f * L.Ar Y

def RDRadIdAlg : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (hr : 0 < r) (L : R.LevelData A r) (st : Fr.Start A) (s Y : ℂ) (f fi : A),
    StarCoords L → Fr.IsStarLevel L → Fr.IsLevelStart L st → StartCoord L st → WaveAtSite L st ⟨0, hr⟩ s f fi →
    star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv →
    star (thR L st Y 0) * f * thR L st Y 1 - star (thR L st Y 2) * f * thR L st Y 3 = algebraMap ℂ A s * f

theorem rDRadIdAlg_of_collapse_gauge_rearr (hC : RDCollapse) (hG : RadialGaugeAdjointRelation) (hR : RDRearr) : RDRadIdAlg := by
  intro A _ _ _ _ r hr L st s Y f fi hS hSL hLS hSC hW hY hi hi1
  rw [hR A r hr L st s Y f fi hS hSL hLS hSC hW hY hi hi1 (hG A r L st Y hSL hS hLS hY hi hi1)]
  exact hC A r hr L st s Y f fi hS hW hY

theorem rDStarCoords_of_actual {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (h : IsActualLevel X L) : StarCoords L := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := h
  intro l
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp l, hpb l]; exact Prod.ext rfl (neg_neg _).symm
  · rw [hp l, hpb l]; exact Prod.ext rfl (neg_neg _).symm
  · rw [hc l, hcb l]; rfl
  · rw [hc l, hcb l]; rfl
  · rw [hci l, hcbi l]; rfl
  · rw [hci l, hcbi l]; rfl

def RDStartCoord : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ), IsData P z z' π π' X μ L st l0 → StartCoord L st

def RDWaveRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hr : 0 < P.r) (s : ℂ), IsData P z z' π π' X μ L st l0 →
    ∀ Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'),
      multiplicationOperator Wv (fun c _ => fsv s (c ⟨0, hr⟩)) → multiplicationOperator Wv' (fun c _ => fsv (-s) (c ⟨0, hr⟩)) →
      WaveAtSite L st ⟨0, hr⟩ s (mkP Wv Wv') (mkP Wv' Wv)

def RDResRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ), IsData P z z' π π' X μ L st l0 →
    ∀ J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z'), ∃ Φ : RadSp P.k P.r z z' π π',
      ∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2

def RDWaveFF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hr : 0 < P.r) (s : ℂ), IsData P z z' π π' X μ L st l0 →
    ∀ J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z'),
      wvG z z' s J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') ∧
      ∀ x ∈ DomR P.k P.r z z',
        resG P.k P.r (Fin.last P.r) (wvG z z' s J) x.1 x.2 = fsv s (x.1 ⟨0, hr⟩) • resG P.k P.r (Fin.last P.r) J x.1 x.2

def RDOpFF : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z'),
      B.opApply Θ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') ∧
      B.opAdj Θ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z')

def RDGqRes : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ q ∈ JF.QDom k r D.z D.z', ∃ x ∈ DomR k r D.z D.z', ∃ w : ℂ, w ≠ 0 ∧
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z'),
      resG k r (Fin.last r) J x.1 x.2 = w • J (B.gq D q)

section Spec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def RDSpec (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) (Y : ℂ)
    (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ (j : Fin 4) (J : B.Mat k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r z z' π π' 0 (JF.Om k r z z') →
    ∀ Φ : RadSp k r z z' π π',
      (∀ x ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) J x.1 x.2) →
      ∀ x ∈ DomR k r z z',
        resG k r (Fin.last r) (B.opApply (Θ j) J) x.1 x.2 =
            ((thR L st Y j).1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
          resG k r (Fin.last r) (B.opAdj (Θ j) J) x.1 x.2 =
            ((thR L st Y j).2.unop Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

end Spec

section Grp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RDGrpIdProp (D : B.RealPlaceData k r Wp Wq) (Θ : Fin 4 → B.DiffOp k r Wp Wq) : Prop :=
  ∀ (s : ℂ) (J : B.Mat k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
    ∀ q ∈ JF.QDom k r D.z D.z',
      s • wvG D.z D.z' s J (B.gq D q) =
        B.opAdj (Θ 0) (wvG D.z D.z' s (B.opApply (Θ 1) J)) (B.gq D q) -
          B.opAdj (Θ 2) (wvG D.z D.z' s (B.opApply (Θ 3) J)) (B.gq D q)

end Grp

def RDIdentSpec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∃ (Y : ℂ) (Θ : Fin 4 → B.DiffOp P.k P.r Wp Wq), star Y = Y ∧ Y ∈ st.inv ∧ Y + 1 ∈ st.inv ∧
      RDOpsProp D Θ ∧ RDSpec L st Y Θ

def RDRadIdOfSpec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∀ (Y : ℂ) (Θ : Fin 4 → B.DiffOp P.k P.r Wp Wq), star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv →
      RDOpsProp D Θ → RDSpec L st Y Θ → RDRadIdPropQ D Θ

def RDGrpIdOfSpec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∀ (Y : ℂ) (Θ : Fin 4 → B.DiffOp P.k P.r Wp Wq), star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv →
      RDOpsProp D Θ → RDSpec L st Y Θ → RDGrpIdProp D Θ

theorem rDIdentABQ_of_spec (ha : RDIdentSpec) (hb : RDRadIdOfSpec) : RDIdentABQ := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨Y, Θ, hY, hi, hi1, hO, hS⟩ := ha Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  exact ⟨Θ, hO, hb Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y Θ hY hi hi1 hO hS⟩

def RDJNice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F →
    B.JF D F ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') ∧ B.CkOn ⊤ (JF.Om k r D.z D.z') (B.JF D F)

def RDWaveJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (H : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D H →
    ∀ g ∈ JF.Om k r D.z D.z', B.JF D (wvG D.z D.z' s H) g = wvG D.z D.z' s (B.JF D H) g

def RDOpLocal : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ JF.Om k r D.z D.z', f₁ g = f₂ g) →
    ∀ g ∈ JF.Om k r D.z D.z', B.opApply Θ f₁ g = B.opApply Θ f₂ g ∧ B.opAdj Θ f₁ g = B.opAdj Θ f₂ g

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_of_top {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (B.Mat k r)}
    {f : B.Mat k r → E} (m : ℕ) (h : B.CkOn ⊤ UU f) : B.CkOn (m : ℕ∞) UU f := by
  intro g₀ hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg
  exact ⟨U, f', hU, hgU, hf'.of_le (WithTop.coe_le_coe.mpr le_top), he⟩

theorem thrW_exists (k r m : ℕ) : ∃ A, Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A m := by
  refine ⟨6 * (r : ℝ) * (m : ℝ) + |(r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1)| + 1, ?_, ?_⟩
  · have := abs_nonneg ((r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1)); linarith
  · have := le_abs_self ((r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1)); linarith

theorem rDRadIdOfSpec_of_grpId_theta (hG : RDGrpIdOfSpec) (hT : Formalism.FourierDecayAlt.P.CutMP.JA.LT.ThetaJ) (hN : RDJNice)
    (hW : RDWaveJ) (hL : RDOpLocal) : RDRadIdOfSpec := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y Θ hY hi hi1 hO hS
  have hGI := hG Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y Θ hY hi hi1 hO hS
  have wvNice : ∀ s F, NiceAll D F → NiceAll D (wvG D.z D.z' s F) := fun s F ⟨ε, hε, h⟩ =>
    ⟨ε, hε, (radial_wave_identity P.k P.r Wp Wq D hr ε s F).1 h⟩
  have link_brest₂ : ∀ j F, NiceAll D F → (∀ g ∈ JF.Om P.k P.r D.z D.z',
      B.opApply (Θ j) (B.JF D F) g = B.JF D (B.opApply (Θ j) F) g) ∧
      ∀ g ∈ JF.Om P.k P.r D.z D.z', B.opAdj (Θ j) (B.JF D F) g = B.JF D (B.opAdj (Θ j) F) g := by
    intro j F hF
    have hF' := hF
    obtain ⟨ε, hε, hCk, hCC, -⟩ := hF'
    obtain ⟨hSm, hC, -, -⟩ := hO j
    obtain ⟨A, hA⟩ := thrW_exists P.k P.r (B.opOrder (Θ j))
    exact hT P.k P.r Wp Wq D (Θ j) A F (JF.Om P.k P.r D.z D.z') hA hSm hC hCk (hCC _ _) subset_rfl
      (ckOn_of_top _ (hN P.k P.r Wp Wq D F hF).2)
  intro s F hF q hq
  have hg := Formalism.FourierDecayAlt.P.big_cell_domain P.k P.r Wp Wq D q hq
  have key := hGI s (B.JF D F) (hN P.k P.r Wp Wq D F hF).1 q hq
  have term : ∀ a b : Fin 4, B.JF D (B.opAdj (Θ a) (wvG D.z D.z' s (B.opApply (Θ b) F))) (B.gq D q) =
      B.opAdj (Θ a) (wvG D.z D.z' s (B.opApply (Θ b) (B.JF D F))) (B.gq D q) := by
    intro a b
    have hF1 : NiceAll D (wvG D.z D.z' s (B.opApply (Θ b) F)) := wvNice s _ ((hO b).2.2.2 F hF).1
    rw [← (link_brest₂ a _ hF1).2 _ hg]
    refine (hL P.k P.r Wp Wq D (Θ a) _ _ (fun g' hg' => ?_) _ hg).2
    rw [hW P.k P.r Wp Wq D s _ ((hO b).2.2.2 F hF).1 g' hg']
    unfold wvG
    rw [(link_brest₂ b F hF).1 g' hg']
  rw [hW P.k P.r Wp Wq D s F hF _ hg, term 0 1, term 2 3]
  exact key

theorem rDGrpIdOfSpec_of_radIdAlg (hA : RDRadIdAlg) (hSC : RDStartCoord) (hWR : RDWaveRad) (hWC : WaveCExists)
    (hRR : RDResRad) (hWF : RDWaveFF) (hOF : RDOpFF) (hGQ : RDGqRes) : RDGrpIdOfSpec := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y Θ hY hi hi1 hO hS s J hJ q hq
  subst hz hz' hπ hπ'
  obtain ⟨x, hx, w, hw0, hres⟩ := hGQ P.k P.r Wp Wq D q hq
  obtain ⟨Wv, hWv⟩ := hWC Wp Wq P.k P.r D.z D.z' D.π D.π' ⟨0, hr⟩ s
  obtain ⟨Wv', hWv'⟩ := hWC Wp Wq P.k P.r D.z D.z' D.π D.π' ⟨0, hr⟩ (-s)
  obtain ⟨Φ, hΦ⟩ := hRR Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD J hJ
  have hwave := hWR Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hr s hD Wv Wv' hWv hWv'
  have halg := hA (Pr (RadSp P.k P.r D.z D.z' D.π D.π')) P.r hr L st s Y (mkP Wv Wv') (mkP Wv' Wv)
    (rDStarCoords_of_actual hD.2.2.1) hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2
    (hSC Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD) hwave hY hi hi1
  have hterm : ∀ a b : Fin 4,
      B.opAdj (Θ a) (wvG D.z D.z' s (B.opApply (Θ b) J)) ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (JF.Om P.k P.r D.z D.z') ∧
      resG P.k P.r (Fin.last P.r) (B.opAdj (Θ a) (wvG D.z D.z' s (B.opApply (Θ b) J))) x.1 x.2 =
        ((star (thR L st Y a) * mkP Wv Wv' * thR L st Y b).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro a b
    have hJb := (hOF P.k P.r Wp Wq D (Θ b) (hO b).1 (hO b).2.1 J hJ).1
    have hwb := hWF Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hr s hD _ hJb
    have hΦ' : ∀ y ∈ DomR P.k P.r D.z D.z', ((Wv ((thR L st Y b).1 Φ) : RadSp P.k P.r D.z D.z' D.π D.π') :
        Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (wvG D.z D.z' s (B.opApply (Θ b) J)) y.1 y.2 := by
      intro y hy
      rw [hWv, hwb.2 y hy, (hS b J hJ Φ hΦ y hy).1]
    exact ⟨(hOF P.k P.r Wp Wq D (Θ a) (hO a).1 (hO a).2.1 _ hwb.1).2, (hS a _ hwb.1 _ hΦ' x hx).2⟩
  have hJw := (hWF Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hr s hD J hJ)
  have hlhs : resG P.k P.r (Fin.last P.r) (wvG D.z D.z' s J) x.1 x.2 =
      ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    rw [hJw.2 x hx, hWv, hΦ x hx]
  have hmain := congrArg (fun E : Pr (RadSp P.k P.r D.z D.z' D.π D.π') =>
    ((E.1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) halg
  have hsplit : ((star (thR L st Y 0) * mkP Wv Wv' * thR L st Y 1 -
      star (thR L st Y 2) * mkP Wv Wv' * thR L st Y 3).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      ((star (thR L st Y 0) * mkP Wv Wv' * thR L st Y 1).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 -
      ((star (thR L st Y 2) * mkP Wv Wv' * thR L st Y 3).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    rfl
  have hright : ((algebraMap ℂ (Pr (RadSp P.k P.r D.z D.z' D.π D.π')) s * mkP Wv Wv').1 Φ :
      Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = s • ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    rfl
  rw [hsplit, hright] at hmain
  apply smul_right_injective (Wq →L[ℂ] Wp) hw0
  simp only
  rw [smul_sub, ← hres _ (hterm 0 1).1, ← hres _ (hterm 2 3).1, smul_comm w s, ← hres _ hJw.1, (hterm 0 1).2,
    (hterm 2 3).2, hlhs]
  exact hmain.symm

end Formalism.FourierDecayAlt.P.CutSE
