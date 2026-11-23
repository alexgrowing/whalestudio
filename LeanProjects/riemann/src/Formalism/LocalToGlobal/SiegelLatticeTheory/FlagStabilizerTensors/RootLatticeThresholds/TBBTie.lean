import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UniformTheoremBOfLocalFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TopLevelBesselOfHypothesis
import Formalism.HermitianCurvature.StatementTBB

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def parOfL {k r : ℕ} (L : LocBessel k r) (u u' : ℕ → ℝ) : Formalism.FourierDecayAlt.M.Par :=
  ⟨k, r, Tz k r L.z, Tz k r L.z', u, u'⟩

def PlTie {k r : ℕ} (L : LocBessel k r) {u u' : ℕ → ℝ} (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) : Prop :=
  p.T.base.z = L.z ∧ p.T.base.z' = L.z' ∧ p.T.base.π = L.π ∧ p.T.base.π' = L.π' ∧ p.T.base.μW = L.μW ∧
    p.T.base.μN = L.μN ∧ p.T.base.μW' = L.μW'

def WeightTie : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)), 1 ≤ k →
    ptWeight k r T T' p = Formalism.FourierDecayAlt.TBB.nPt k r (T * T') (p.1.map Prod.swap)

def EnergyTie : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u u' : ℕ → ℝ)
    (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq), 1 ≤ k → L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → PlTie L p →
    IsKFinCoefH L.σ f → Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f → IsSection k r L.z L.z' μsec →
    Formalism.FourierDecayAlt.TBB.jN2 p f ≤ ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jNorm2 L f μsec

def CoefCC1 (Cgc : ℝ) : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsKFinCoefH L.σ f →
    GapAtLeast L.ε L.lam (Cgc * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) →
    Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f

def ThmBpTied (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C₄ : ℝ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS →
    ∃ (u u' : ℕ → ℝ) (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) (n₀ p₀ : ℕ),
      PlTie L p ∧ 2 * p₀ + n₀ ≤ A ∧ Formalism.FourierDecayAlt.TBB.ThmBpAt p f b C₄ n₀ p₀

theorem tieTopXk (k r : ℕ) (hk : 1 ≤ k) (L : LocBessel k r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat k r) :
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 F →
        0 < Gpt (Tz k r L.z) (Tz k r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact topLevelBesselHypothesis k0 r L Ds ν' m₀

theorem pc_le (r : ℕ) (s : List ℕ) : Formalism.MainNotions.BigCellDensity.pc r s ≤ (r + 1) ^ 2 := by
  unfold Formalism.MainNotions.BigCellDensity.pc
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem exists_relrep {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (h : orbSq L F γ ≠ 0) : ∃ g, IsPtRep L γ g ∧ IsRelStab L g := by
  by_contra hne
  apply h
  unfold orbSq
  refine le_antisymm ?_ bot_le
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  exact (hne ⟨g, hg.1, hg.2.1⟩).elim

theorem ew_top {P : Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (F : Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.C.LPt)
    (hγ : Formalism.FourierDecayAlt.D.IsLocPt γ (P.r + 1)) (hn : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ) :
    Formalism.FourierDecayAlt.TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ =
      Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ) (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
  unfold Formalism.FourierDecayAlt.TBB.Ew Formalism.FourierDecayAlt.TBB.NP Formalism.FourierDecayAlt.KB.Pl.RR Formalism.FourierDecayAlt.D.RRplace
  rw [dif_pos ⟨hγ, hγ⟩, dif_neg (by omega), if_pos rfl, if_pos rfl]
  simp only [Formalism.FourierDecayAlt.TBB.normC, List.map_nil, List.prod_nil, div_one, Real.mul_self_sqrt hn,
    Complex.re_ofReal_mul]

def BpLoc1N (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ^ A) * jNorm2 L f μsec

def NScale1 : Prop :=
  ∀ (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ), BpLoc1N D Ch Cg dist dinf A C e → BpLoc1 D Ch Cg dist dinf A C e

theorem theoremB_expansion_bound {r A e n' : ℕ} {b C₄ G Pc nn VV Ew : ℝ} {jN jR : ENNReal}
    (hb2 : 2 ≤ b) (he : 4 ≤ e) (hC4 : 0 ≤ C₄) (hG : 0 < G) (hn : 0 ≤ nn) (hPc0 : 0 ≤ Pc)
    (hPc : Pc ≤ Real.pi ^ (2 * (2 * r + 2) ^ 2)) (hA' : n' ≤ A) (hEw : Ew = nn * VV)
    (hB : ENNReal.ofReal Ew ≤ ENNReal.ofReal (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n') * jN)
    (hJ : jN ≤ ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jR) :
    ENNReal.ofReal nn * ENNReal.ofReal (Pc * VV) ≤
      ENNReal.ofReal (b ^ ((C₄ + 8) * ((2 * r + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / G) ^ A) * jR := by
  have hb0 : (0:ℝ) < b := by linarith
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hX1 : (1:ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)
  have hX4e : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ e := pow_le_pow_right₀ hX1 he
  have hX2e : ((2 * r + 2 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ e := pow_le_pow_right₀ hX1 (by omega)
  have hP0 : (0:ℝ) ≤ Real.pi ^ (2 * (2 * r + 2) ^ 2) := by positivity
  have hPP : Real.pi ^ (2 * (2 * r + 2) ^ 2) * Real.pi ^ (2 * (2 * r + 2) ^ 2) ≤
      b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
    have h1 : Real.pi ^ (2 * (2 * r + 2) ^ 2) * Real.pi ^ (2 * (2 * r + 2) ^ 2) ≤
        (b ^ 2) ^ (4 * (2 * r + 2) ^ 2) := by
      rw [← pow_add, show 2 * (2 * r + 2) ^ 2 + 2 * (2 * r + 2) ^ 2 = 4 * (2 * r + 2) ^ 2 by ring]
      apply pow_le_pow_left₀ Real.pi_pos.le
      nlinarith [Real.pi_le_four]
    calc _ ≤ (b ^ 2) ^ (4 * (2 * r + 2) ^ 2) := h1
      _ = b ^ (((8 * (2 * r + 2) ^ 2 : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast, ← pow_mul]; ring_nf
      _ ≤ b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1
          push_cast at hX2e ⊢
          linarith
  have hB1 : (0:ℝ) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := (Real.rpow_pos_of_pos hb0 _).le
  have hG0 : (0:ℝ) ≤ G⁻¹ ^ n' := pow_nonneg (inv_nonneg.mpr hG.le) _
  have hBnn : (0:ℝ) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n' := mul_nonneg hB1 hG0
  have hM1 : (1:ℝ) ≤ max 1 (1 / G) := le_max_left _ _
  have hGM : G⁻¹ ^ n' ≤ max 1 (1 / G) ^ A := by
    calc G⁻¹ ^ n' ≤ max 1 (1 / G) ^ n' := by
          apply pow_le_pow_left₀ (inv_nonneg.mpr hG.le)
          rw [one_div]; exact le_max_right _ _
      _ ≤ max 1 (1 / G) ^ A := pow_le_pow_right₀ hM1 hA'
  have hbC : b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ e) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_left hX4e hC4)
  have hreal : Pc * (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n') * Real.pi ^ (2 * (2 * r + 2) ^ 2) ≤
      b ^ ((C₄ + 8) * ((2 * r + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / G) ^ A := by
    have hsplit : b ^ ((C₄ + 8) * ((2 * r + 2 : ℕ) : ℝ) ^ e) =
        b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
      rw [← Real.rpow_add hb0]; ring_nf
    rw [hsplit]
    have hPcP : Pc * Real.pi ^ (2 * (2 * r + 2) ^ 2) ≤ b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) :=
      le_trans (mul_le_mul_of_nonneg_right hPc hP0) hPP
    have hE8 : (0:ℝ) ≤ b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) := (Real.rpow_pos_of_pos hb0 _).le
    have hEC : (0:ℝ) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ e) := (Real.rpow_pos_of_pos hb0 _).le
    calc Pc * (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n') * Real.pi ^ (2 * (2 * r + 2) ^ 2)
        = (Pc * Real.pi ^ (2 * (2 * r + 2) ^ 2)) * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n' := by ring
      _ ≤ b ^ (8 * ((2 * r + 2 : ℕ) : ℝ) ^ e) * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ e) *
            max 1 (1 / G) ^ A :=
          mul_le_mul (mul_le_mul hPcP hbC hB1 hE8) hGM hG0 (mul_nonneg hE8 hEC)
  have hL : ENNReal.ofReal nn * ENNReal.ofReal (Pc * VV) = ENNReal.ofReal Pc * ENNReal.ofReal Ew := by
    rw [← ENNReal.ofReal_mul hn, ← ENNReal.ofReal_mul hPc0, hEw]
    congr 1; ring
  rw [hL]
  calc ENNReal.ofReal Pc * ENNReal.ofReal Ew
      ≤ ENNReal.ofReal Pc * (ENNReal.ofReal (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n') *
          (ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jR)) :=
        by gcongr; exact hB.trans (by gcongr)
    _ = ENNReal.ofReal (Pc * (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n') *
          Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jR := by
        rw [ENNReal.ofReal_mul (mul_nonneg hPc0 hBnn), ENNReal.ofReal_mul hPc0]; ring
    _ ≤ _ := by gcongr

theorem pointWeight_eq_blockWeight (k r : ℕ) (T T' GG : ℝ) (hk : 1 ≤ k) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ b ∈ bs, 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
    (∀ x, bs.getLast? = some x → GG = Complex.normSq x.1 - T * T') →
    ptWeightFrom k r T T' a bs = Formalism.FourierDecayAlt.C.nAux k r GG (fun _ _ => 1) (a + 1) (bs.map Prod.swap)
  | [], a, _, _, _ => by simp [ptWeightFrom, Formalism.FourierDecayAlt.C.nAux]
  | (t, s) :: bs, a, hs, hsum, hlast => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hsum' : a + (s + (bs.map Prod.snd).sum) = r + 1 := by simpa using hsum
    have ih := pointWeight_eq_blockWeight k r T T' GG hk bs (a + s) (fun b hb => hs b (by simp [hb])) (by omega)
      (fun x hx => hlast x (by rw [List.getLast?_cons, hx]; rfl))
    simp only [ptWeightFrom, List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.C.nAux]
    rw [show a + 1 + s = a + s + 1 by omega, ← ih]
    congr 1
    by_cases hc : s = 1 ∧ a + 1 = r + 1
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩]
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons b bs' =>
          have := hs b (by simp)
          simp only [List.map_cons, List.sum_cons] at hsum'
          omega
      subst hbs
      obtain ⟨rfl, -⟩ := hc
      rw [hlast (t, 1) (by simp)]
    · rw [if_neg hc, if_neg (by omega), one_mul, show a + s + 1 - 1 = a + s by omega]
      have hle : a + s ≤ r + 1 := by omega
      have hexp : (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (a + s) + s - 3)) =
          ((2 * s * (Ml k r (a + s) + s - 3) : ℕ) : ℤ) := by
        unfold Formalism.FourierDecayAlt.C.Mlev Ml
        have h3 : 3 ≤ 2 * (r + 1 - (a + s)) + k + 1 + s := by omega
        push_cast [h3, Nat.sub_add_cancel hle]
        have e2 : ((r + 1 - (a + s) : ℕ) : ℤ) = (r : ℤ) + 1 - ((a + s : ℕ) : ℤ) := by omega
        rw [e2]
        push_cast
        ring
      rw [hexp, zpow_natCast]

theorem weightTie : WeightTie := by
  intro k r T T' p hk
  unfold ptWeight Formalism.FourierDecayAlt.TBB.nPt
  refine pointWeight_eq_blockWeight k r T T' _ hk p.1 0 (fun b hb => (p.2.1 b hb).2)
    (by rw [p.2.2, Nat.zero_add]) ?_
  intro x hx
  simp [Formalism.FourierDecayAlt.D.ptGG, Formalism.FourierDecayAlt.D.ptLast, List.getLast?_map, hx]

theorem bpLoc1_of_tbb {D : D7} {Ch Cg dist dinf C₄ Cgc : ℝ} {A e : ℕ} (hCg : 2 ≤ Cg) (he : 4 ≤ e) (hC4 : 0 ≤ C₄)
    (hgap : Cgc * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) ≤
      Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) -
        2 * dinf)
    (hW : WeightTie) (hE : EnergyTie) (hCC : CoefCC1 Cgc) (hT : ThmBpTied D Ch Cg dist dinf A C₄) :
    BpLoc1N D Ch Cg dist dinf A (C₄ + 8) e := by
  intro b v L f μsec hok hμN p hGp
  obtain ⟨u, u', pl, n₀, p₀, htie, hA, hbp⟩ := hT b v L f μsec hok hμN
  by_cases h0 : orbSq L f p = 0
  · rw [h0, mul_zero]; exact bot_le
  by_cases hn0 : ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p < 0
  · rw [ENNReal.ofReal_of_nonpos hn0.le, zero_mul]; exact bot_le
  push_neg at hn0
  obtain ⟨g, hrep, hstab⟩ := exists_relrep L f p h0
  have hGpos : 0 < Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p :=
    lt_of_le_of_ne (Formalism.MainNotions.BesselShellMomentBounds.GPoint_nonneg_of_rep L p g hrep) (Ne.symm hGp)
  obtain ⟨hLoc, -, hdinf, hKfin, hsec⟩ := hok
  obtain ⟨hk, -, hc, hκ, hκ', hstd, -, -⟩ := hLoc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlamb, -, -, hall, hgap0, -, -⟩ := hstd
  have hcStd : L.c = cStd := by rw [hc]; simp [cOfDpsi, cStd]
  have hX3 : (8:ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by
    have h2 : (2:ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * D.R.rS + 2)
    calc (8:ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 3
  have hb2 : 2 ≤ b := by
    have hn : 1 < 2 * D.R.rS + D.R.k + 1 := by omega
    have hg := hall ⟨0, by omega⟩ ⟨1, hn⟩ (by simp [Fin.ext_iff])
    have h1 := abs_le.mp (hlamb ⟨0, by omega⟩)
    have h2 := abs_le.mp (hlamb ⟨1, hn⟩)
    have h3 : |lamSH D.R (D.hc v) ⟨0, by omega⟩ - lamSH D.R (D.hc v) ⟨1, hn⟩| ≤ 2 * b :=
      abs_le.mpr ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
    nlinarith [hX3, hCg]
  have hInCC : Formalism.FourierDecayAlt.B.InCC (A0 D.R.k D.R.rS) 1 f := by
    apply hCC D.R.k D.R.rS L f hk hKfin
    intro a a' hne
    have h0' := hgap0 a a' hne
    have ha := abs_le.mp (hdinf a)
    have ha' := abs_le.mp (hdinf a')
    have e1 := le_abs_self (L.lam a - L.lam a')
    have e2 := neg_abs_le (L.lam a - L.lam a')
    have h5 : |lamSH D.R (D.hc v) a - lamSH D.R (D.hc v) a'| ≤ |L.lam a - L.lam a'| + 2 * dinf :=
      abs_le.mpr ⟨by linarith [ha.1, ha.2, ha'.1, ha'.2], by linarith [ha.1, ha.2, ha'.1, ha'.2]⟩
    linarith
  have htie' := htie
  obtain ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩ := htie'
  have horb := tieTopXk D.R.k D.R.rS hk L pl.T.base pl.ν' pl.m₀ hcStd hκ hκ' hz hz' hπ hπ' hμW hμN' hμW'
    pl.hF f p hKfin hInCC hGpos ⟨g, hrep, hstab⟩
  have hTT : Formalism.FourierDecayAlt.TBB.TTp pl = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold Formalism.FourierDecayAlt.TBB.TTp
    rw [hz, hz'] <;> rfl
  have hloc : Formalism.FourierDecayAlt.D.IsLocPt (p.1.map Prod.swap) (D.R.rS + 1) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨(p.2.1 y hy).2, (p.2.1 y hy).1⟩
    · unfold Formalism.FourierDecayAlt.D.ptSize
      rw [List.map_map]
      have hfs : (Prod.fst ∘ Prod.swap : ℂ × ℕ → ℕ) = Prod.snd := rfl
      rw [hfs]
      exact p.2.2
  have hGeq : Formalism.FourierDecayAlt.TBB.Gp pl (p.1.map Prod.swap) = Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p := by
    unfold Formalism.FourierDecayAlt.TBB.Gp
    rw [hTT]
    show Formalism.FourierDecayAlt.D.ptG (Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z') D.R.rS (p.1.map Prod.swap) = _
    exact Formalism.MainNotions.BigCellDensity.ptG_eq_GPoint _ _ p
  have hGp' : 0 < Formalism.FourierDecayAlt.TBB.Gp pl (p.1.map Prod.swap) := by rw [hGeq]; exact hGpos
  have hw := weightTie D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p hk
  have hn : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z')
      (p.1.map Prod.swap) := by rw [← hw]; exact hn0
  have hn' : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt (parOfL L u u').k (parOfL L u u').r (Formalism.FourierDecayAlt.TBB.TTp pl)
      (p.1.map Prod.swap) := by rw [hTT]; exact hn
  have hEw := ew_top pl f (p.1.map Prod.swap) hloc hn'
  have hB := hbp (p.1.map Prod.swap) hloc hGp'
  rw [hGeq] at hB
  have hJ := hE D.R.k D.R.rS L f μsec u u' pl hk hcStd hκ hκ' htie hKfin hInCC hsec
  have hPc : Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc D.R.rS (p.1.map Prod.snd)) ≤
      Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) := by
    apply pow_le_pow_right₀ (by linarith [Real.pi_gt_three])
    have h1 := pc_le D.R.rS (p.1.map Prod.snd)
    have h2 : (D.R.rS + 1) ^ 2 ≤ (2 * D.R.rS + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    linarith
  rw [horb, hw]
  rw [hTT] at hEw
  exact theoremB_expansion_bound hb2 he hC4 hGpos hn (by positivity) hPc hA hEw hB hJ

def TheoremBLocalExpansion : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C₄ CA Cinf Cgf Cgc Cg₀ : ℝ), 2 ≤ Cg₀ ∧ 0 ≤ C₄ ∧
    (∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) ∧ CoefCC1 Cgc ∧
    ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        ThmBpTied D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C₄

theorem theoremBLocal_of_energy (hNS : NScale1) (hE : EnergyTie) (h : TheoremBLocalExpansion) : BesselExpansionLocalFrame := by
  intro Aw Ch hAw
  obtain ⟨C1, C₄, CA, Cinf, Cgf, Cgc, Cg₀, hCg₀, hC4, hOB, hCC, hmain⟩ := h Aw Ch hAw
  refine ⟨C1, C₄ + 8, CA, Cinf, Cgf, max Cg₀ (Cgc + 2 * |Cinf|), le_trans hCg₀ (le_max_left _ _), hOB, ?_⟩
  intro Cg hCg D
  obtain ⟨dist', A, hA, hQ, hT⟩ := hmain Cg (le_trans (le_max_left _ _) hCg) D
  refine ⟨dist', A, hA, hQ, hNS D Ch Cg dist' _ A (C₄ + 8) 5 ?_⟩
  refine bpLoc1_of_tbb (le_trans hCg₀ (le_trans (le_max_left _ _) hCg)) (by norm_num) hC4 ?_ weightTie hE hCC hT
  have hd : 2 * |Cinf| ≤ Cg - Cgc := by linarith [le_trans (le_max_right Cg₀ (Cgc + 2 * |Cinf|)) hCg]
  have hX : (2:ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * D.R.rS + 2)
  have hX30 : (0:ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by positivity
  have hX3 : ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h1 : (1:ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1)
  have hQ1 : (1:ℝ) ≤ ((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
      ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3 := by
    have h3 : (1:ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ h1
    have h4 : (0:ℝ) ≤ ((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have ha0 : 0 ≤ Cg - Cgc := le_trans (by positivity) hd
  have hY0 : (0:ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := le_trans hX30 hX3
  have s1 : (Cg - Cgc) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) ≤
      (Cg - Cgc) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
          ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) :=
    le_mul_of_one_le_right (mul_nonneg ha0 hY0) hQ1
  have s2 : (Cg - Cgc) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 ≤
      (Cg - Cgc) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hX3 ha0
  have s3 : 2 * Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 ≤ (Cg - Cgc) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cinf]) hX30
  nlinarith [s1, s2, s3]

theorem weighted_uniform_rotated_of_expansion_alt (hNS : NScale1) (hE : EnergyTie) (h : TheoremBLocalExpansion) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform := uniformTheoremB_of_local_frame (theoremBLocal_of_energy hNS hE h)

end Formalism.L2.SG.Pf.BesselExpansion
