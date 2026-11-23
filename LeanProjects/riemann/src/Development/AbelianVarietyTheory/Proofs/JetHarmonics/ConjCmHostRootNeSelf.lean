import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LongGeneratorWeights
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormGeneratorIffPrincipal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.LongGeneratorWeights

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

def NoBaseRows (T : Top D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, ThetaWt D w →
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → WeightAlgebra.DF w + 2 ≤ qq D → T.Q.l.Mb.IsPrincipal →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
      ∃ f ∈ T.C j w,
        (∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
          (P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
            ∀ σ' : T.Q.c.F →+* ℂ, l1At σ' P ≤ Real.exp (140 * D.R.r * large₂.sc.L * WeightAlgebra.DF w)) ∧
          IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f) ∧ NeZeroOn T j σ k f

theorem wt_ext {j : ℕ} {w w' : WeightFamilies.Wt D j} (h1 : w.aP = w'.aP) (h2 : w.aM = w'.aM) (h3 : w.n = w'.n) : w = w' := by
  cases w; cases w'; simp_all

def WeightsExist : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j)
    (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    Formalism.MainNotions.Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 →
    (∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2) ∧ (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW)

theorem anti_nonneg {p : ℕ} (g : Fin p → ℤ) (h1 : ∀ (i : Fin p) (h : i.1 + 1 < p), g ⟨i.1 + 1, h⟩ ≤ g i)
    (h2 : ∀ i : Fin p, i.1 + 1 = p → 0 ≤ g i) : Antitone g ∧ ∀ i, 0 ≤ g i := by
  cases p with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    have ha : Antitone g := Fin.antitone_iff_succ_le.2 fun i => h1 i.castSucc (by simp)
    exact ⟨ha, fun i => (h2 (Fin.last n) rfl).trans (ha (Fin.le_last i))⟩

theorem div_step (a c q T' : ℤ) (hp : 0 < T') (hc : c ≤ T') (ha : T' * T' ≤ a - c)
    (hq : q = Int.fdiv (a - c) T') : a ≤ (T' + 2) * q := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le] at hq
  have h1 : a - c < (q + 1) * T' := by rw [hq]; exact Int.lt_ediv_add_one_mul_self _ hp
  have h2 : T' ≤ q := by
    by_contra hlt
    have h3 : q + 1 ≤ T' := by omega
    nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
  nlinarith

theorem block {p : ℕ} (a l : Fin p → ℕ) (Dm T r c : ℕ) (h40 : 40 * (Dm + 2) ≤ T) (hc : c ≤ T)
    (hgap : ∀ i : Fin p, i.1 + 1 < p → (((T + Dm + 2) * ((T + Dm + 2) + 2 * r) : ℕ) : ℤ) ≤ gapZ a i + 2)
    (hlast : ∀ i : Fin p, i.1 + 1 = p → 2 * T ^ 2 ≤ a i)
    (hL : ∀ i, gapZ l i = if i.1 + 1 < p then Int.fdiv (gapZ a i - (-2)) ((T + Dm + 2 : ℕ) : ℤ)
      else Int.fdiv ((a i : ℤ) - c) ((T + Dm + 2 : ℕ) : ℤ)) :
    Antitone (fun i => ((T : ℤ) + Dm + 4) * l i - a i) ∧ ∀ i, 0 ≤ ((T : ℤ) + Dm + 4) * l i - a i := by
  refine anti_nonneg _ (fun i h => ?_) (fun i h => ?_)
  · have e := hL i
    rw [if_pos h] at e
    have hg := hgap i h
    have := div_step (gapZ a i) (-2) (gapZ l i) ((T + Dm + 2 : ℕ) : ℤ) (by positivity) (by omega)
      (by push_cast at hg ⊢; nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ T + Dm + 2) (by positivity : (0 : ℤ) ≤ r)]) e
    simp only [gapZ, dif_pos h] at this
    push_cast at this
    nlinarith
  · have hn : ¬ i.1 + 1 < p := by omega
    have e := hL i
    rw [if_neg hn] at e
    simp only [gapZ, dif_neg hn] at e
    have hl : 2 * (T : ℤ) ^ 2 ≤ a i := by exact_mod_cast hlast i h
    have h40' : 40 * ((Dm : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have hc' : (c : ℤ) ≤ T := by exact_mod_cast hc
    have hD : (0 : ℤ) ≤ Dm := by positivity
    have hT0 : (0 : ℤ) ≤ T := by positivity
    have := div_step (a i) c (l i) ((T + Dm + 2 : ℕ) : ℤ) (by positivity) (by omega)
      (by push_cast
          nlinarith [mul_nonneg hT0 (sub_nonneg.2 h40'), mul_nonneg (by omega : (0 : ℤ) ≤ Dm + 2) (sub_nonneg.2 h40'),
            mul_nonneg hT0 (by omega : (0 : ℤ) ≤ T - 80)]) e
    push_cast at this
    linarith

end GlobalTheory.LeafCompare
