import Formalism.HermitianCurvature.HermitianCurvatureProofs.CellIdentityShifted

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def uPlus (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i

def uMinus (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i

structure WigData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {Wq : Type} [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ) (l n₀ : ℕ)
    (b : ℝ) where
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  πp : B.Mat k r → (Wqp →L[ℂ] Wqp)
  πm : B.Mat k r → (Wqm →L[ℂ] Wqm)
  Ap : B.Mat k r → (Wqp →L[ℂ] Wq)
  Am : B.Mat k r → (Wqm →L[ℂ] Wq)
  typeP : Q.IsType k r z' πp (uPlus u l n₀)
  typeM : Q.IsType k r z' πm (uMinus u l n₀)
  polyP : PolyOp (n₀ * (r + 1)) Ap
  polyM : PolyOp (n₀ * (r + 1)) Am
  equivP : WigEquiv z z' π' πp Ap
  equivM : WigEquiv z z' π' πm Am
  upperP : WigUpper z z' n₀ Ap
  upperM : WigUpper z z' n₀ Am
  lower : WigLower z z' b n₀ Ap Am

attribute [instance] WigData.iNp WigData.iIp WigData.iFp WigData.iNm WigData.iIm WigData.iFm

def WigExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Q.IsType k r z' π' u →
    (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) →
    1 ≤ l → l < k → (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1) → 3 ≤ b → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) →
    Nonempty (WigData k r z z' π' u l n₀ b)

def PlaceSwapExists : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (p : KB.Pl P Wp Wq) (u'' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ),
    Q.IsType P.k P.r p.T.base.z' π'' u'' → (shP P P.u u'').OK → 1 ≤ l0 → l0 ≤ P.k →
    ∃ q : KB.Pl (shP P P.u u'') Wp Wq', SwapTie p q ∧ q.T.base.π' = π'' ∧ q.l0 = l0

theorem okPlus (P : M.Par) (l n₀ : ℕ) (hOK : P.OK) (hu : P.u = P.u') (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1)) : (shP P P.u (uPlus P.u' l n₀)).OK := by
  have key : ∀ a b c d : ℝ, a + 1 ≤ c → a + 1 ≤ d → b + 1 ≤ c → b + 1 ≤ d →
      max a b + 1 / 2 ≤ min c d - 1 / 2 := by
    intro a b c d h1 h2 h3 h4
    have ha : a + 1 ≤ min c d := le_min h1 h2
    have hb : b + 1 ≤ min c d := le_min h3 h4
    have hm : max a b ≤ min c d - 1 := max_le (by linarith) (by linarith)
    linarith
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨n, hn⟩ := hOK.int_u' i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [shP, uPlus, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [shP, uPlus, if_neg h]
      exact hn
  · have hg := hOK.gap i hi
    simp only [Formalism.FourierDecayAlt.M.Par.lo, Formalism.FourierDecayAlt.M.Par.hi, shP, uPlus] at hg ⊢
    rw [hu] at hg ⊢
    simp only [max_self, min_self] at hg
    by_cases h1 : i = l
    · subst h1
      simp only [if_true, show ¬ (i = i + 1) by omega, if_false]
      exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases h2 : i = l + 1
      · subst h2
        simp only [show ¬ (l + 1 + 1 = l + 1) by omega, if_false, if_true]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
      · simp only [show ¬ (i + 1 = l + 1) by omega, if_false, if_neg h2]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

theorem okMinus (P : M.Par) (l n₀ : ℕ) (hOK : P.OK) (hu : P.u = P.u') (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1)) : (shP P P.u (uMinus P.u' l n₀)).OK := by
  have key : ∀ a b c d : ℝ, a + 1 ≤ c → a + 1 ≤ d → b + 1 ≤ c → b + 1 ≤ d →
      max a b + 1 / 2 ≤ min c d - 1 / 2 := by
    intro a b c d h1 h2 h3 h4
    have ha : a + 1 ≤ min c d := le_min h1 h2
    have hb : b + 1 ≤ min c d := le_min h3 h4
    have hm : max a b ≤ min c d - 1 := max_le (by linarith) (by linarith)
    linarith
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨n, hn⟩ := hOK.int_u' i hi
    by_cases h : i = l
    · refine ⟨n - n₀, ?_⟩
      simp only [shP, uMinus, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [shP, uMinus, if_neg h]
      exact hn
  · have hg := hOK.gap i hi
    simp only [Formalism.FourierDecayAlt.M.Par.lo, Formalism.FourierDecayAlt.M.Par.hi, shP, uMinus] at hg ⊢
    rw [hu] at hg ⊢
    simp only [max_self, min_self] at hg
    by_cases h1 : i = l
    · subst h1
      simp only [if_true, show ¬ (i + 1 = i) by omega, if_false]
      exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases h2 : i + 1 = l
      · subst h2
        simp only [show ¬ (i = i + 1) by omega, if_false, if_true]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
      · simp only [if_neg h1, if_neg h2]
        exact key _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

theorem shiftAtR_exists (hW : WigExists) (hPS : PlaceSwapExists) : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ l : ℕ) (A₀ : ℝ),
    (∀ i ∈ Finset.Ico 1 P.k, P.u' (i + 1) + 1 ≤ P.u' i) →
    1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1) → 3 ≤ b →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) →
    (shP P P.u (uPlus P.u' l n₀)).OK → (shP P P.u (uMinus P.u' l n₀)).OK →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∃ S : ShiftAtR p f b n₀, S.up = P.u ∧ S.up' = uPlus P.u' l n₀ ∧ S.um = P.u ∧ S.um' = uMinus P.u' l n₀ ∧
      S.pp.l0 = l + 1 ∧ S.pm.l0 = l := by
  obtain ⟨c₃, hc⟩ := shiftAtR_of_parts cell_identity_shifted
  refine ⟨c₃, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ l A₀ hdec hl1 hlk hposition hb hub hOKp hOKm hA hf
  obtain ⟨-, hz, hz', -, -, -, htype⟩ := p.hP
  obtain ⟨W⟩ := hW P.k P.r p.T.base.z p.T.base.z' Wq p.T.base.π' P.u' l n₀ b hz hz' p.T.base.T_pos
    p.T.base.T'_pos htype hdec hl1 hlk hposition hb hub
  obtain ⟨pp, hpT, hpπ, hpl⟩ := hPS P Wp Wq W.Wqp p (uPlus P.u' l n₀) W.πp (l + 1) W.typeP hOKp (by omega)
    (by omega)
  obtain ⟨pm, hmT, hmπ, hml⟩ := hPS P Wp Wq W.Wqm p (uMinus P.u' l n₀) W.πm l W.typeM hOKm hl1 (le_of_lt hlk)
  obtain ⟨S, h1, h2, h3, h4, h5, h6⟩ := hc P Wp Wq W.Wqp W.Wqm p f b n₀ A₀ P.u (uPlus P.u' l n₀) P.u
    (uMinus P.u' l n₀) pp pm W.Ap W.Am hpT hmT (hpπ ▸ W.equivP) (hmπ ▸ W.equivM) W.polyP W.polyM W.upperP
    W.upperM W.lower hA hf
  exact ⟨S, h1, h2, h3, h4, h5.trans hpl, h6.trans hml⟩

theorem shiftAtR_exists_eq (hW : WigExists) (hPS : PlaceSwapExists) : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ l : ℕ) (A₀ : ℝ),
    P.u = P.u' → 1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1) → 3 ≤ b →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∃ S : ShiftAtR p f b n₀, S.up = P.u ∧ S.up' = uPlus P.u' l n₀ ∧ S.um = P.u ∧ S.um' = uMinus P.u' l n₀ ∧
      S.pp.l0 = l + 1 ∧ S.pm.l0 = l := by
  obtain ⟨c₃, hc⟩ := shiftAtR_exists hW hPS
  refine ⟨c₃, fun P Wp Wq _ _ _ _ _ _ p f b n₀ l A₀ hu hl1 hlk hposition hb hbd hA hf => ?_⟩
  have hOK : P.OK := p.hP.1
  have hdec : ∀ i ∈ Finset.Ico 1 P.k, P.u' (i + 1) + 1 ≤ P.u' i := by
    intro i hi
    have hi' : i ∈ Finset.Icc 1 (P.k - 1) := by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
      omega
    have hg := hOK.gap i hi'
    simp only [Formalism.FourierDecayAlt.M.Par.lo, Formalism.FourierDecayAlt.M.Par.hi] at hg
    rw [hu] at hg
    simp only [max_self, min_self] at hg
    linarith
  exact hc P Wp Wq p f b n₀ l A₀ hdec hl1 hlk hposition hb hbd (okPlus P l n₀ hOK hu hl1 hlk hposition)
    (okMinus P l n₀ hOK hu hl1 hlk hposition) hA hf

end

end Formalism.FourierDecayAlt.P.CutBPEq
