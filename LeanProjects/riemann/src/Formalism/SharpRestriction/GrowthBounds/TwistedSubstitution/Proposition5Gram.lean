import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.PlaneCoeff

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def NSConcl (CH CE C6 C18 : ℝ) (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m : ℕ} (r : ℕ) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r] [NeZero K]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (cP κ DX : ℕ)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∃ (J : ℕ) (_ : NeZero J) (Dt : SignedChainData p O r J) (F2 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)),
    Dt.Hyp CH ∧ 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c ∧ Dt.XX F2 ∧ vBB (O := O) p F2 = 0 ∧
    ∀ Gp R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O),
      (∀ mo, geQ (vK p (Gp.coeff mo)) 0) → Dt.YY C6 C18 Gp →
      (∀ mo, geQ (vK p (R.coeff mo)) (Dt.c - Dt.EE CE)) →
      (∀ mo ∈ Gp.support ∪ R.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) →
      geQ (vBB (O := O) p (Dt.ph (Gp + R))) (Dt.n0 - Dt.kp) →
      leQ (vK p (Dt.Bform F2 (Dt.ph (Gp + R)))) (Dt.EE CE + 2 * Dt.kp + Dt.n0 - Dt.kp) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock G (∑ q, sig q) / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O))

theorem nsAt_of (CH CE C6 C18 : ℝ) (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r]
    [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (c0 cP κ : ℕ) (bD : ℝ)
    {nb : ℕ} (B : Fin nb → RRing O n' (r + K)) (DX : ℕ) (hDX : (DX : ℝ) ≤ bD)
    (h : ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => symP p O hk hrk Fr cP (p ^ G') (B b))) →
      HasMultideg G d → InWj w G 0 → ¬ InWj w G 1 →
      NSConcl CH CE C6 C18 p r d deg K hk Fr N₁ G' Y cP κ DX G) :
    NSAt CH CE C6 C18 p w r TT d deg K hk hrk Fr N₁ G' Y c0 cP κ bD B :=
  ⟨DX, hDX, h⟩

def DataII (C CLa : ℝ) (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (F : Frames n' r) (nb : ℕ) (B : Fin nb → RRing O n' (r + K)) : Prop :=
  UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w ∧
  Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar ∧
  FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F ∧
  (∃ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) ∧
    ∀ i, B i ∈ Gen O p K F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
      (G2d F (flatDeg lam0) E')) ∧
  LinearIndependent O B ∧ (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T)

def MemStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b =>
        symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))) →
      MemAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) G

def Proposition5At (C CD CLa CH CE C6 C18 : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∃ DX : ℕ, (DX : ℝ) ≤ CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b =>
        symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))) →
      HasMultideg G (dT TT lam0) → InWj w G 0 → ¬ InWj w G 1 →
      MemAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) G →
      NSConcl CH CE C6 C18 p r (dT TT lam0) (flatDeg lam0) K hk F (orbitWindowCount r de h x) (goodG' r de h x) Y
        (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0)) DX G

theorem nsStep_of (C CD CLa CH CE C6 C18 : ℝ) (hM : MemStep C CLa) (hP : Proposition5At C CD CLa CH CE C6 C18) :
    NSStep C CD CLa CH CE C6 C18 := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K
    _ _ hk hrk F hF E' hE' nb B hB hli hc
  have hD : DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B :=
    ⟨hSet, H, hF, ⟨E', hE', hB⟩, hli, hc⟩
  obtain ⟨DX, hDX, hP'⟩ := hP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
  exact nsAt_of CH CE C6 C18 p w r TT (dT TT lam0) (flatDeg lam0) K hk hrk F _ _ Y c0 _ _ _ B DX hDX
    fun G h1 h2 h3 h4 => hP' G h1 h2 h3 h4
      (hM p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD G h1)

def RestMEM (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → MemStep C CLa

def Proposition5Gram (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → Proposition5At C CDf CLa CH CE C6 C18

theorem restNS_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hM : RestMEM D CLa Ck Crk Cdeg) (hP : Proposition5Gram D CLa Ck Crk Cdeg CH CE C6 C18) :
    RestNS D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA
  obtain ⟨C₁, h1, hM'⟩ := hM hA
  obtain ⟨CDf, C₂, h2, h3, hP'⟩ := hP hA
  refine ⟨CDf, max C₁ C₂, h2, lt_max_of_lt_left h1, fun C hC => ?_⟩
  exact nsStep_of C CDf CLa CH CE C6 C18 (hM' C (le_trans (le_max_left _ _) hC)) (hP' C (le_trans (le_max_right _ _) hC))

end Formalism.MainNotions.TestSideWords
