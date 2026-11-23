import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.PrimStep

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def OpCl {R : Type} [CommRing R] {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) : Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ f ∈ M, ∃ l : List (Fin n' × (Fin k × Fin k)), (∀ z ∈ l, z.1 ∈ TT) ∧
    (∀ s, (l.filter fun z => z.1 = s).length ≤ c) ∧ y = opWord l f}

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def SgOp (c0 : ℕ) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
    Submodule (KK O) (MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) :=
  OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))))

def CloudBAt (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ κ : ℕ, (κ : ℝ) ≤ bK ∧
    ∀ (n2 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)), (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) →
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O,
          (∑ x, c x • S x) ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e) →
          ∃ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
            (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB ∧
            Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e ∧
            Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) ∧
            ∃ (Λ : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))) →ₗ[Kf] Module.Dual Kf (Vsp Kf lam0)) (cc : O),
              (∀ T, algebraMap O Kf cc * be p r lam0 (∑ x, c x • S x) (Λ T) =
                (p : Kf) ^ κ * be p r (flW (dT TT lam0)) (Θ F1) T) ∧
              (∀ T ∈ Re' p ι σ w r (flW (dT TT lam0)) e, Λ T ∈ Re' p ι σ w r lam0 e ∧
                be p r lam0 (∑ x, c x • S x) (Λ T) ∈ Set.range (algebraMap O Kf)) ∧
              (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ (i : ℤ),
                ∀ T ∈ scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW (dT TT lam0)) e'),
                  Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (Re' p ι σ w r lam0 e')) ∧
              (∀ (i : ℤ), ∀ T ∈ scale (algebraMap O Kf w ^ i)
                  (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)),
                Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)))

def FlatAt (c0 cP : ℕ) (bT bD : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ tF DF : ℕ, (tF : ℝ) ≤ bT ∧ (DF : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
        T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
        ValLe (p : O) DF (be p r (flW (dT TT lam0)) (Θ F1) T)

end At

def CloudBStep (C CK CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        CloudBAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def FlatStep (C Ct0 CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        FlatAt p n' ι σ w r TT lam0 c0 (cPrime n' r TT.card c0 cpp cStar)
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0)
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def RestCloudB (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudBStep C CK CLa

def RestFlat (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CDf C₁ : ℝ, 0 < Ct0 ∧ 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → FlatStep C Ct0 CDf CLa

theorem test_bound_of_two_halves (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hCl : RestCloudB D CLa Ck Crk Cdeg) (hFl : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨CK, C₂, hCK, hC2, hC⟩ := hCl hA
  obtain ⟨Ct0, CDf, C₃, h0, h1, hC3, hF⟩ := hFl hA h14a h14b
  refine ⟨Ct0, CK + CDf, max C₂ C₃, h0, by linarith, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨κ, hκ, hcl⟩ := hC C (le_trans (le_max_left _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨tF, DF, htF, hDF, hfl⟩ := hF C (le_trans (le_max_right _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0
    aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  refine ⟨tF + (r * TT.card * c0 + 2 * r * n' * cpp), κ + DF, ?_, ?_, ?_⟩
  · unfold om
    push_cast
    linarith
  · push_cast
    have e1 : (CK + CDf) * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a =
        CK * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a + CDf * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a := by
      ring
    push_cast at hκ hDF
    rw [e1]
    linarith
  intro n2 sh hsh S hS c hv
  obtain ⟨F1, f1, f2, f3, Λ, cc, l1, l2, l3, l4⟩ := hcl n2 sh hsh S hS c hv
  obtain ⟨T, t1, t2, t3, t4⟩ := hfl F1 f1 f2 f3
  refine ⟨Λ T, ?_, (l2 T t2).1, ?_, ?_⟩
  · have := l4 _ T t1
    convert this using 3
    push_cast
    ring
  · intro e' he' htg hne
    have := l3 e' he' htg _ T (t3 e' he' htg hne)
    convert this using 3
    unfold cPrime
    push_cast
    ring
  · obtain ⟨aa, haa⟩ := (l2 T t2).2
    obtain ⟨y, b', hy, hyb⟩ := t4
    refine ⟨aa, cc * b', haa.symm, ?_⟩
    have hinj : Function.Injective (algebraMap O Kf) := by
      have := hSet.1.frac_O
      exact IsFractionRing.injective O Kf
    apply hinj
    have h5 := l1 T
    rw [← haa, hy] at h5
    have : algebraMap O Kf (aa * (cc * b')) = (algebraMap O Kf cc * algebraMap O Kf aa) * algebraMap O Kf b' := by
      simp only [map_mul]; ring
    rw [this, h5, mul_assoc, ← map_mul, hyb]
    simp [pow_add]

end Formalism.MainNotions.TestSideCounting
