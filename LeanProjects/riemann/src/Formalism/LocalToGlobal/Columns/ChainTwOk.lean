import Formalism.LocalToGlobal.Columns.ChainTwL
import Formalism.LocalToGlobal.Columns.ChainOneOkF

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwOkG

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem twSurjG (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (h : AutY X R (i + 1)) (hs : h ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) :
    SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h := by
  obtain ⟨⟨hbar, hred⟩, hiff⟩ := reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2 hB i hi P hP h hs
  have hin : ocbInAt R i P.1 hbar :=
    @residueFieldUnfolding_claims_hold.1 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ hP) (ocbRanks_step hB.hm hi) hbar ((hiff hbar hred).1 H)
  exact liftFromResidueParabolicProduct_holds Ch sel mu cst m2 hB i hi P hP h hs hbar hred hin

theorem twNonVanG (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1 := by
  have h := (reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2 hB i hi P hP 1 (Subgroup.one_mem _)).2 1 (ocbIsRed_one P.1 (qOf P.1) _ _)
  refine h.2 ?_
  exact (@ocbNe_one (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))).2
    (@residueFieldUnfolding_claims_hold.2 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ hP) (ocbRanks_step hB.hm hi))

end TwOkG

section TwLat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem twInX_mem_std (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} (x : Sp E n) :
    Loc.inX E n c x ∈ stdAt E (n + c) P ↔ x ∈ stdAt E n P := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rwa [ciInX_apply, dif_pos (by simp)] at h1
  · intro h l
    rw [ciInX_apply]
    split_ifs with hl
    · exact h _
    · exact ⟨0, 1, one_notMem P, by simp⟩

theorem twPrX_le_Q (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) : Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JQ P q kj n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← twInX_mem_std P (c := c) (g x), ← hg]
  exact (hr'.1 _).trans (twInX_mem_std P x)

end TwLat

section TwOk

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical

variable (X) in

def TwDegOne (P : HeightOneSpectrum (𝓞 X.E)) : Prop := (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2

variable (X Pr R) in

def TwFinQ (sharp : Bool) : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → TwDegOne X P →
    {D : Quotient (twSetoid (Pr := Pr) (R := R) sharp j P) | ∃ h, Quotient.mk _ h = D ∧ TwBdd (Pr := Pr) j P h}.Finite

def TwNormDC (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h →
    ∃ h', SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' ∧ TwBdd (Pr := Pr) (i + 1) P.1 h' ∧ TwNF (Pr := Pr) (i + 1) P.1 h' ∧
      prCat (Pr := Pr) cst.sharp (i + 1) P.1 h' ≤ GLint X.E (R.N (i + 1)) P.1 ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h'

def TwChrQ (m2 : ℕ) : Prop :=
  (∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → TwNF (Pr := Pr) (i + 1) P.1 h → prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1 →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → TwChrOk Ch sel mu cst (i + 1) P h) ∧
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → TwChrOk Ch sel mu cst (m2 + 1) P 1

def TwZeroQ : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → GLint X.E (R.N 0) P.1 ≤ prCat (Pr := Pr) cst.sharp 0 P.1 1 ∧
    ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp 0 P.1) 1, chiInv Ch sel mu cst 0 P 1 r = 1

structure TwCstQ (G : ChGlob X R.m) : Prop where
  psi_add : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) →
    IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * y) →
      twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) (x + y) = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x * twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) y
  psi_int : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x : X.E, IntAt P.1 x → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) x = 1
  psi_ne : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) ((qOf P.1 : X.E)⁻¹) ≠ 1
  sq_sq : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → twSqrt P.1 ^ 2 = (qOf P.1 : X.K)
  weil : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (a : X.E) (b : ℤ), IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * a) →
    IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) →
      G.σ₀ (twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) a) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ (2 * R.m))
  xi0 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0

structure TwAnQ (m2 : ℕ) : Prop where
  deep : ∀ A' B', cst.A ≤ A' → cst.B ≤ B' → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
    ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)), TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe →
      E1at Ch sel mu { cst with A := A', B := B' } i P hal hbe = E1at Ch sel mu cst i P hal hbe
  psiSupp : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
      ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)
  psiInv : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * z i)) →
      PsiAt Ch sel mu cst m2 P hal x₀ (y' + z) = PsiAt Ch sel mu cst m2 P hal x₀ y'
  xiSupp : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x : HomE X.E (R.N i) (R.N (i + 1)),
      XiAt Ch sel mu cst i P hal hbe x ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l)
  xiInv : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x z : HomE X.E (R.N i) (R.N (i + 1)),
      (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
        XiAt Ch sel mu cst i P hal hbe (x + z) = XiAt Ch sel mu cst i P hal hbe x
  psiSuppX : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
      ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x₀ (Pi.single s 1) l)
  psiInvX : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
    ∀ (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
      (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
        PsiAt Ch sel mu cst m2 P hal (x₀ + z) y' = PsiAt Ch sel mu cst m2 P hal x₀ y'

variable {Ch sel mu cst}

theorem twBdd_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : TwBdd (Pr := Pr) (R := R) j P 1 := fun x hx => by
  refine ⟨by simpa using hx, ?_⟩
  have e : ((qOf P : X.E) ^ j) = algebraMap (𝓞 X.E) X.E ((qOf P : 𝓞 X.E) ^ j) := by simp
  rw [e, algebraMap_smul]
  exact Submodule.smul_mem _ _ (by simpa using hx)

theorem twNormAt_of' {m2 : ℕ} (hN : TwNormDC Ch sel mu cst m2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) {i : ℕ} (hi : i < m2)
    (hsrc : ∀ (al : (twSt Ch sel mu cst m2 i).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P) ∧ TwNF (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P)) :
    TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i) := by
  intro P D hD
  obtain ⟨h, hhD, hb, al, hal⟩ := hD
  have hP := (Finset.mem_sdiff.1 P.2).2
  obtain ⟨h', hs, hb', hnf, hint, hal'⟩ := hN i hi (twRow P) hP (hd (twRow P) hP) _ h (hsrc al (twRow P) hP).1 (hsrc al (twRow P) hP).2 hb hal
  refine ⟨h', ?_, ⟨hb', al, hal'⟩, hnf, hint⟩
  rw [← hhD]
  exact (Quotient.sound hs).symm

theorem twSt_cand {m2 i : ℕ} (hi : i + 1 ≤ m2) (hN : TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i))
    (b : (twSt Ch sel mu cst m2 (i + 1)).β) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    TwBdd (Pr := Pr) (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ∧
      TwNF (Pr := Pr) (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ∧
      (∃ al : (twSt Ch sel mu cst m2 i).β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P ((twSt Ch sel mu cst m2 i).h al P) ((twSt Ch sel mu cst m2 (i + 1)).h b P)) ∧
      prCat (Pr := Pr) cst.sharp (i + 1) P.1 ((twSt Ch sel mu cst m2 (i + 1)).h b P) ≤ GLint X.E (R.N (i + 1)) P.1 := by
  revert b
  rw [twSt_succ_le Ch sel mu cst hi]
  intro b
  obtain ⟨-, ⟨hb, al, hal⟩, hnf, hint⟩ := twNext_spec hN b ⟨P.1, tw_mem_QOff hP⟩
  exact ⟨hb, hnf, ⟨al, hal⟩, hint⟩

theorem twNF_one_zero {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) : TwNF (Pr := Pr) (R := R) 0 P 1 := by
  refine ⟨fun _ => 0, 0, fun _ => ⟨by simp, le_refl _⟩, zero_mem _, fun v => ?_⟩
  have hl : lamYat (Pr := Pr) (R := R) 0 P = LocE.lamY P (qOf P) (R.N 0) (cOf R 0) 0 := by
    unfold lamYat
    rw [if_neg hP]
  rw [inv_one]
  show v ∈ _ ↔ _
  rw [hl]
  unfold LocE.lamY
  rw [ciMem_sclLat]
  constructor
  · intro h
    refine ⟨fun l => ?_, fun i => ?_⟩
    · have h1 := h (Fin.castAdd _ l)
      simp only [Fin.val_castAdd, LocE.scE, if_pos l.2, zpow_zero, inv_one, one_mul] at h1
      simpa using h1
    · have h1 := h (Fin.natAdd _ i)
      simp only [Fin.val_natAdd, LocE.scE] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ l
    refine Fin.addCases (fun l => ?_) (fun i => ?_) l
    · have := h1 l
      simp only [Fin.val_castAdd, LocE.scE, if_pos l.2, zpow_zero, inv_one, one_mul]
      simpa using this
    · have := h2 i
      simp only [Fin.val_natAdd, LocE.scE]
      simpa using this

theorem twNormAt_all {m2 : ℕ} (hN : TwNormDC Ch sel mu cst m2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)
  | 0, hi => twNormAt_of' hN hd hi fun _ P hP => ⟨twBdd_one 0 P.1, twNF_one_zero hP⟩
  | i + 1, hi => twNormAt_of' hN hd hi fun al P hP =>
      have H := twSt_cand (by omega) (twNormAt_all hN hd i (by omega)) al P hP
      ⟨H.1, H.2.1⟩

theorem twSt_of_twNormAt {m2 : ℕ} (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ i, i < m2 → ∀ (al : (twSt Ch sel mu cst m2 i).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P) ∧ TwNF (Pr := Pr) i P.1 ((twSt Ch sel mu cst m2 i).h al P)
  | 0, _, _, P, hP => ⟨twBdd_one 0 P.1, twNF_one_zero hP⟩
  | i + 1, hi, al, P, hP =>
      have H := twSt_cand (by omega) (hN i (by omega)) al P hP
      ⟨H.1, H.2.1⟩

theorem twSt_bdd {m2 : ℕ} (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) j P.1 ((twSt Ch sel mu cst m2 j).h b P)
  | 0, _, P, _ => twBdd_one 0 P.1
  | i + 1, b, P, hP => by
      by_cases h1 : i + 1 ≤ m2
      · exact (twSt_cand h1 (hN i (by omega)) b P hP).1
      · revert b
        by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _; exact twBdd_one _ _
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

theorem twJat_Q (sharp : Bool) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    Jat (Pr := Pr) (R := R) sharp j P = LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j) := by
  unfold Jat
  rw [if_neg hP]

theorem twSt_int {m2 : ℕ} (hs : cst.sharp = true) (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu),
      prCat (Pr := Pr) cst.sharp j P.1 ((twSt Ch sel mu cst m2 j).h b P) ≤ GLint X.E (R.N j) P.1 := by
  intro j b P
  by_cases hG : P.1 ∈ Pr.vGs
  · rw [twSt_h_g Ch sel mu cst m2 j b P hG, hs]
    show Loc.prX (Loc.Cbe (Jat (Pr := Pr) true j P.1) 1) ≤ _
    rw [ookJat j hG]
    exact ookPrX_le
  · have h1 : ∀ b' : (twSt Ch sel mu cst m2 j).β, (twSt Ch sel mu cst m2 j).h b' P = 1 →
        prCat (Pr := Pr) cst.sharp j P.1 ((twSt Ch sel mu cst m2 j).h b' P) ≤ GLint X.E (R.N j) P.1 := fun b' e => by
      rw [e]
      show Loc.prX (Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) 1) ≤ _
      rw [twJat_Q _ j hG]
      exact twPrX_le_Q _ _ _ _ _
    cases j with
    | zero => exact h1 b rfl
    | succ i =>
      by_cases h2 : i + 1 ≤ m2
      · exact (twSt_cand h2 (hN i (by omega)) b P hG).2.2.2
      · revert b h1
        by_cases h3 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h2, if_pos h3]]
          intro b h1; exact h1 b rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h2, if_neg h3]]
          intro b; exact b.elim

end TwOk

end Formalism.L2.Col
