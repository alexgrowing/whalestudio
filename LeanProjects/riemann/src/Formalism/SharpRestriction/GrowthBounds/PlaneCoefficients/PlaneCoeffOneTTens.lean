import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlanePairsOnBlocksAt
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem coeff_sumSupp {σ R S : Type*} [CommSemiring R] [CommSemiring S] (F : MvPolynomial σ R) (g : R → S)
    (hg : g 0 = 0) (mo : σ →₀ ℕ) : (∑ x ∈ F.support, monomial x (g (F.coeff x))).coeff mo = g (F.coeff mo) := by
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have h0 : F.coeff mo = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    rw [h0, hg]

def tens {σ τ Kf : Type} [Field Kf] (A : MvPolynomial σ Kf) (G : MvPolynomial τ Kf) :
    MvPolynomial σ (MvPolynomial τ Kf) :=
  ∑ mo ∈ A.support, monomial mo (A.coeff mo • G)

theorem planeCoeff_oneT_tens {σ τ Kf : Type} [Field Kf] (e : Module.End Kf (MvPolynomial τ Kf)) (nu : τ →₀ ℕ)
    (A : MvPolynomial σ Kf) (G : MvPolynomial τ Kf) :
    planeCoeff nu (oneT e (tens A G)) = (e G).coeff nu • A := by
  ext mo
  have h1 : (tens A G).coeff mo = A.coeff mo • G := by
    unfold tens
    exact coeff_sumSupp A (fun a => a • G) (by simp) mo
  have h2 : ∀ T : MvPolynomial σ (MvPolynomial τ Kf), (oneT e T).coeff mo = e (T.coeff mo) := by
    intro T
    unfold oneT
    exact coeff_sumSupp T e (by simp) mo
  have h3 : ∀ X : MvPolynomial σ (MvPolynomial τ Kf), (planeCoeff nu X).coeff mo = (X.coeff mo).coeff nu := by
    intro X
    unfold planeCoeff
    exact coeff_sumSupp X (fun q => q.coeff nu) (by simp) mo
  rw [h3, h2, h1, LinearMap.map_smul]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

def compD {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    MvPolynomial (ι × Fin s) Kf :=
  ∑ mo ∈ H.support.filter (fun mo => ∀ x, multideg mo x = d x), monomial mo (H.coeff mo)

theorem compD_mem_Pol {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    compD d H ∈ Pol Kf s d := by
  unfold compD
  refine Submodule.sum_mem _ (fun mo hmo => ?_)
  rw [Finset.mem_filter] at hmo
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset hx
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hmo.2

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def levP (F : MvPolynomial (TV n' (m + 1)) (KK O)) : MvPolynomial (TL J nL r × Fin r) (KK O) :=
  ∑ mo ∈ F.support, monomial (plMon Fr p hk nL mo) (F.coeff mo)

def levN (F : MvPolynomial (TV n' (m + 1)) (KK O)) : MvPolynomial (TL J nL r × Fin K) (KK O) :=
  ∑ mo ∈ F.support, monomial (noMon Fr p hk nL mo) (F.coeff mo)

end Lev

section Fac

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K) (F : Frames n' r)

def zPl (A : ℤ → MvPolynomial (ℤ × Fin r) O) (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O))
    (rename (castV hk) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (plEmb O r K (A j))) * monomial l 1) *
      monomial ga 1)

def zNo (G : ℤ → MvPolynomial (ℤ × Fin K) O) : MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O))
    (rename (castV hk) (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (nmEmb O r K (G j))))

end Fac

def PlaneEven {n' k : ℕ} (r : ℕ) (ga : TV n' k →₀ ℕ) : Prop := ∀ v : TV n' k, ga v ≠ 0 → v.2.val < r ∧ Even v.1.val

def TieS {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val})

def RestT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
    ∀ (J : ℕ) [NeZero J] (nL : ZMod J → ℕ), J = Fr.J → (∀ j, nL j = (Fr.LLset (segZ j)).card) →
    ∀ (A : ℤ → MvPolynomial (ℤ × Fin r) O) (G : ℤ → MvPolynomial (ℤ × Fin K) O),
      (∀ i : ℕ, i < Fr.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters i}) →
      (∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) →
    ∀ (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
    ∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ),
      levImg Fr p hk nL rho dPl dNo (symG p O hk Fr l ga fun z => plEmb O r K (A z) * nmEmb O r K (G z)) =
        if InLow Fr p hk nL rho (l.mapDomain (castV hk) + ga) then
          tens (compD dPl (levP Fr p hk nL (zPl p O hk Fr A l ga))) (compD dNo (levN Fr p hk nL (zNo p O hk Fr G)))
        else 0

def RestN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)], UniformizedDVR p O → AdmissibleDVR p n' O →
    ∀ (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt →
    ∀ (G : ℤ → MvPolynomial (ℤ × Fin K) O),
      (∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) →
    ∀ (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      e (compD dNo (levN Fr p hk Dt.nL (zNo p O hk Fr G))) ≠ 0 →
      ∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r → ∀ M : ℤ,
        (lam1S LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (G (segZ j)) ≤ ((M : ℤ) : WithBot ℤ) → ka j u 0 ≤ M) ∧
        (lam1S LZ {y | y ≤ posU Fr (Dt.nL j) (segZ j) u} (G (segZ j)) ≤ ((M : ℤ) : WithBot ℤ) → ka j (u + 1) 0 ≤ M)

def RestTh : Prop :=
  ∀ (p : ℕ) (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O]
    (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
    ∀ (deg : Fin n' → ℕ) (Y : ℝ) (mS : ℕ) (J : ℕ) [NeZero J] (nL : ZMod J → ℕ), J = Fr.J →
      (∀ j, nL j = (Fr.LLset (segZ j)).card) →
    ∀ (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} →
      (∀ x ∈ Fr.letters (segZ j), ¬ Fr.IsW (segZ j) x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + g2mg p n' r K Fr deg mS Y (segZ j) x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + g2mg p n' r K Fr deg mS Y (segZ j) x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (g2th p n' Fr deg (segZ j) x)) →
    ∀ (ka : ZMod J → ℕ → Fin K → ℤ),
      (∀ u : ℕ, u < nL j + r → ∀ M' : ℤ,
        (lam1S LZ {y | y < posU Fr (nL j) (segZ j) u} G ≤ ((M' : ℤ) : WithBot ℤ) → ka j u 0 ≤ M') ∧
        (lam1S LZ {y | y ≤ posU Fr (nL j) (segZ j) u} G ≤ ((M' : ℤ) : WithBot ℤ) → ka j (u + 1) 0 ≤ M')) →
      ∀ u : ℕ, u < nL j + r →
        geZ (valS LZ {y | y < posU Fr (nL j) (segZ j) u} A) (thStar Fr p deg Y (r + K) mS nL K ka j u)

def dwB {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)
    (dPl : TL J Dt.nL r → ℕ) (mo₀ : TV n' (m + 1) →₀ ℕ) (j : ZMod J) : ℝ :=
  ∑ m' : Fin r, ((dPl ⟨j - 1, Sum.inr m'⟩ - multideg (plMon Fr p hk Dt.nL mo₀) ⟨j - 1, Sum.inr m'⟩ : ℕ) : ℝ) /
    (Dt.P (j - 1) m' : ℝ)

def RestPl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt → 2 ≤ J →
    ∀ (A : ℤ → MvPolynomial (ℤ × Fin r) O),
      (∀ i : ℕ, i < Fr.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters i}) →
    ∀ (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
    ∀ (t : ZMod J → ℕ → ℝ),
      (∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
        geZ (valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (A (segZ j))) (t j u)) →
    ∀ (dPl : TL J Dt.nL r → ℕ),
      (∀ (rho' : (ZMod J × Fin r) × Fin r → ℕ) (j : ZMod J) (i : Fin (Dt.nch j)),
        geZ (valS Dt.modelLet (Dt.chainML j i)
          (Dt.Fdig rho' (compD dPl (levP Fr p hk Dt.nL (zPl p O hk Fr A l ga))))) (t j i.val)) ∧
      ∀ (j : ZMod J) (mm : Fin r), mm.val + 2 ≤ r →
        geZ (valS Dt.trueLet (Dt.TSet j mm) (compD dPl (levP Fr p hk Dt.nL (zPl p O hk Fr A l ga))))
          (t j (Dt.nL j + (r - 1 - mm.val)) - dwB Fr hk Dt dPl (l.mapDomain (castV hk) + ga) j)

def RestSP : Prop :=
  ∀ (p n' r k : ℕ) [NeZero n'] (R : Type) [CommRing R] (F : Frames n' r) (hrk : r ≤ k) (c' Q L₁ N₁ : ℕ),
    F.Valid L₁ N₁ → Even n' → 1 ≤ r → ∀ ga ∈ (SPR R p F hrk c' Q).support, PlaneEven r ga

def RestArithStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    2 ≤ F.J ∧
    ∀ (E' : Fin n' → ℕ) (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p F l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS F Dt →
    ∀ (dPl dNo : TL J Dt.nL r → ℕ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ),
      BlockDeg F p Dt.nL (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t) rho dPl dNo →
      InLow F p hk Dt.nL rho (l.mapDomain (castV hk) + ga) →
      ∀ (jj : ZMod J) (mm : Fin r), mm.val + 2 ≤ r →
        dwB F hk Dt dPl (l.mapDomain (castV hk) + ga) jj ≤
          1 / 8 * slU F p (flatDeg lam0) Y (r + K) Dt.nL jj (Dt.nL jj + (r - 1 - mm.val))

theorem rest5aPairBStep_of (hT : RestT) (hN : RestN) (hTh : RestTh) (hP : RestPl) (hSP : RestSP) (C CLa : ℝ)
    (hAr : RestArithStep C CLa) : PlanePairsOnBlocksAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD E' xs hxs l hl ga hga J _ Dt dPl dNo ka hTd rho hb e he nu
  have S : UniformizedDVR p O := dvrOfStd hD.1
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hpF.out S
  have hR : AdmissibleDVR p n' O := Formalism.MainNotions.flipOneThree.admissible_dvr_of_unramified_quadratic_setting hD.1
  have hV := hD.2.2.1.2.1
  have hev : Even n' := hD.1.1.even
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hTd
  have hS : TieS F Dt := ⟨t1, t2, t3, t5, t6, t7⟩
  have hgaP : PlaneEven r ga := hSP p n' r (m + 1) O F hrk _ _ L₁ _ hV hev (NeZero.pos r) ga hga
  obtain ⟨hJ2, hAr'⟩ := hAr p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD
  set mS : ℕ := mStar p F (r + K) (orbitWindowCount r de h' x) (p ^ goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar) with hmS

  have hex : ∀ z : ℤ, ∃ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      (0 ≤ z → z < F.J →
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters z} ∧
      G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters z ∧ ¬ F.IsW z v.1} ∧
      (∀ x ∈ F.letters z, ¬ F.IsW z x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + g2mg p n' r K F (flatDeg lam0) mS Y z x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + g2mg p n' r K F (flatDeg lam0) mS Y z x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (g2th p n' F (flatDeg lam0) z x)) ∧
      xs z = plEmb O r K A * nmEmb O r K G) := by
    intro z
    by_cases hz : 0 ≤ z ∧ z < F.J
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
      obtain ⟨A, G, M, h1, h2, h3, h4⟩ := hxs i (by exact_mod_cast hz.2)
      exact ⟨A, G, M, fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, 0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
  choose A G M hAGM using hex
  have hnat : ∀ i : ℕ, i < F.J → (0 : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) < F.J := fun i hi =>
    ⟨Int.natCast_nonneg i, by exact_mod_cast hi⟩
  have hAs : ∀ i : ℕ, i < F.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters i} := fun i hi =>
    (hAGM i (hnat i hi).1 (hnat i hi).2).1
  have hGs : ∀ i : ℕ, i < F.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters i ∧ ¬ F.IsW i v.1} := fun i hi =>
    (hAGM i (hnat i hi).1 (hnat i hi).2).2.1
  have hsym : symG p O hk F l ga xs = symG p O hk F l ga fun z => plEmb O r K (A z) * nmEmb O r K (G z) := by
    unfold symG
    congr 4
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [(hAGM i (hnat i (Finset.mem_range.1 hi)).1 (hnat i (Finset.mem_range.1 hi)).2).2.2.2]
  rw [hsym, hT p n' r K m O hk F L₁ _ hV J Dt.nL t1 t2 A G hAs hGs l hl ga hgaP rho dPl dNo]
  split_ifs with hlow
  swap
  · rw [oneT_zero, planeCoeff_zero]; exact XX_zero Dt
  rw [planeCoeff_oneT_tens]
  by_cases he0 : e (compD dNo (levN F p hk Dt.nL (zNo p O hk F G))) = 0
  · rw [he0, coeff_zero, zero_smul]; exact XX_zero Dt
  apply XX_smul
  have hseg : ∀ jj : ZMod J, (0 : ℤ) ≤ segZ jj ∧ segZ jj < F.J := by
    intro jj
    refine ⟨Int.natCast_nonneg _, ?_⟩
    have := ZMod.val_lt jj
    unfold segZ
    rw [← t1]
    exact_mod_cast this
  have hNN := hN p n' r K m O S hR hk F L₁ _ hV hev J Dt hS G hGs dNo ka e he he0
  have hval : ∀ (jj : ZMod J) (u : ℕ), u < Dt.nL jj + r →
      geZ (valS LZ {y | y < posU F (Dt.nL jj) (segZ jj) u} (A (segZ jj)))
        (thStar F p (flatDeg lam0) Y (r + K) mS Dt.nL K ka jj u) := by
    intro jj
    obtain ⟨g1, g2, g3, -⟩ := hAGM (segZ jj) (hseg jj).1 (hseg jj).2
    exact hTh p n' r K O F L₁ _ hV (flatDeg lam0) Y mS J Dt.nL t1 t2 jj (A (segZ jj)) (G (segZ jj)) (M (segZ jj)) g1 g3 ka
      (hNN jj)
  obtain ⟨hch, hlk⟩ := hP p n' r K m O hk F L₁ _ hV hev J Dt hS (by rw [t1]; exact hJ2) A hAs l hl ga hgaP
    (fun jj u => thStar F p (flatDeg lam0) Y (r + K) mS Dt.nL K ka jj u) hval dPl
  refine ⟨by rw [t4]; exact compD_mem_Pol _ _, fun rho' jj i => ?_, fun jj mm hmm => ?_⟩
  · rw [t8 jj i, zero_mul, sub_zero]
    exact hch rho' jj i
  · rw [t9 jj mm hmm]
    have h8 := hAr' E' l hl ga hgaP J Dt hS dPl dNo rho hb hlow jj mm hmm
    intro k hk'
    have h9 := hlk jj mm hmm k hk'
    linarith

theorem rest5aMono_of_cut (hT : RestT) (hN : RestN) (hTh : RestTh) (hP : RestPl) (hSP : RestSP)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Lemma5aMonomial D CLa Ck Crk Cdeg := by
  apply rest5aMono_of_B
  intro _
  obtain ⟨C₁, hC₁, hC⟩ := hAr
  exact ⟨C₁, hC₁, fun C hC' => rest5aPairBStep_of hT hN hTh hP hSP C CLa (hC C hC' CLa)⟩

end Formalism.MainNotions.PairMembershipBlocks
