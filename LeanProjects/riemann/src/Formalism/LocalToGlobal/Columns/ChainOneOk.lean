import Formalism.LocalToGlobal.Columns.ChainOneOkL
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

theorem ookC {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2) : cOf R i = cOf R (i + 1) + 1 := by
  unfold cOf
  omega

theorem ookJat (j : ℕ) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    Jat (Pr := Pr) (R := R) true j w = LocE.JGsym w (qOf w) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
  unfold Jat
  rw [if_pos hw]
  rfl

def ookKap (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) : X.K :=
  muAt Ch sel mu c i P 1 * (muAt Ch sel mu c i P 1)⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) 1) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) 1 * ((R.N i + cOf R i : ℕ) : ℤ))

theorem ookOmPhi_eq (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu c i P 1 1 y = ookKap Ch sel mu c i P *
      LocE.PhiGS (P := P.1) (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) y := by
  unfold omPhi
  rw [ciOm_one]
  unfold PhiAt
  rw [if_pos hP, hs, if_pos rfl]
  rfl

theorem ookSupp (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∀ y, omPhi Ch sel mu c i P 1 1 y ≠ 0 → ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s) := by
  intro y hy
  rw [ookOmPhi_eq Ch sel mu c hs i P hP] at hy
  exact ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) (ocbRanks_step hm hi) (ookC hm hi) y (right_ne_zero_of_mul hy)

theorem ookRedPsi (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (σ : X.K →+* ℂ) :
    ∃ Ψr : Loc.SF (𝓞 X.E ⧸ P.1.asIdeal) ℂ (R.N i + (cOf R (i + 1) + 1)) (R.N (i + 1) + cOf R (i + 1)),
      ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
        (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
          Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
        σ (omPhi Ch sel mu c i P 1 1 y) = Ψr ybar := by
  refine ⟨fun ybar => σ (ookKap Ch sel mu c i P) *
    @ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) ((σ : X.K →* ℂ).compAddChar (psi0P Ch P.1))
      (fun s => (Units.map (σ : X.K →* ℂ)).comp (chiP Ch P.1 s)) R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) ybar, ?_⟩
  intro y ybar hint hred
  rw [ookOmPhi_eq Ch sel mu c hs i P hP, map_mul]
  exact congrArg (σ (ookKap Ch sel mu c i P) * ·)
    (ocbPhiGS_red (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) σ (psi0P Ch P.1) (chiP Ch P.1) (ocbRanks_step hm hi) (ookC hm hi) y ybar hint hred)

theorem ookE1at_indep (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (hψ : ∀ a, IntAt P.1 a → c.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) (σ : X.K →+* ℂ) {A' B' : ℕ}
    (hA : R.m ≤ c.A) (hB : 1 ≤ c.B) (hA' : R.m ≤ A') (hB' : 1 ≤ B') :
    E1at Ch sel mu { c with A := A', B := B' } i P 1 1 = E1at Ch sel mu c i P 1 1 := by
  funext xj
  obtain ⟨Ψr, hred⟩ := ookRedPsi Ch sel mu hX hPr c hs hm hi P hP σ
  have hAc : cOf R (i + 1) + 1 ≤ c.A := by unfold cOf; omega
  have hAc' : cOf R (i + 1) + 1 ≤ A' := by unfold cOf; omega
  exact firstUnfolding_reduction_independent (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (ciQOf_prime hPr hP) (ciCard P.1) (ookC hm hi) σ
    (omPhi Ch sel mu c i P 1 1) Ψr (ookSupp Ch sel mu c hs hm hi P hP) hred (c.psi P) (fun u => σ (psi0P Ch P.1 u))
    (fun a ha => by rw [hψ a ha]) hAc hB hAc' hB' xj

theorem ookXiSupp (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (x : HomE X.E (R.N i) (R.N (i + 1))) (h : XiAt Ch sel mu c i P 1 1 x ≠ 0)
    (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) : IntAt P.1 ((qOf P.1 : X.E) ^ c.A * x (Pi.single s 1) l) := by
  unfold XiAt at h
  have h1 := right_ne_zero_of_mul h
  have hx := xInt_of_firstUnfolding_ne_zero (ookC hm hi) (omPhi Ch sel mu c i P 1 1) (ookSupp Ch sel mu c hs hm hi P hP) _ _ _ x h1
  have h2 := hx l.1 s.1 l.2 s.2
  rw [ocbS_eN_single s.2, ocbS_atN_of_lt _ l.2] at h2
  refine IntAt.mul ?_ h2
  rw [← Nat.cast_pow]
  exact ocbS_intAt_natCast _

theorem ookXiInv (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (hψ : ∀ a, IntAt P.1 a → c.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) (σ : X.K →+* ℂ)
    (hA : R.m ≤ c.A) (hB : c.B = 1) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ c.B)⁻¹ * z (Pi.single s 1) l)) :
    XiAt Ch sel mu c i P 1 1 (x + z) = XiAt Ch sel mu c i P 1 1 x := by
  obtain ⟨Ψr, hred⟩ := ookRedPsi Ch sel mu hX hPr c hs hm hi P hP σ
  have hAc : cOf R (i + 1) + 1 ≤ c.A := by unfold cOf; omega
  have hz' : ∀ l s, l < R.N (i + 1) → s < R.N i → IntAt P.1 (Loc.atN (z (Loc.eN X.E (R.N i) s)) l / (qOf P.1 : X.E)) := by
    intro l s hl hs
    have h1 := hz ⟨s, hs⟩ ⟨l, hl⟩
    rw [hB, pow_one, inv_mul_eq_div] at h1
    rw [ocbS_eN_single hs, ocbS_atN_of_lt _ hl]
    exact h1
  unfold XiAt
  congr 1
  exact firstUnfolding_add_eq_self_of_intAt_div (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (ciQOf_prime hPr hP) (ciCard P.1) (ookC hm hi) σ
    (omPhi Ch sel mu c i P 1 1) Ψr (ookSupp Ch sel mu c hs hm hi P hP) hred (c.psi P) (fun u => σ (psi0P Ch P.1 u))
    (fun a ha => by rw [hψ a ha]) hAc (by rw [hB]) x z hz'

theorem ookLast {m2 : ℕ} (hm : R.m = m2 + 2) :
    cOf R m2 = 1 ∧ cOf R (m2 + 1) = 0 ∧ R.k ≤ R.N m2 ∧ R.k ≤ R.r ∧ R.r + (m2 + 1 - 1) * R.t = R.N m2 + cOf R m2 ∧
      R.r + (m2 + 1 - 1) * R.t ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
  have h1 : cOf R m2 = 1 := by unfold cOf; omega
  have h2 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have h3 := Y_eq_X_add (R := R) (j := m2) (by omega)
  have h4 : R.N (m2 + 1) = R.N m2 + R.t + 1 := by unfold Ranks.N; ring
  have h5 : R.k ≤ R.N m2 := by unfold Ranks.N; omega
  have h6 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h7 : R.m - 1 - m2 = 1 := by omega
  rw [h7] at h3
  refine ⟨h1, h2, h5, h6, ?_, ?_⟩
  · rw [Nat.add_sub_cancel, h1]; exact h3
  · rw [Nat.add_sub_cancel, h3, h4, h2]; omega

theorem ookPsiSuppX (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (h : PsiAt Ch sel mu c m2 P 1 x₀ y' ≠ 0) (s : Fin (R.N m2)) (l : Fin (R.N (m2 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ c.A * x₀ (Pi.single s 1) l) := by
  classical
  obtain ⟨hc', hc, hk, -, ha, -⟩ := ookLast (R := R) hm
  unfold PsiAt at h
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP] at h
  have h' := right_ne_zero_of_mul h
  rw [phiGS_eq] at h'
  have hC := (ite_ne_right_iff.1 h').1
  have hp' : LocE.fPos R.k (cOf R m2) (R.N m2) s.1 < R.r + (m2 + 1 - 1) * R.t := by
    rw [ha]; exact ocbPhi_fPos_lt hk (Nat.lt_of_lt_of_le s.2 (Nat.le_add_right _ _))
  have h1 := hC.1 l.1 _ (Nat.lt_of_lt_of_le l.2 (Nat.le_add_right _ _)) hp'
  rw [ookEntB_joinX (qOf P.1) hc' hc hk x₀ y' l.2 s.2] at h1
  refine IntAt.mul ?_ h1
  rw [← Nat.cast_pow]
  exact ocbS_intAt_natCast _

theorem ookPsiInv (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1)))
    (hz : ∀ i, IntAt P.1 (z i)) : PsiAt Ch sel mu c m2 P 1 x₀ (y' + z) = PsiAt Ch sel mu c m2 P 1 x₀ y' := by
  obtain ⟨hc', hc, hk, hkr, ha, han⟩ := ookLast (R := R) hm
  unfold PsiAt
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP, ookOmPhi_eq Ch sel mu c hs m2 P hP]
  congr 1
  refine ookPhiGS_congr (ciQ_mem P.1) (ciQ_ne_zero (ciQ_notMem_sq hX hPr hP)) _ _ _ _ hkr han fun p p' hp hp' => ?_
  have hp0 : p < R.N (m2 + 1) := by omega
  by_cases hpk : p' = R.k
  · rw [hpk, symEntB_join_col _ hc' hc x₀ (y' + z) hp0, symEntB_join_col _ hc' hc x₀ y' hp0]
    exact ⟨z ⟨p, hp0⟩, hz _, by rw [Pi.add_apply, mul_add]⟩
  · obtain ⟨hsl, hfp⟩ := ookFIdx_lt hc' hk (by omega) hpk
    rw [← hfp, ookEntB_joinX _ hc' hc hk x₀ (y' + z) hp0 hsl, ookEntB_joinX _ hc' hc hk x₀ y' hp0 hsl]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩

theorem ookPsiInvX (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hB : c.B = 1) (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ c.B)⁻¹ * z (Pi.single s 1) l)) :
    PsiAt Ch sel mu c m2 P 1 (x₀ + z) y' = PsiAt Ch sel mu c m2 P 1 x₀ y' := by
  obtain ⟨hc', hc, hk, hkr, ha, han⟩ := ookLast (R := R) hm
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero (ciQ_notMem_sq hX hPr hP)
  unfold PsiAt
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP, ookOmPhi_eq Ch sel mu c hs m2 P hP]
  congr 1
  refine ookPhiGS_congr (ciQ_mem P.1) hq0 _ _ _ _ hkr han fun p p' hp hp' => ?_
  have hp0 : p < R.N (m2 + 1) := by omega
  by_cases hpk : p' = R.k
  · rw [hpk, symEntB_join_col _ hc' hc (x₀ + z) y' hp0, symEntB_join_col _ hc' hc x₀ y' hp0]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩
  · obtain ⟨hsl, hfp⟩ := ookFIdx_lt hc' hk (by omega) hpk
    rw [← hfp, ookEntB_joinX _ hc' hc hk (x₀ + z) y' hp0 hsl, ookEntB_joinX _ hc' hc hk x₀ y' hp0 hsl]
    have h1 := hz ⟨_, hsl⟩ ⟨p, hp0⟩
    rw [hB, pow_one] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearMap.add_apply, Pi.add_apply, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]

end Glob

section Cst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def ookCst (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (mq : ℕ → SB → X.K) (A : ℕ) : LocCst X SB :=
  { ciCst Ch SB mq with A := A, sharp := true }

variable {Ch}

theorem ookCst_ok (hPr : Pr.Ok) (hCh : Ch.Ok) {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (hSB : ∀ P ∈ SB, P ∈ Pr.vGs)
    (h4 : ∀ P ∈ SB, qOf P % 4 = 1) {mq : ℕ → SB → X.K} {A : ℕ} (hA : 1 ≤ A) : (ookCst Ch SB mq A).Ok where
  psi_add := (ciCst_ok hPr hCh hSB h4 (mq := mq)).psi_add
  psi_int := (ciCst_ok hPr hCh hSB h4 (mq := mq)).psi_int
  psi_ne := (ciCst_ok hPr hCh hSB h4 (mq := mq)).psi_ne
  D_pos _ := le_refl 1
  sq_sq := (ciCst_ok hPr hCh hSB h4 (mq := mq)).sq_sq
  M_pos := le_refl 1
  M_le_A := hA
  M_le_B := le_refl 1
  B_pos := le_refl 1

theorem ookXiUnit (hCh : Ch.Ok) {σ₀ : X.K →+* ℂ} {xi0 : X.E} (hW : Ch.WeilTied σ₀ xi0) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : IntAt w xi0 ∧ redP w xi0 ≠ 0 := by
  have hne : redP w xi0 ≠ 0 := by
    intro h0
    apply hCh.psi_zero_nontrivial_character ⟨w, hw⟩
    ext c
    apply σ₀.injective
    rw [hW ⟨w, hw⟩ c 0 (by rw [h0, zero_mul, Int.cast_zero]), AddChar.one_apply, map_one]
    simp
  exact ⟨intAt_of_redP_ne_zero₂ hne, hne⟩

end Cst

section Ok

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

def ookCstR (G : ChGlob X R.m) : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S)) :=
  ookCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) (ciMuq G ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) R.m

variable {Ch}

theorem referenceConstants_psi_depth_one (hPr : Pr.Ok) (G : ChGlob X R.m) (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (a : X.E) (ha : IntAt P.1 a) :
    (ookCstR Ch sel S G).psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) := by
  show ciPsi Ch P _ = _
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr (ciMemG sel S P)).ne_zero
  unfold ciPsi
  rw [mul_div_cancel₀ _ hq0, if_pos ha]

theorem ookCstR_base (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m) {m2 : ℕ}
    (hm : R.m = m2 + 2) : OcbBase Ch sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S G) m2 where
  hX := hX
  hPr := hPr
  hCh := hCh
  hm := hm
  cst_ok := ookCst_ok hPr hCh (fun P hP => ciMemG sel S ⟨P, hP⟩) (fun P hP => h4 P (ciMemG sel S ⟨P, hP⟩)) (by have := R.two_le_m; omega)
  sharp := rfl
  psi0 P a _ ha := referenceConstants_psi_depth_one sel S hPr G P a ha
  depthG _ _ := rfl

theorem oneIdx_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2)
    (hO : OneCosetSym Ch sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S G) (colLevSym Ch) m2)
    (hN : NonVanSym Ch sel (mu0 X.F X.E X.K S) (ookCstR Ch sel S G) m2) :
    (oneIdx (colLevSym Ch) (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).Ok Ch sel (mu0 X.F X.E X.K S)
      (ookCstR Ch sel S G) G m2 := by
  have hG : ∀ P : rowSG Pr sel (mu0 X.F X.E X.K S), P.1 ∈ Pr.vGs := ciMemG sel S
  have hSB : ∀ P ∈ rowSG Pr sel (mu0 X.F X.E X.K S), P ∈ Pr.vGs := fun P hP => ciMemG sel S ⟨P, hP⟩
  have hψ : ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (a : X.E), IntAt P.1 a →
      (ookCstR Ch sel S G).psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) :=
    fun P a ha => referenceConstants_psi_depth_one sel S hPr G P a ha
  have hs : (ookCstR Ch sel S G).sharp = true := rfl
  have hA : R.m ≤ (ookCstR Ch sel S G).A := le_refl _
  have hB : (ookCstR Ch sel S G).B = 1 := rfl
  obtain ⟨hc', hc, -, -, -, -⟩ := ookLast (R := R) hm
  obtain ⟨hn, hinj, hsurj⟩ := oneIdx_clauses hO hN
  exact
    { hm := hm
      cst_ok := ookCst_ok hPr hCh hSB (fun P hP => h4 P (hSB P hP)) (by have := R.two_le_m; omega)
      xiUnitAtPrime := fun P => ookXiUnit hCh hW P.1 (hG P)
      weil := ciCst_weil Ch hX hPr hSB (ciMuq G ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) hW (fun P hP => (ookXiUnit hCh hW P (hSB P hP)).1)
      muqQ := fun _ _ P hP => absurd (hG P) hP
      muqG := fun i h P hP qu hqu => ciMuq_tie G _ hval i h P hP qu hqu
      mu0G := fun j => (hT.mu0 j).atg
      psi0 := fun P a _ ha => hψ P a ha
      deep := fun A' B' hA' hB' i hi _ _ P =>
        ookE1at_indep Ch sel _ hX hPr _ hs hm hi P (hG P) (hψ P) G.σ₀ hA (le_refl 1) (le_trans hA hA') (le_trans (le_refl 1) hB')
      zero_uniq := ⟨⟨(), Nat.zero_le _⟩, fun _ => Subtype.ext rfl⟩
      zero_h := fun _ _ => rfl
      zero_G := fun _ => colLevSym_zero Ch
      zero_Q := fun _ => rfl
      last_uniq := ⟨⟨(), le_refl _⟩, fun _ => Subtype.ext rfl⟩
      last_h := fun _ _ => rfl
      nonvan := hn
      inj := fun i hi b b' _ => hinj i hi b b'
      surj := hsurj
      stabG := fun _ _ _ _ => Subgroup.one_mem _
      depthG := fun _ _ => rfl
      depthQ := fun P hP => absurd (hG P) hP
      depthQ' := fun P hP => absurd (hG P) hP
      boundQ := fun _ _ P hP => absurd (hG P) hP
      psiSupp := fun _ P x₀ y' h i => by
        rw [if_pos (hG P), pow_one]
        exact (psiAt_sym Ch sel _ _ hc' hc hs P (hG P) x₀ y' h i).1
      psiInv := fun _ P x₀ y' z hz =>
        ookPsiInv Ch sel _ hX hPr _ hs hm P (hG P) x₀ y' z fun i => by
          have h1 := hz i
          rwa [if_pos (hG P), pow_zero, inv_one, one_mul] at h1
      xiSupp := fun i hi _ _ P x h s l => ookXiSupp Ch sel _ _ hs hm hi P (hG P) x h s l
      xiInv := fun i hi _ _ P x z hz => ookXiInv Ch sel _ hX hPr _ hs hm hi P (hG P) (hψ P) G.σ₀ hA hB x z hz
      psiSuppX := fun _ P x₀ y' h s l => ookPsiSuppX Ch sel _ _ hs hm P (hG P) x₀ y' h s l
      psiInvX := fun _ P x₀ z y' hz => ookPsiInvX Ch sel _ hX hPr _ hs hm P (hG P) hB x₀ z y' hz
      int := fun j _ P => by
        show Loc.prX (Loc.Cbe (Jat (Pr := Pr) true j P.1) 1) ≤ _
        rw [ookJat j (hG P)]
        exact ookPrX_le
      grpQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
      chrQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
      grpG := fun j b w hbar => hO.grpG j b.2 w hbar
      chrG := fun j b w hbar g r hr hrg hred => hO.chrG j b.2 w hbar g r hr hrg hred }

end Ok

end Formalism.L2.Col
