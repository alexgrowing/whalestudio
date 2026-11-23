import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CardStabDvdAutU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem card_autU (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) = Nat.card (Mem.Col2.autO N) :=
  Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, γ.1.2, mem_autLat.2 (mem_autU.1 γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, mem_autU.2 (mem_autLat.1 γ.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_autU_dvd_tilN (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) ∣ Nat.card (autU (tilN N)) := by
  let f : autU N →* autU (tilN N) :=
    ((extUH rfl).comp (autU N).subtype).codRestrict _ fun γ => mem_autU.2 (by
      have h := tilN_gmap γ.1.1 N
      rw [mem_autU.1 γ.2] at h
      exact h.symm)
  refine Subgroup.card_dvd_of_injective f fun a b hab => Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  have h : extE a.1.1 = extE b.1.1 := congrArg (fun z : autU (tilN N) => z.1.1) hab
  have h1 := initL_extE a.1.1 (incl E n x)
  rw [h, initL_extE] at h1
  have h2 : initL E n (incl E n x) = x := by
    funext i
    simp [initL, incl, LinearMap.funLeft_apply]
  rw [h2] at h1
  exact h1.symm

theorem exists_card_autU_dvd {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (k : ℕ) :
    ∃ N' : Submodule (𝓞 E) (Sp E (n + k)), IsSdLat N' ∧ Nat.card (autU N) ∣ Nat.card (autU N') := by
  induction k with
  | zero => exact ⟨N, hN, dvd_rfl⟩
  | succ k ih =>
    obtain ⟨N', h1, h2⟩ := ih
    exact ⟨tilN N', ⟨tilN_lattice h1.1, tilN_unimodular h1.2⟩, h2.trans (card_autU_dvd_tilN N')⟩

theorem card_autU_dvd_DGam (hE : PosStar E) (R : Ranks) (hm : 1 ≤ R.m) {i : ℕ} (hi : i ≤ R.m) {N : Submodule (𝓞 E) (Sp E (R.N i))}
    (hN : IsSdLat N) : Nat.card (autU N) ∣ Mem.Col2.DGam E R := by
  have hle : R.N i ≤ R.N R.m := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨N', h1, h2⟩ := exists_card_autU_dvd hN k
  refine h2.trans ?_
  rw [card_autU]
  exact Mem.Col2.dvd_DGam hE R (hk ▸ Mem.Col2.N_mem_gamRanks R hm le_rfl) h1.1 h1.2

end Aut

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ)
  (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ)

def muInvPt (i : ℕ) {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) p.deco.1.N (frsF sel mu p)

def rhoPt (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) : ℂ :=
  σ (muInvPt Ch sel mu cst i p) * chi (R.N i) p.deco.1.N ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoPt' (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) : ℂ :=
  (σ (muInvPt Ch sel mu cst i p))⁻¹ * chi (R.N (i + 1)) p.deco.1.N ^ (((R.N i / 2 : ℕ) : ℤ))

def RhoUnit : Prop :=
  (∀ i, i < R.m → ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr)‖ = 1) ∧
  ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → ‖chi n N‖ = 1

def ChiSplit (A : Amb X) : Prop :=
  ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    A.chiF a b N N' = chi a N ^ (((b / 2 : ℕ) : ℤ)) * chi b N' ^ (-((a / 2 : ℕ) : ℤ))

variable {Ch sel mu cst σ chi}

theorem RhoUnit.norm_rhoPt (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) :
    ‖rhoPt Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt, norm_mul, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, one_mul]

theorem RhoUnit.norm_rhoPt' (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) :
    ‖rhoPt' Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt', norm_mul, norm_inv, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, inv_one, one_mul]

theorem rhoUnit_of {D : D7} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) :
    RhoUnit Ch sel mu cst s.σ₀ (chiLat s χ) :=
  ⟨fun _ hi _ N fr => hG ▸ norm_muInvDet hX hPr hsel hS (hG ▸ ht) hL hi N fr, fun _ _ hN => norm_chiLat hX hs hχ hN⟩

end Rho

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (P : LevFam X.E X.K R.r Pr.vGs) (c : TopDepth R cst.M)

@[reducible] def twFam : ℕ → GFam X.K := levFam W sel mu cst L u m2 b hY (topLevG Ch P) (topLevQ R sel mu c.pos)

def TwEquiv : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    TopEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P c

variable {W Ch sel mu cst L A u m2 b hY P c}

theorem TwEquiv.kerEquivC (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok)
    (H : TilOk Pr sel mu u) : KerEquivC W Ch sel mu cst L A u m2 b hY P :=
  ⟨h.1, h.2.1, h.2.2.cp2Equiv hX hPr hm hc H (tameFr_chTh W Ch sel mu cst A u m2)⟩

def twistedKernelPointCoset (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (al : L.β m2) :
    ClsKer ((chF W sel mu L u m2).mem al) (cplMem W sel mu cst L u m2 b hY).gsd :=
  cplKer1 (topCpl h.2.1 h.2.2 al)

def twistedKernelCosetPoint (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) :
    ClsKer (cplMem W sel mu cst L u m2 b hY).gsd (frmMem W sel mu L u (topLevG Ch P) (topLevQ R sel mu c.pos)).gsd where
  k d p' := topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) d.1.1 d.1.2 p'
  equiv g g₁ d p' := h.2.2 g g₁ d.1.1 d.1.2 p'

def twKer (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) : KerFam (twFam W Ch sel mu cst L u m2 b hY P c) :=
  spKer (matFam h.1) (twistedKernelPointCoset h) (twistedKernelCosetPoint h)

def twXi (i j : ℕ) (e : j = i + 1) : ∀ (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β),
    (twFam W Ch sel mu cst L u m2 b hY P c i).D β → (twFam W Ch sel mu cst L u m2 b hY P c j).D β' → HomE X.E (R.N i) (R.N j) → X.K
  | .mat al _, .mat be _ =>
    (match j, e, be with | _, rfl, be => XiEntry Ch sel mu cst L i al be :
      ChPt (R := R) sel mu u i → ChPt (R := R) sel mu u j → HomE X.E (R.N i) (R.N j) → X.K)
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : m2 = i), h', al with
      | _, _, rfl, rfl, al => fun p₀ d => XiCpl1 Ch sel mu cst L m2 al p₀ d.1.1 d.1.2 :
      ChPt (R := R) sel mu u i → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.cpl h') → HomE X.E (R.N i) (R.N j) → X.K)
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => fun d p' => XiTop Ch sel mu cst m2 d.1.1 d.1.2 p' :
      (twFam W Ch sel mu cst L u m2 b hY P c i).D (.cpl h) → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.top h') →
        HomE X.E (R.N i) (R.N j) → X.K)
  | .mat _ _, .top _ => fun _ _ _ => 0
  | .cpl _, .mat _ _ => fun _ _ _ => 0
  | .cpl _, .cpl _ => fun _ _ _ => 0
  | .top _, _ => fun _ _ _ => 0

def twRep (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : ChPt (R := R) sel mu u i :=
  levPt i x.1 (((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2)

def twSrc (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi) : ChSrc X R where
  F := twFam W Ch sel mu cst L u m2 b hY P c
  ok := levFam_ok hF (topGSD_ok W Ch sel mu hX P u c)
  lam := W.lamTrue u
  eV _ := LinearEquiv.refl _ _
  kk := twKer hK
  rho i x := rhoPt Ch sel mu cst A.σ₀ chi i (twRep i x)
  rho' i x := rhoPt' Ch sel mu cst A.σ₀ chi i (twRep (i + 1) x)
  rho_norm _ hi _ := hρ.norm_rhoPt hi _
  rho'_norm _ hi _ := hρ.norm_rhoPt' hi _
  DG := Mem.Col2.DGam X.E R
  DG_pos := Mem.Col2.DGam_pos (posStar_of_ok hX) R
  dvd i hi x := (card_stab_dvd_autU i x.1 _).trans
    (card_autU_dvd_DGam (posStar_of_ok hX) R (by omega) hi ⟨(twRep i x).deco.2.lat, (twRep i x).deco.2.uni⟩)

def twSrcOf {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {G : ChGlob X R.m} {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok)
    (hχ : TaylorLogMetric.IsChi D χ) (hF : ∀ j, (chF W sel mu L u j).Ok) (hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c) : ChSrc X R :=
  twSrc (chiLat s χ) hX hL.hm hF hK (rhoUnit_of hX hPr hsel hS ht hL hG hs hχ)

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Laws

variable (b hY P c) in

def twStart {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (twFam W Ch sel mu cst L u m2 b hY P c 0).Forms :=
  spIn m2 R.m _ _ 0 ∘ₗ startC hL u

section Col

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} {G : ChGlob X R.m}

end Col

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c R.m).Cl :=
  (inferInstance : Nonempty (TopPt R sel mu u)).elim fun p => ⟨⟨.top rfl, Quotient.mk _ p⟩⟩

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c (m2 + 1)).Cl :=
  haveI : NeZero (R.N (m2 + 1)) := ⟨(R.N_pos _).ne'⟩
  open Classical in ⟨⟨.cpl rfl, Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG Pr sel mu) (stdLat X.E (R.N (m2 + 1)))
    fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)}), 0, zero_mem _, rfl⟩⟩⟩

example (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m < i) : IsEmpty (twFam W Ch sel mu cst L u m2 b hY P c i).Cl :=
  ⟨fun x => (SpIdx.isEmpty_of_lt (by omega) hi).false x.1⟩

example (σ : X.K →+* ℂ) (z : ℂ) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (h : muInvPt Ch sel mu cst i p = 1) (h' : muInvPt Ch sel mu cst i p' = 1) :
    rhoPt Ch sel mu cst σ (fun _ _ => z) i p = (z ^ (R.N (i + 1) / 2))⁻¹ ∧ rhoPt' Ch sel mu cst σ (fun _ _ => z) i p' = z ^ (R.N i / 2) := by
  simp only [rhoPt, rhoPt', h, h', map_one, one_mul, inv_one, zpow_neg, zpow_natCast, and_self]

end Chain

end GlobalTheory.GO
