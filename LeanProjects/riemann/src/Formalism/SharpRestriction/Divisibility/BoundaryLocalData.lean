import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

noncomputable section

namespace Formalism.MainNotions.BoundaryLocalData

open Formalism.BasicNotions NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def vU (p : ℕ) {C : Type} [NormedField C] (u : Cˣ) : ℝ := -Real.logb p ‖(u : C)‖

theorem sqrtMinusD_sq (D : Formalism.BasicNotions.D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  exact D.host.sqd_sq

theorem half_one_add_sqrt_neg_isIntegral (D : Formalism.BasicNotions.D7) :
    IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2 : D.host.E) := by
  obtain ⟨-, -, -, hd, -⟩ := D.host.hyp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((4 * k + 2 : ℕ) : ℤ), ?_, ?_⟩
  · monicity!
  · have h := sqrtMinusD_sq D
    rw [hk] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    push_cast at h
    simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    have : ((1 + D.host.sqrtMinusD) / 2 : D.host.E) ^ 2 =
        (1 + 2 * D.host.sqrtMinusD + D.host.sqrtMinusD ^ 2) / 4 := by ring
    rw [this, h]
    ring

def w0 (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2, half_one_add_sqrt_neg_isIntegral D⟩

theorem conj_sqrtMinusD (D : Formalism.BasicNotions.D7) :
    D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have h := D.host.gal_sqd D.host.conj
  have h2 : D.host.gal D.host.conj = D.R.cc := D.host.gal.apply_symm_apply _
  rw [h2] at h
  simpa [Host.sqrtMinusD, Formalism.HC.Frame.cc, c0] using h

theorem one_sub_halfSqrt_eq_conj (D : Formalism.BasicNotions.D7) :
    ((1 - w0 D : 𝓞 D.host.E) : D.host.E) = D.host.conj (w0 D : D.host.E) := by
  have hw : algebraMap (𝓞 D.host.E) D.host.E (w0 D) = (1 + D.host.sqrtMinusD) / 2 := rfl
  change algebraMap (𝓞 D.host.E) D.host.E (1 - w0 D) =
    D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (w0 D))
  rw [map_sub, map_one, hw, map_div₀, map_add, map_one, conj_sqrtMinusD, map_ofNat]
  ring

structure LocB (D : Formalism.BasicNotions.D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) where

  chX : ∀ {Z : L.Mdl}, L.Pt Z → Type
  [xAdd : ∀ {Z : L.Mdl} (y : L.Pt Z), AddCommGroup (chX y)]
  [xMod : ∀ {Z : L.Mdl} (y : L.Pt Z), Module (𝓞 D.host.E) (chX y)]

  phi : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y ≃+ chX y

  phi_conj : ∀ {Z : L.Mdl} (y : L.Pt Z) (c c' : 𝓞 D.host.E),
    (c' : D.host.E) = D.host.conj (c : D.host.E) → ∀ a : L.Ylat y, phi y (c' • a) = c • phi y a

  tau : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → chX y → ((L.fld y).C)ˣ
  tau_add_left : ∀ {Z : L.Mdl} (y : L.Pt Z) a a' χ, tau y (a + a') χ = tau y a χ * tau y a' χ
  tau_add_right : ∀ {Z : L.Mdl} (y : L.Pt Z) a χ χ', tau y a (χ + χ') = tau y a χ * tau y a χ'
  tau_symm : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, tau y a (phi y b) = tau y b (phi y a)
  tau_smul : ∀ {Z : L.Mdl} (y : L.Pt Z) (c : 𝓞 D.host.E) a χ, tau y (c • a) χ = tau y a (c • χ)

  be_tau : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, L.be y a b = vU p (tau y a (phi y b))

  multiplicationLatticeFirst : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  multiplicationLatticeSecond : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  mulC : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → ((L.fld y).C)ˣ

  psiV_def : ∀ {Z : L.Mdl} (y : L.Pt Z) a, L.psiV y a = vU p (mulC y a (w0 D • a))

  StrictHenselianAcyclic : L.Unim → Type
  squareRootLineBundle : L.Unim → Type
  res2 : ∀ {La}, StrictHenselianAcyclic La → squareRootLineBundle La

  PoiQ : ∀ La, squareRootLineBundle La

  biext : ∀ {La}, StrictHenselianAcyclic La → Prop

  dg : ∀ {La}, StrictHenselianAcyclic La → L.LBG La
  dgq : ∀ {La}, squareRootLineBundle La → L.LBGq La
  dg_res : ∀ {La} (P : StrictHenselianAcyclic La), L.resQ (dg P) = dgq (res2 P)

  PPq_def : ∀ La, L.PPq La = dgq (PoiQ La)

  BPt : Type

  Rl : BPt → Type
  [iRr : ∀ z, CommRing (Rl z)]
  [iRd : ∀ z, IsDomain (Rl z)]
  [iRl : ∀ z, IsLocalRing (Rl z)]
  [iRn : ∀ z, IsNoetherianRing (Rl z)]
  [iRi : ∀ z, IsIntegrallyClosed (Rl z)]
  [iRc : ∀ z, IsAdicComplete (IsLocalRing.maximalIdeal (Rl z)) (Rl z)]

  Yb : BPt → Type
  [iYa : ∀ z, AddCommGroup (Yb z)]
  [iYm : ∀ z, Module (𝓞 D.host.E) (Yb z)]
  Xb : BPt → Type
  [iXa : ∀ z, AddCommGroup (Xb z)]
  [iXm : ∀ z, Module (𝓞 D.host.E) (Xb z)]
  phib : ∀ z, Yb z ≃+ Xb z
  phib_conj : ∀ z (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a : Yb z, phib z (c' • a) = c • phib z a
  taub : ∀ z, Yb z → Xb z → (FractionRing (Rl z))ˣ
  taub_add_left : ∀ z a a' χ, taub z (a + a') χ = taub z a χ * taub z a' χ
  taub_add_right : ∀ z a χ χ', taub z a (χ + χ') = taub z a χ * taub z a χ'
  taub_symm : ∀ z a b, taub z a (phib z b) = taub z b (phib z a)
  taub_smul : ∀ z (c : 𝓞 D.host.E) a χ, taub z (c • a) χ = taub z a (c • χ)

  taub_pos : ∀ z a, ((taub z a (phib z a) : (FractionRing (Rl z))ˣ) : FractionRing (Rl z)) ∈
    (algebraMap (Rl z) (FractionRing (Rl z))).range

  Sg : BPt → Type
  [iSg : ∀ z, AddCommGroup (Sg z)]
  [iSk : ∀ z, Module (FractionRing (Rl z)) (Sg z)]
  [iSm : ∀ z, Module (Rl z) (Sg z)]
  [iSt : ∀ z, IsScalarTower (Rl z) (FractionRing (Rl z)) (Sg z)]

  Sreg : ∀ z, Submodule (Rl z) (Sg z)

  fc : ∀ z, Sg z →ₗ[FractionRing (Rl z)] (Xb z → FractionRing (Rl z))

  trU : ∀ z, Yb z → Xb z → (Rl z)ˣ

  oX : L.Sh L.Xm
  oX_inv : L.IsInv oX

  secOf : ∀ {F : L.Sh L.Xm}, L.GIso oX F → L.Sec F

  nrm_secOf : ∀ {F : L.Sh L.Xm} (φ : L.GIso oX F) y, L.nrm F (secOf φ) y = (p : ℝ) ^ (-(L.vrat φ y))

  keySh_inv : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)

  dimB : L.Pt L.Xm → ℕ
  dimB_add : ∀ y, dimB y + L.dP y = D.R.f * r

  FB : ∀ (y : L.Pt L.Xm) (nW n : ℕ), (Fin nW → chX y) → Type
  [fbAdd : ∀ y nW n χ, AddCommGroup (FB y nW n χ)]
  [fbMod : ∀ y nW n χ, Module (L.fld y).C (FB y nW n χ)]

  nB : ∀ {y nW n χ}, FB y nW n χ → ℝ

  sgc : ∀ y nW n χ, L.Sn y (L.latStd nW) n →ₗ[(L.fld y).C] FB y nW n χ

  trB : ∀ y nW n (a : Fin nW → L.Ylat y) χ,
    FB y nW n χ ≃ₗ[(L.fld y).C] FB y nW n (χ + n • fun i => phi y (a i))
  trB_norm : ∀ y nW n a χ σ, nB (trB y nW n a χ σ) = nB σ

  alp : ℕ → 𝓞 D.host.E
  alp_spec : ∀ n, ModuliIntegralCharts.NHyp D p n →
    (alp n : D.host.E) * D.host.conj (alp n : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ alp n = (mm : 𝓞 D.host.E)) ∨ (alp n : D.host.E) ∈ D.host.K)

  th1 : ∀ y nW, L.Sn y (L.latStd nW) 1
  pbAl : ∀ y nW n, L.Sn y (L.latStd nW) 1 →ₗ[(L.fld y).C] L.Sn y (L.latStd nW) n
  vth_def : ∀ y nW n, ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = pbAl y nW n (th1 y nW)

  jX : ∀ y nW n DF χ, FB y nW n χ →ₗ[(L.fld y).C] L.Jet y (L.latStd nW) n DF

  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (L.fld y).C (L.Jet y (L.latStd nW) n DF)),
    ∀ v, v ∈ L.intJet y (L.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1

  jX_int : ∀ y nW n DF χ (σ : FB y nW n χ), nB σ ≤ 1 → jX y nW n DF χ σ ∈ L.intJet y (L.latStd nW) n DF

  jet_fourier : ∀ y nW n DF (s : L.Sn y (L.latStd nW) n) (t : (L.fld y).C), t ≠ 0 →
    ∃ F₀ : Finset (Fin nW → chX y), ∀ F : Finset (Fin nW → chX y), F₀ ⊆ F →
      ∃ v ∈ L.intJet y (L.latStd nW) n DF,
        L.jet y (L.latStd nW) n DF s - ∑ χ ∈ F, jX y nW n DF χ (sgc y nW n χ s) = t • v

attribute [instance] LocB.xAdd LocB.xMod LocB.iRr LocB.iRd LocB.iRl LocB.iRn LocB.iRi LocB.iYa LocB.iYm
  LocB.iXa LocB.iXm LocB.iSg LocB.iSk LocB.iSm LocB.iSt LocB.fbAdd LocB.fbMod

structure Prov (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) where
  loc : ∀ w p, p.Prime → LocB D (X.loc w p)

namespace LocB

variable {D : Formalism.BasicNotions.D7} {r j p : ℕ} {L : ModuliIntegralCharts.Loc D r j p} (B : LocB D L)

def shiftA {Z : L.Mdl} (y : L.Pt Z) (a : L.Ylat y) : B.chX y :=
  B.multiplicationLatticeFirst y a (w0 D • a) + w0 D • B.multiplicationLatticeSecond y a (w0 D • a)

def psiA {Z : L.Mdl} (y : L.Pt Z) (a : L.Ylat y) : ((L.fld y).C)ˣ := B.mulC y a (w0 D • a)

def psib (z : B.BPt) (a : B.Yb z) : (FractionRing (B.Rl z))ˣ := B.taub z a (B.phib z (w0 D • a))

def IntR (z : B.BPt) (x : FractionRing (B.Rl z)) : Prop :=
  x ∈ (algebraMap (B.Rl z) (FractionRing (B.Rl z))).range

variable {y : L.Pt L.Xm} {nW : ℕ}

abbrev phiN (a : Fin nW → L.Ylat y) : Fin nW → B.chX y := fun i => B.phi y (a i)

def psiN (a : Fin nW → L.Ylat y) : ((L.fld y).C)ˣ := ∏ i, B.psiA y (a i)
def tauN (a : Fin nW → L.Ylat y) (χ : Fin nW → B.chX y) : ((L.fld y).C)ˣ := ∏ i, B.tau y (a i) (χ i)

def beN (χ : Fin nW → B.chX y) : ℝ :=
  ∑ i, L.be y ((B.phi y).symm (χ i)) ((B.phi y).symm (χ i))

def beMix (a : Fin nW → L.Ylat y) (χ : Fin nW → B.chX y) : ℝ :=
  ∑ i, L.be y (a i) ((B.phi y).symm (χ i))

variable (y nW)

def nfc (n : ℕ) (s : L.Sn y (L.latStd nW) n) (χ : Fin nW → B.chX y) : ℝ := B.nB (B.sgc y nW n χ s)

def NN (n : ℕ) : Set (L.Sn y (L.latStd nW) n) :=
  {s | ∀ χ, B.nfc y nW n s χ ≤ (p : ℝ) ^ (-(B.beN χ / (2 * (n : ℝ))))}

def QP (n : ℕ) (σ : ∀ χ, B.FB y nW n χ) : Prop :=
  ∀ (a : Fin nW → L.Ylat y) χ, σ (χ + n • B.phiN a) =
    (((B.psiN a) ^ n * B.tauN a χ : ((L.fld y).C)ˣ) : (L.fld y).C) • B.trB y nW n a χ (σ χ)

def IsRep (n : ℕ) (Rep : Set (Fin nW → B.chX y)) : Prop :=
  ∀ χ, ∃! χ₀, χ₀ ∈ Rep ∧ ∃ a : Fin nW → L.Ylat y, χ = χ₀ + n • B.phiN a

def SpanModP (b : Fin (L.dP y) → B.chX y) : Prop :=
  ∀ χ : B.chX y, ∃ (c : Fin (L.dP y) → ℤ) (χ' : B.chX y), χ = ∑ k, c k • b k + p • χ'

def SS (DF : ℕ) (b : Fin (L.dP y) → B.chX y) : Set (Fin nW → B.chX y) :=
  {χ | ∃ m : Fin nW → Fin (L.dP y) → ℕ, ∑ i, ∑ k, m i k ≤ DF ∧ ∀ i, χ i = ∑ k, m i k • b k}

def Mul : Prop :=
  ∀ {Z : L.Mdl} (y : L.Pt Z) (a b : L.Ylat y),
    B.multiplicationLatticeFirst y a b = B.phi y b ∧ B.multiplicationLatticeSecond y a b = B.phi y a ∧ B.mulC y a b = B.tau y a (B.phi y b)

def FER : Prop :=
  ∀ z (s : B.Sg z) (a : B.Yb z) (χ : B.Xb z),
    B.fc z s (χ + B.phib z a) =
      algebraMap (B.Rl z) (FractionRing (B.Rl z)) (B.trU z a χ : B.Rl z) *
        (B.psib z a : FractionRing (B.Rl z)) * (B.taub z a χ : FractionRing (B.Rl z)) * B.fc z s χ

def RegR : Prop :=
  ∀ z, (∀ s ∈ B.Sreg z, ∀ χ, B.IntR z (B.fc z s χ)) ∧
    (∀ s : B.Sg z, ∃ a : B.Rl z, a ≠ 0 ∧ a • s ∈ B.Sreg z) ∧
    (∀ s ∈ B.Sreg z, ∀ a : B.Rl z, a ≠ 0 →
      (∀ χ, ∃ c : B.Rl z, B.fc z s χ = algebraMap (B.Rl z) (FractionRing (B.Rl z)) (a * c)) →
      ∃ s' ∈ B.Sreg z, s = a • s') ∧
    Function.Injective (B.fc z) ∧
    Module.finrank (FractionRing (B.Rl z)) (B.Sg z) = 1

def LocFree : Prop :=
  ∀ z, (∀ s, s ∈ B.Sreg z ↔ ∀ χ, B.IntR z (B.fc z s χ)) ∧
    Module.Free (B.Rl z) (B.Sreg z) ∧ Module.finrank (B.Rl z) (B.Sreg z) = 1

def Desc : Prop :=
  (∀ z, Module.Free (B.Rl z) (B.Sreg z) ∧ Module.finrank (B.Rl z) (B.Sreg z) = 1) → L.IsInv L.piPP

def Fou : Prop :=
  ∀ y nW n, 0 < n → (∀ s, B.QP y nW n fun χ => B.sgc y nW n χ s) ∧
    ∀ Rep, B.IsRep y nW n Rep → ∀ σ : ∀ χ, B.FB y nW n χ, ∃! s, ∀ χ ∈ Rep, B.sgc y nW n χ s = σ χ

def FreeB : Prop :=
  ∀ y nW n, 0 < n → ∀ χ, ∃ b : Module.Basis (Fin (n ^ (B.dimB y * nW))) (L.fld y).C (B.FB y nW n χ),
    ∀ a : Fin (n ^ (B.dimB y * nW)) → (L.fld y).C, B.nB (∑ i, a i • b i) = ⨆ i, ‖a i‖

def ActF : Prop :=
  ∀ y nW n, ModuliIntegralCharts.NHyp D p n → ∀ g : L.Th y (L.latStd nW) n,
    ∃ (a : Fin nW → L.Ylat y) (K : ℝ), 0 < K ∧ ∀ s χ,
      B.nfc y nW n (L.act y _ n g s) (χ + B.phiN a) =
        K * (p : ℝ) ^ (-(B.beMix a χ / (n : ℝ))) * B.nfc y nW n s χ

def Perf (L : ModuliIntegralCharts.Loc D r j p) : Prop :=
  ∀ y La n, 0 < n → ∀ g : L.Th y La n, (∀ h, g * h = h * g) → ∃ a, L.scal y La n a = g

def VthF : Prop :=
  ∀ y nW, B.nfc y nW 1 (B.th1 y nW) 0 = 1 ∧
    ∀ n, ModuliIntegralCharts.NHyp D p n → ∀ s,
      (∀ χ, B.nfc y nW n (B.pbAl y nW n s) (B.alp n • χ) = B.nfc y nW 1 s χ) ∧
      ∀ χ : Fin nW → B.chX y, (¬ ∃ χ' : Fin nW → B.chX y, χ = B.alp n • χ') → B.nfc y nW n (B.pbAl y nW n s) χ = 0

def JetB : Prop :=
  ∀ y nW n DF, 3 * DF + 2 ≤ n → ∀ b, B.SpanModP y b →
    ∀ v ∈ L.intJet y (L.latStd nW) n DF, v ∈ ModuliIntegralCharts.Ospan (C := (L.fld y).C)
      {u | ∃ χ ∈ B.SS y nW DF b, ∃ σ : B.FB y nW n χ, B.nB σ ≤ 1 ∧ u = B.jX y nW n DF χ σ}

end LocB

variable (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D)

def adm1 : Prop := ModuliIntegralCharts.Conclusion4 D X

def adm2 : Prop := ModuliIntegralCharts.adm2 D X

def adm3 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).Mul

def ArchimedeanSignatureMatching (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).FER ∧ (Y.loc w p hp).RegR

def adm5 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).Desc

def adm6 : Prop :=
  ∀ w p, p.Prime → ∀ (c : ℕ) (kf : X.KF (D.R.f * X.rk w) c) (y : (X.loc w p).Pt (X.loc w p).Xm),
    (X.loc w p).good y → (X.loc w p).nrm ((X.loc w p).keySh c) (X.pbKF w p kf) y = 1

def adm7 (Y : Prov D X) : Prop :=
  ∀ w p hp (c : ℕ) (kf : X.KF (D.R.f * X.rk w) c), (∃ N : ℝ, ∀ z, X.kfNorm kf z = N) →
    ∃ φ : (X.loc w p).GIso (Y.loc w p hp).oX ((X.loc w p).keySh c),
      (Y.loc w p hp).secOf φ = X.pbKF w p kf

def adm8 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).Fou

def adm9 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).FreeB

def adm10 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).ActF ∧ LocB.Perf (X.loc w p)

def adm11 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).VthF

def adm12 (Y : Prov D X) : Prop := ∀ w p hp, (Y.loc w p hp).JetB

def adm13 : Prop := ModuliIntegralCharts.Conclusion2 D X

def adm14 : Prop := ModuliIntegralCharts.PointsLemma D X

def adm15 : Prop := ModuliIntegralCharts.Conclusion5 D X

def adm16 : Prop := ModuliIntegralCharts.adm1 D X

def admitted (Y : Prov D X) : Prop :=
  adm1 D X ∧ adm2 D X ∧ adm3 D X Y ∧ ArchimedeanSignatureMatching D X Y ∧ adm5 D X Y ∧ adm6 D X ∧ adm7 D X Y ∧ adm8 D X Y ∧
    adm9 D X Y ∧ adm10 D X Y ∧ adm11 D X Y ∧ adm12 D X Y ∧ adm13 D X ∧ adm14 D X ∧ adm15 D X ∧ adm16 D X

def PoincareBundleExtensionCond (Y : Prov D X) : Prop :=
  ∀ w p hp La, ∃ P : (Y.loc w p hp).StrictHenselianAcyclic La,
    (Y.loc w p hp).res2 P = (Y.loc w p hp).PoiQ La ∧ (Y.loc w p hp).biext P ∧
    (X.loc w p).symmG ((Y.loc w p hp).dg P) ∧ (X.loc w p).rigG ((Y.loc w p hp).dg P) ∧
    ∀ y, ∃ M : (X.loc w p).LBB y La, (X.loc w p).principal M ∧
      (X.loc w p).resGt ((Y.loc w p hp).dg P) y = (X.loc w p).prPull M

def ZeroGainValuation (Y : Prov D X) : Prop :=
  ∀ w p hp (Z : (X.loc w p).Mdl) (y : (X.loc w p).Pt Z) (a : (X.loc w p).Ylat y),
    (Y.loc w p hp).shiftA y a = (Y.loc w p hp).phi y a ∧
    (Y.loc w p hp).psiA y a = (Y.loc w p hp).tau y a ((Y.loc w p hp).phi y (w0 D • a)) ∧
    (X.loc w p).psiV y a = (X.loc w p).be y a a / 2

def Conclusion1 (Y : Prov D X) : Prop := PoincareBundleExtensionCond D X Y ∧ ZeroGainValuation D X Y

def Conclusion2 (Y : Prov D X) : Prop :=
  ∀ w p hp, (X.loc w p).IsInv (X.loc w p).piPP ∧ (Y.loc w p hp).LocFree

def PointsLemma (ka : ℝ) : Prop := ModuliIntegralCharts.Conclusion8 D X ka ∧ ModuliIntegralCharts.KeyFormulaLineBundle D X ka

def Conclusion4 (Y : Prov D X) : Prop :=
  ∀ w p hp (y : (X.loc w p).Pt (X.loc w p).Xm) (n : ℕ), ModuliIntegralCharts.NHyp D p n →
    (∀ La (x : (X.loc w p).At y La n), ∃! g : (X.loc w p).Th y La n,
        (X.loc w p).ovr y La n g = Multiplicative.ofAdd x ∧ (X.loc w p).dl y La n g = g⁻¹ ∧ g ^ n = 1) ∧
    ∀ nW : ℕ,
      (∃ b : Fin (n ^ (D.R.f * X.rk w * nW)) → (X.loc w p).Sn y ((X.loc w p).latStd nW) n,
        (∀ i, b i ∈ (Y.loc w p hp).NN y nW n) ∧
        ∀ s ∈ (Y.loc w p hp).NN y nW n,
          ∃! a : Fin (n ^ (D.R.f * X.rk w * nW)) → ((X.loc w p).fld y).C,
            (∀ i, ‖a i‖ ≤ 1) ∧ s = ∑ i, a i • b i) ∧
      ∀ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg →
        (∀ x, (X.loc w p).act y _ n (sg x) ((X.loc w p).vth y _ n) ∈ (Y.loc w p hp).NN y nW n) ∧
        ∀ s ∈ (Y.loc w p hp).NN y nW n,
          ∃ a : (X.loc w p).At y ((X.loc w p).latStd nW) n → ((X.loc w p).fld y).C,
            (∀ x, ‖a x‖ ≤ 1) ∧ s = ∑ x, a x • (X.loc w p).act y _ n (sg x) ((X.loc w p).vth y _ n)

def Conclusion5 : Prop := ModuliIntegralCharts.LinkConditions D X

def IntegralChartJetBound : Prop := ModuliIntegralCharts.jet_form_downstream' D X

def Conclusion6 : Prop := ModuliIntegralCharts.RunConditions D X

def Stmt (Y : Prov D X) (ka : ℝ) : Prop :=
  admitted D X Y → Conclusion1 D X Y ∧ Conclusion2 D X Y ∧ PointsLemma D X ka ∧ Conclusion4 D X Y ∧ Conclusion5 D X ∧ Conclusion6 D X

def BoundsOfCoreAdmissibleData (Y : Prov D X) (ka : ℝ) : Prop :=
  admitted D X Y → ZeroGainValuation D X Y ∧ Conclusion2 D X Y ∧ ModuliIntegralCharts.KeyFormulaLineBundle D X ka ∧ Conclusion4 D X Y ∧ Conclusion5 D X

theorem Ospan_smul {C V : Type} [NormedField C] [AddCommGroup V] [Module C V] (S : Set V) (a : C)
    (ha : ‖a‖ ≤ 1) {v : V} (hv : v ∈ ModuliIntegralCharts.Ospan (C := C) S) : a • v ∈ ModuliIntegralCharts.Ospan (C := C) S := by
  unfold ModuliIntegralCharts.Ospan at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a * b, ?_, s, hs, by rw [mul_smul]⟩
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem jetBoundDownstream_of_jetBound (h : Conclusion5 D X) : IntegralChartJetBound D X := by
  intro w p hp n DF nW hn h3 y sg hsg t' ht' v hv
  obtain ⟨t, ht, h⟩ := (h w p hp n DF nW hn h3 y).2 sg hsg
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-((X.loc w p).cJ y n DF * (X.loc w p).phiCy y)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, norm_zero] at ht; linarith
  have : t' • v = (t' / t) • (t • v) := by
    rw [smul_smul, div_mul_cancel₀ _ ht0]
  rw [this]
  refine Ospan_smul _ _ ?_ (h v hv)
  rw [norm_div]
  exact div_le_one_of_le₀ (ht'.trans ht) (norm_nonneg _)

theorem finiteModel_of_heckeEstimate (Y : Prov D X) (h1 : Conclusion1 D X Y) (h2 : Conclusion2 D X Y) : ModuliIntegralCharts.division_rows_rational_lattice D X := by
  intro w p hp
  refine ⟨fun La => ?_, fun Z y a => (h1.2 w p hp Z y a).2.2, (h2 w p hp).1⟩
  obtain ⟨P, hP, -, hs, hr, hM⟩ := h1.1 w p hp La
  exact ⟨(Y.loc w p hp).dg P, by rw [(Y.loc w p hp).dg_res, hP, (Y.loc w p hp).PPq_def], hs, hr, hM⟩

abbrev ObjClass : Type 1 := ∀ {D : Formalism.BasicNotions.D7} {X : ModuliIntegralCharts.Prov D}, Prov D X → Prop

def UniformExportStatement (𝒪 : ObjClass) (ka : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) (Y : Prov D X), 𝒪 Y → Stmt D X Y ka

def Comparison₂ (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) (Y : Prov D X) (ka : ℝ) : Prop :=
  PoincareBundleExtensionCond D X Y ∧ ModuliIntegralCharts.Conclusion8 D X ka ∧ Conclusion6 D X

def TieClass (ka : ℝ) : ObjClass := fun {D} {X} Y => Comparison₂ D X Y ka

theorem essentialPacket_of_packet {D : Formalism.BasicNotions.D7} {X : ModuliIntegralCharts.Prov D} {Y : Prov D X} {ka : ℝ} (h : Stmt D X Y ka) :
    BoundsOfCoreAdmissibleData D X Y ka :=
  fun a => ⟨(h a).1.2, (h a).2.1, (h a).2.2.1.2, (h a).2.2.2.1, (h a).2.2.2.2.1⟩

theorem packet_of_essential_of_clauses {D : Formalism.BasicNotions.D7} {X : ModuliIntegralCharts.Prov D} {Y : Prov D X} {ka : ℝ} (h : BoundsOfCoreAdmissibleData D X Y ka)
    (t : Comparison₂ D X Y ka) : Stmt D X Y ka :=
  fun a => ⟨⟨t.1, (h a).1⟩, (h a).2.1, ⟨t.2.1, (h a).2.2.1⟩, (h a).2.2.2.1, (h a).2.2.2.2, t.2.2⟩

def UniformKeyFormulaOfAdmissible (ka : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) (Y : Prov D X), BoundsOfCoreAdmissibleData D X Y ka

theorem uniformPacket_clauseClass_of_essential {ka : ℝ} (h : UniformKeyFormulaOfAdmissible ka) : UniformExportStatement (TieClass ka) ka :=
  fun D X Y t => packet_of_essential_of_clauses (h D X Y) t

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

abbrev BaseObjectsAlongFamily : Type 1 := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ModuliIntegralCharts.Prov (Fm.D x i)

abbrev ProvF (XF : BaseObjectsAlongFamily Fm) : Type 1 := ∀ x hx (i : Fm.Ix x), Prov (Fm.D x i) (XF x hx i)

variable (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF)

def AdmFx : Prop := ∀ x hx (i : Fm.Ix x), admitted (Fm.D x i) (XF x hx i) (YF x hx i)

def familyPoincareExtensionAndPointBounds (ka : ℝ) : Prop :=
  ∀ x hx (i : Fm.Ix x),
    Conclusion1 (Fm.D x i) (XF x hx i) (YF x hx i) ∧ Conclusion2 (Fm.D x i) (XF x hx i) (YF x hx i) ∧
    PointsLemma (Fm.D x i) (XF x hx i) ka ∧ Conclusion4 (Fm.D x i) (XF x hx i) (YF x hx i) ∧
    Conclusion5 (Fm.D x i) (XF x hx i) ∧ Conclusion6 (Fm.D x i) (XF x hx i)

def FamilyPacketImplication (ka : ℝ) : Prop := AdmFx Fm XF YF → familyPoincareExtensionAndPointBounds Fm XF YF ka

def InClass (𝒪 : ObjClass) : Prop := ∀ x hx (i : Fm.Ix x), 𝒪 (YF x hx i)

theorem familyPacket_of_uniformPacket {𝒪 : ObjClass} {ka : ℝ} (h : UniformExportStatement 𝒪 ka) (hO : InClass Fm XF YF 𝒪) :
    FamilyPacketImplication Fm XF YF ka :=
  fun a x hx i => h _ _ _ (hO x hx i) (a x hx i)

theorem jetBoundDownstream_of_family {ka : ℝ} (h : familyPoincareExtensionAndPointBounds Fm XF YF ka) :
    ∀ x hx (i : Fm.Ix x), IntegralChartJetBound (Fm.D x i) (XF x hx i) :=
  fun x hx i => jetBoundDownstream_of_jetBound _ _ (h x hx i).2.2.2.2.1

def familyValuationAndKeyFormula (ka : ℝ) : Prop :=
  ∀ x hx (i : Fm.Ix x),
    ZeroGainValuation (Fm.D x i) (XF x hx i) (YF x hx i) ∧ Conclusion2 (Fm.D x i) (XF x hx i) (YF x hx i) ∧
    ModuliIntegralCharts.KeyFormulaLineBundle (Fm.D x i) (XF x hx i) ka ∧ Conclusion4 (Fm.D x i) (XF x hx i) (YF x hx i) ∧ Conclusion5 (Fm.D x i) (XF x hx i)

def FamilyKeyFormulaOfAdmissible (ka : ℝ) : Prop := AdmFx Fm XF YF → familyValuationAndKeyFormula Fm XF YF ka

theorem familyEssential_of_uniformEssential {ka : ℝ} (h : UniformKeyFormulaOfAdmissible ka) : FamilyKeyFormulaOfAdmissible Fm XF YF ka :=
  fun a x hx i => h _ _ _ (a x hx i)

theorem familyEssential_of_familyPacket {ka : ℝ} (h : FamilyPacketImplication Fm XF YF ka) : FamilyKeyFormulaOfAdmissible Fm XF YF ka :=
  fun a x hx i => ⟨(h a x hx i).1.2, (h a x hx i).2.1, (h a x hx i).2.2.1.2, (h a x hx i).2.2.2.1, (h a x hx i).2.2.2.2.1⟩

theorem familyPacket_of_familyEssential {ka : ℝ} (h : FamilyKeyFormulaOfAdmissible Fm XF YF ka) (t : InClass Fm XF YF (TieClass ka)) :
    FamilyPacketImplication Fm XF YF ka :=
  fun a x hx i => ⟨⟨(t x hx i).1, (h a x hx i).1⟩, (h a x hx i).2.1, ⟨(t x hx i).2.1, (h a x hx i).2.2.1⟩,
    (h a x hx i).2.2.2.1, (h a x hx i).2.2.2.2, (t x hx i).2.2⟩

theorem jetBound_of_familyEssential {ka : ℝ} (h : familyValuationAndKeyFormula Fm XF YF ka) :
    ∀ x hx (i : Fm.Ix x), Conclusion5 (Fm.D x i) (XF x hx i) :=
  fun x hx i => (h x hx i).2.2.2.2

end Family

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒪 : ObjClass) (ka : ℝ) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    ∀ (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF), InClass Fm XF YF 𝒪 → FamilyPacketImplication Fm XF YF ka)

theorem closed_absolute_share_of_uniform_export {𝒪 : ObjClass} {ka : ℝ} (h : UniformExportStatement 𝒪 ka) (𝒞 : Formalism.MainNotions.FamClass) :
    ClosedAbsoluteShare 𝒞 𝒪 ka :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ XF YF hO => familyPacket_of_uniformPacket Fm XF YF h hO⟩⟩

def ShareAbsoluteConstant (𝒞 : Formalism.MainNotions.FamClass) (𝒪 : ObjClass) : Prop := ∃ ka : ℝ, ClosedAbsoluteShare 𝒞 𝒪 ka

def ClosedFamilyKeyFormula (𝒞 : Formalism.MainNotions.FamClass) (ka : ℝ) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF), FamilyKeyFormulaOfAdmissible Fm XF YF ka)

theorem closedEssential_of_uniformEssential {ka : ℝ} (h : UniformKeyFormulaOfAdmissible ka) (𝒞 : Formalism.MainNotions.FamClass) : ClosedFamilyKeyFormula 𝒞 ka :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ XF YF => familyEssential_of_uniformEssential Fm XF YF h⟩⟩

def PacketAlongFamilyInClass (𝒪 : ObjClass) (ka : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF), InClass Fm XF YF 𝒪 → FamilyPacketImplication Fm XF YF ka

theorem packetAlongFamily_of_uniform {𝒪 : ObjClass} {ka : ℝ} (h : UniformExportStatement 𝒪 ka) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    PacketAlongFamilyInClass 𝒪 ka Fm :=
  fun XF YF hO => familyPacket_of_uniformPacket Fm XF YF h hO

theorem closedPacket_iff_alongFamily (𝒞 : Formalism.MainNotions.FamClass) (𝒪 : ObjClass) (ka : ℝ) :
    ClosedAbsoluteShare 𝒞 𝒪 ka ↔ Formalism.MainNotions.Closed 𝒞 (fun Fm _ => PacketAlongFamilyInClass 𝒪 ka Fm) := Iff.rfl

theorem uniformPacket_anti_class {𝒪 𝒪' : ObjClass} {ka : ℝ}
    (hs : ∀ {D : Formalism.BasicNotions.D7} {X : ModuliIntegralCharts.Prov D} (Y : Prov D X), 𝒪' Y → 𝒪 Y) (h : UniformExportStatement 𝒪 ka) : UniformExportStatement 𝒪' ka :=
  fun D X Y hY => h D X Y (hs Y hY)

end Formalism.MainNotions.BoundaryLocalData
