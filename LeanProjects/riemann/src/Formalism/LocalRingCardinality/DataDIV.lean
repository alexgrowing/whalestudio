import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.DegreeFormula.FlagDegFormula

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology MvPolynomial Finset

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions Formalism.DegreeFormula

structure Geo (F : Type) [Field F] [NumberField F] [StarRing F] where

  Var : Type

  dim : Var → ℕ

  Fn : Var → Type
  [fnField : ∀ Y, Field (Fn Y)]
  [fnAlg : ∀ Y, Algebra F (Fn Y)]

  Dv : Var → Type
  [dvGrp : ∀ Y, AddCommGroup (Dv Y)]

  Eff : ∀ Y, Dv Y → Prop
  eff_zero : ∀ Y, Eff Y 0
  eff_add : ∀ Y a b, Eff Y a → Eff Y b → Eff Y (a + b)

  H0 : ∀ Y, Dv Y → Submodule F (Fn Y)
  degreeZeroCohomology_finiteDimensional : ∀ Y Δ, FiniteDimensional F (H0 Y Δ)
  mul_mem_riemannRochSpace_add : ∀ Y Δ Δ' (f g : Fn Y), f ∈ H0 Y Δ → g ∈ H0 Y Δ' → f * g ∈ H0 Y (Δ + Δ')
  riemannRoch_mono : ∀ Y Δ Δ', Eff Y (Δ' - Δ) → H0 Y Δ ≤ H0 Y Δ'

  KY : ∀ Y, Dv Y

  Cl : Var → Type

  properCl : ∀ Y, Cl Y → Prop

  subCl : ∀ Y, Cl Y → Cl Y → Prop

  supp : ∀ Y, Dv Y → Cl Y

  inter : ∀ Y, (Fin (dim Y) → Dv Y) → ℤ

  nef : ∀ Y, Dv Y → Prop

  big : ∀ Y, Dv Y → Prop

  bpf : ∀ Y, Dv Y → Set (Fn Y) → Prop

  phiBir : ∀ Y, Dv Y → Set (Fn Y) → Prop

  phiNoContr : ∀ Y, Dv Y → Set (Fn Y) → Cl Y → Prop

  vanishOn : ∀ Y, Dv Y → Fn Y → Cl Y → Prop

  hdim : ∀ Y, ℕ → Dv Y → ℕ

  pts : ∀ Y, (F →+* ℂ) → Type
  [ptsMeas : ∀ Y σ, MeasurableSpace (pts Y σ)]

  vol : ∀ Y σ, Measure (pts Y σ)

  FnC : ∀ Y, (F →+* ℂ) → Type
  [fnCRing : ∀ Y σ, CommRing (FnC Y σ)]
  [fnCAlg : ∀ Y σ, Algebra ℂ (FnC Y σ)]

  cx : ∀ Y σ, Fn Y →+* FnC Y σ
  cx_smul : ∀ Y σ (a : F) (f : Fn Y), cx Y σ (a • f) = σ a • cx Y σ f

  Met : ∀ Y, (F →+* ℂ) → Dv Y → Type

  mAdd : ∀ Y σ Δ Δ', Met Y σ Δ → Met Y σ Δ' → Met Y σ (Δ + Δ')

  mPow : ∀ Y σ Δ (k : ℕ), Met Y σ Δ → Met Y σ (k • Δ)

  fsMet : ∀ Y σ Δ {k : Type} [Fintype k], (k → FnC Y σ) → Met Y σ Δ

  pn : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → pts Y σ → ℝ

  pnK : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → pts Y σ → ℝ

  mSmooth : ∀ Y σ Δ, Met Y σ Δ → Prop

  mPsh : ∀ Y σ Δ, Met Y σ Δ → (pts Y σ → ℝ) → Prop

  redZero : ∀ Y σ, Dv Y → (Fin (dim Y) → FnC Y σ) → Set (pts Y σ) → Prop

  agreeOn : ∀ Y σ, Dv Y → FnC Y σ → FnC Y σ → Set (pts Y σ) → Prop

  resNorm : ∀ Y σ Δ, Met Y σ Δ → ∀ Δs, Met Y σ Δs → (Fin (dim Y) → FnC Y σ) → FnC Y σ →
    pts Y σ → ℝ

  Adl : Var → Type

  ofW : ∀ Y (L : Dv Y) (W : HLat F), (W.V →ₗ[F] Fn Y) → Adl Y

  twist : ∀ Y, Adl Y → (InfinitePlace F → ℝ) → (HeightOneSpectrum (𝓞 F) → ℝ) → Adl Y

  arTop : ∀ Y, Adl Y → ℝ

  arVol : ∀ Y, Adl Y → ℝ

  nefA : ∀ Y, Adl Y → Prop

  supInf : ∀ Y, Adl Y → InfinitePlace F → ℕ → Fn Y → ℝ

  supFin : ∀ Y, Adl Y → HeightOneSpectrum (𝓞 F) → ℕ → Fn Y → ℝ

  cutGood : ∀ Y, Cl Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → Prop

  cutHt : ∀ Y, Adl Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ℝ

  cutOrd : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → Dv Y → Fn Y → ℕ

  resFull : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Fn Y) →
    Adl Y → Prop

  resDeg : ∀ Y (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Fn Y) → (Fin (dim Y) → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Fn Y) →
    Adl Y → ℝ

  supInf_ofW : ∀ Y (L : Dv Y) (W : HLat F) (ι : W.V →ₗ[F] Fn Y) (v : InfinitePlace F) (τ : ℕ)
    (f : Fn Y), supInf Y (ofW Y L W ι) v τ f =
      ⨆ y, Real.sqrt (pn Y v.embedding (τ • L) (mPow Y v.embedding L τ
        (fsMet Y v.embedding L (fun k : W.ι => ∑ i, (W.X v) i k • cx Y v.embedding (ι (W.b i)))))
        (cx Y v.embedding f) y)

  supInf_twist : ∀ Y (Lb : Adl Y) ci cf, (Function.support cf).Finite → ∀ (v : InfinitePlace F) (τ : ℕ) (f : Fn Y),
    supInf Y (twist Y Lb ci cf) v τ f = Real.exp (-((τ : ℝ) * ci v)) * supInf Y Lb v τ f
  supFin_twist : ∀ Y (Lb : Adl Y) ci cf, (Function.support cf).Finite → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ)
    (f : Fn Y), supFin Y (twist Y Lb ci cf) v τ f = Real.exp (-((τ : ℝ) * cf v)) * supFin Y Lb v τ f

  regOn : ∀ Y σ, Dv Y → FnC Y σ → Set (pts Y σ) → Prop

attribute [instance] Geo.fnField Geo.fnAlg Geo.dvGrp Geo.ptsMeas Geo.fnCRing Geo.fnCAlg

section Poly
variable (Tau : Type) [Fintype Tau] (N : ℕ)

abbrev Rt : Type := Tau × Fin N

abbrev Vm : Type := (Bool × Rt Tau N) ⊕ (Bool × ℕ)

def tagHT : MvPolynomial (Rt Tau N) ℝ →ₐ[ℝ] MvPolynomial (Vm Tau N) ℝ :=
  rename (fun x => Sum.inl (true, x))

def tagDR : MvPolynomial (Rt Tau N) ℝ →ₐ[ℝ] MvPolynomial (Vm Tau N) ℝ :=
  rename (fun x => Sum.inl (false, x))

end Poly

structure ShimX (Tau : Type) [Fintype Tau] where

  N : ℕ

  j : ℕ
  j_pos : 1 ≤ j
  j_lt : j < N

  lev : Finset ℕ
  lev_prime : ∀ p ∈ lev, p.Prime

  Comp : Type
  [compFin : Fintype Comp]
  [compNe : Nonempty Comp]

  vol : ℝ

  chern : MvPolynomial (Rt Tau N) ℝ →ₗ[ℝ] ℝ

  chern_homog : ∀ (P : MvPolynomial (Rt Tau N) ℝ) (d : ℕ), d ≠ dimFl Tau N → P.IsHomogeneous d →
    chern P = 0

  arDeg : Finset ℕ → ℝ → MvPolynomial (Rt Tau N) ℝ →ₗ[ℝ] ℝ
  arDeg_homog : ∀ S R (P : MvPolynomial (Rt Tau N) ℝ) (d : ℕ), d ≠ dimFl Tau N + 1 →
    P.IsHomogeneous d → arDeg S R P = 0

  arMix : Finset ℕ → ℝ → ℕ → MvPolynomial (Vm Tau N) ℝ →ₗ[ℝ] ℝ
  arMix_HT : ∀ S R p (P : MvPolynomial (Rt Tau N) ℝ),
    arMix S R p (tagHT Tau N P) = arDeg (insert p S) R P
  arMix_DR : ∀ S R p (P : MvPolynomial (Rt Tau N) ℝ),
    arMix S R p (tagDR Tau N P) = arDeg (S.erase p) R P

  CurveHT : ℕ → Type
  degHT : ∀ p, CurveHT p → Rt Tau N → ℝ

  CurveDR : ℕ → Type
  degDR : ∀ p, CurveDR p → Rt Tau N → ℝ

  FibComp : ℕ → Type
  fibInBd : ∀ p, FibComp p → Prop

  Pt : Type

  phiDR : ℕ → Pt → Rt Tau N → ℝ

  phiMod : ℕ → Pt → Rt Tau N → ℝ

  phiFr : ℕ → Pt → Rt Tau N → ℝ

  XC : Type
  rfn : XC → ℝ
  rfn_ge : ∀ z, Real.exp 1 ≤ rfn z
  hLo : XC → ℝ
  hUp : XC → ℝ
  hLo_le : ∀ z, 0 < hLo z ∧ hLo z ≤ hUp z
  connN : XC → ℝ
  curvN : XC → ℝ
  compOf : XC → Comp

  normDetInf : Tau → XC → ℝ

  compPt : Pt → Comp

  normDetT : ℕ → Tau → Pt → ℝ

  normDetH : ℕ → Tau → Pt → ℝ

  htDetT : ℝ → Comp → Tau → ℝ

  ALB : Type
  arSelf : ALB → ℝ
  arSelfC : ALB → Comp → ℝ
  arSelf_sum : ∀ L, arSelf L = ∑ c, arSelfC L c
  geo : ALB → ℝ
  geoC : ALB → Comp → ℝ
  geo_sum : ∀ L, geo L = ∑ c, geoC L c
  arVol : ALB → ℝ
  semipos : ALB → Prop
  nefFib : ALB → Prop
  arNef : ALB → Prop

  Mbar : ℝ → (Tau → Fin N → ℝ) → ℚ → ALB

attribute [instance] ShimX.compFin ShimX.compNe

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.BasicNotions.DV

namespace DV

abbrev KW (p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (WittVector p (AlgebraicClosure (ZMod p)))

def sgF (p : ℕ) [Fact p.Prime] : KW p ≃+* KW p :=
  WittVector.FractionRing.frobenius p (AlgebraicClosure (ZMod p))

abbrev Emb (D : D7) (p : ℕ) [Fact p.Prime] : Type := D.host.E →+* KW p

def phiPow (D : D7) {p : ℕ} [Fact p.Prime] (n : ℕ) (τ : Emb D p) : Emb D p :=
  ((sgF p : KW p →+* KW p) ^ n).comp τ

def cEmb (D : D7) {p : ℕ} [Fact p.Prime] (τ : Emb D p) : Emb D p :=
  τ.comp (D.host.conj : D.host.E →+* D.host.E)

def Unram (D : D7) (p : ℕ) : Prop :=
  ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
    ((p : 𝓞 D.host.E) ∈ w.asIdeal) → eWL D.host.E w = 1

structure ITh where

  LB : Type

  Ch : Type
  [ring : CommRing Ch]
  [alg : Algebra ℚ Ch]

  c1 : LB → Ch

  VDiv : Type
  [grp : AddCommGroup VDiv]
  [modQ : Module ℚ VDiv]

  cD : VDiv →ₗ[ℚ] Ch

  capDeg : VDiv →ₗ[ℚ] Ch →ₗ[ℚ] ℚ

  divP : VDiv

  cD_divP : cD divP = 0

  dim : ℕ

attribute [instance] ITh.ring ITh.alg ITh.grp ITh.modQ

structure FPair (Z : ITh) (r : ℕ) where

  x : Fin r → Z.LB

  x' : Fin r → Z.LB

  Dv : Fin r → Z.VDiv

  hx : ∀ i, Z.c1 (x' i) = Z.c1 (x i) - Z.cD (Dv i)

def Gk (Z : ITh) (k : ℕ) (y y' : Z.Ch) : Z.Ch :=
  ∑ a ∈ Finset.range k, y ^ a * y' ^ (k - 1 - a)

def ck {Z : ITh} {r : ℕ} (P : FPair Z r) (k : ℕ) (Q : Z.Ch) : ℚ :=
  ∑ i, Z.capDeg (P.Dv i) (Gk Z k (Z.c1 (P.x i)) (Z.c1 (P.x' i)) * Q)

def chk {Z : ITh} {r : ℕ} (P : FPair Z r) (k : ℕ) (Q : Z.Ch) : ℝ :=
  (ck P k Q : ℝ) / (Nat.factorial k : ℝ)

def chDiv {Z : ITh} {r : ℕ} (x : Fin r → Z.LB) (i : ℕ) (Q : Z.Ch) : ℝ :=
  (Z.capDeg Z.divP ((∑ l, Z.c1 (x l) ^ i) * Q) : ℝ) / (Nat.factorial i : ℝ)

def evQ (Z : ITh) (Q : MvPolynomial Z.LB ℚ) : Z.Ch := MvPolynomial.aeval Z.c1 Q

structure Mdl (D : D7) (p : ℕ) [Fact p.Prime] (N : ℕ) (rk : Emb D p → ℕ) where

  Z : ITh

  cov : ℕ
  cov_pos : 0 < cov

  lvl : ℕ

  lie : ∀ τ : Emb D p, FPair Z (rk τ)

  om : ∀ τ : Emb D p, FPair Z (N - rk τ)

  lieW : FPair Z (D.R.f * N)

  omW : FPair Z (D.R.f * N)

  om_dual : ∀ τ : Emb D p, ∃ e : Fin (N - rk τ) ≃ Fin (rk (cEmb D τ)),
    ∀ i, Z.c1 ((om τ).x i) = - Z.c1 ((lie (cEmb D τ)).x (e i))

  dim_eq : Z.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1

  omW_dual : ∃ e : Fin (D.R.f * N) ≃ Fin (D.R.f * N),
    ∀ i, Z.c1 (omW.x i) = - Z.c1 (lieW.x (e i))

def rkOf {D : D7} {p : ℕ} [Fact p.Prime] (Ps : Set (Emb D p)) (N j : ℕ) (τ : Emb D p) : ℕ := by
  classical exact if τ ∈ Ps then j else N - j

section Glob
variable (D : D7)

abbrev EmbC : Type := D.what₂.Tau ⊕ D.what₂.Tau

def toGG : EmbC D → D.R.GG
  | Sum.inl τ => ((D.eTau τ : D.R.Psi) : D.R.GG)
  | Sum.inr τ => ((D.eTau τ : D.R.Psi) : D.R.GG) * D.R.cc

open Classical in

def ofGG (g : D.R.GG) : EmbC D :=
  if h : g ∈ D.R.Psi then Sum.inl (D.eTau.symm ⟨g, h⟩)
  else if h' : g * D.R.cc ∈ D.R.Psi then
    Sum.inr (D.eTau.symm ⟨g * D.R.cc, h'⟩)
  else Sum.inl (D.eTau.symm 1)

def tauEmb (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

open Classical in

def frobG (p : ℕ) : D.R.GG :=
  if h : ∃ g : D.R.GG, ∀ (P : Ideal (NumberField.RingOfIntegers D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P
  then h.choose else 1

def frobEmb (p n : ℕ) (σ : EmbC D) : EmbC D := ofGG D (toGG D σ * frobG D p ^ n)

variable (N : ℕ)

def pk (τ : D.what₂.Tau) (k : ℕ) : MvPolynomial (Rt D.what₂.Tau N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def chTot (k : ℕ) : MvPolynomial (Rt D.what₂.Tau N) ℝ :=
  C ((Nat.factorial k : ℝ)⁻¹) * ∑ τ : D.what₂.Tau, ∑ i : Fin N, (X (τ, i) ^ k + (-X (τ, i)) ^ k)

def collapse : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Rt D.what₂.Tau N) ℝ :=
  aeval (fun v => match v with
    | Sum.inl (_, x) => X x
    | Sum.inr (_, k) => chTot D N k)

variable {D N}

def chLie (j : ℕ) (k : ℕ) : EmbC D → MvPolynomial (Rt D.what₂.Tau N) ℝ
  | Sum.inl τ => C ((Nat.factorial k : ℝ)⁻¹) *
      ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k
  | Sum.inr τ => C ((Nat.factorial k : ℝ)⁻¹) *
      ∑ i ∈ univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-X (τ, i)) ^ k

variable (D N)

def chLieA (j k : ℕ) : MvPolynomial (Rt D.what₂.Tau N) ℝ :=
  ∑ τ : D.what₂.Tau, (chLie j k (Sum.inl τ) + chLie j k (Sum.inr τ))

end Glob

def PsiOf (D : D7) {p : ℕ} [Fact p.Prime] (jc : KW p →+* ℂ) : Set (Emb D p) :=
  {τ | ∃ τ0 : D.what₂.Tau, jc.comp τ = tauEmb D τ0}

end DV

def DV.kapW (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin D.R.r) : ℤ :=
  if h : i.1 < (D.R.sigW j).1 then D.what₂.kaBig j τ ⟨i.1, h⟩ + ((D.R.nV / 2 : ℕ) : ℤ)
  else if h' : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2 then
    D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, h'⟩ - ((D.R.nV / 2 : ℕ) : ℤ)
  else 0

def DV.UnramE (D : D7) (p : ℕ) : Prop :=
  ¬ p ∣ (NumberField.discr D.host.E).natAbs

structure DivX (D : D7) : Type 1 where

  geo : DV.Geo D.what₂.LL

  Lev : Type
  levPr : Lev → Finset ℕ

  shv : letI := D.host.cmStar; HSpace D.host.E → Lev → DV.ShimX D.what₂.Tau

  shv_N : letI := D.host.cmStar; ∀ S κ, 2 ≤ S.rank → (shv S κ).N = S.rank
  shv_lev : letI := D.host.cmStar; ∀ S κ, (shv S κ).lev = levPr κ

  PlP : ∀ (p : ℕ) [Fact p.Prime], Type
  [plpFin : ∀ (p : ℕ) [Fact p.Prime], Fintype (PlP p)]
  plpNe : ∀ (p : ℕ) [Fact p.Prime], Nonempty (PlP p)
  wtP : ∀ (p : ℕ) [Fact p.Prime], PlP p → ℝ
  divisorWeight_nonneg : ∀ (p : ℕ) [Fact p.Prime] (la : PlP p), 0 ≤ wtP p la
  divisorWeight_sum : ∀ (p : ℕ) [Fact p.Prime], ∑ la, wtP p la = 1

  plP : ∀ (p : ℕ) [Fact p.Prime], PlP p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}

  divisorWeight_def : ∀ (p : ℕ) [Fact p.Prime] (la : PlP p),
    wtP p la = (D.what₂.places.ramIdx (plP p la).1 : ℝ) *
      (padicValNat p (Ideal.absNorm (D.plEq (plP p la).1).asIdeal) : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)

  jC : ∀ (p : ℕ) [Fact p.Prime], PlP p → (DV.KW p →+* ℂ)

  Mp : letI := D.host.cmStar; ∀ (_S : HSpace D.host.E) (_κ : Lev) (p : ℕ) [Fact p.Prime], PlP p → Type

  md : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime] (la : PlP p),
    Mp S κ p la →
      DV.Mdl D p (shv S κ).N (DV.rkOf (DV.PsiOf D (jC p la)) (shv S κ).N (shv S κ).j)

  vdd : ℕ → D.what₂.Tau → ℝ
  vdd_unram : ∀ p τ, DV.UnramE D p → vdd p τ = 0

  phiFr_unram : letI := D.host.cmStar; ∀ S κ p y x, DV.UnramE D p →
    (shv S κ).phiFr p y x = (shv S κ).phiDR p y x

  vdd_nonneg : ∀ p τ, 0 ≤ vdd p τ

  CurveM : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p), Mp S κ p la → Type
  degM : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p) (z : Mp S κ p la), CurveM S κ p la z → DV.Rt D.what₂.Tau (shv S κ).N → ℝ

  htMdl : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p), Mp S κ p la
  htCurve : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime],
    (shv S κ).CurveHT p ≃ Σ la : PlP p, CurveM S κ p la (htMdl S κ p la)
  htCurve_deg : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (c : (shv S κ).CurveHT p),
    degM S κ p (htCurve S κ p c).1 (htMdl S κ p (htCurve S κ p c).1) (htCurve S κ p c).2 =
      (shv S κ).degHT p c

  MjH : ℕ → HLat D.what₂.LL
  MjH_good : ∀ j, (MjH j).Good

  jM : ∀ j, (MjH j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  jM_basis : ∀ j, LinearIndependent ℂ (fun i => jM j ((MjH j).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jM j ((MjH j).b i))) = ⊤

  jM_lat : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ (MjH j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jM j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  MjLat_sub : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM j)

  jM_metric : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (MjH j).b (MjH j).X
    (InfinitePlace.mk D.what₂.embLL) x) = ‖jM j x‖

  Qp : D.what₂.Tup → Finset ℕ

  degreeZero_partial_set_empty : Qp D.what₂.mu0 = ∅

  Qp_muAt : ∀ w, D.what₂.places.resChar w ∉ Qp (D.what₂.muAt w)

  Qp_g : ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ i, D.host.g i ∉ Qp μ

  QPl : D.what₂.Tup → Type
  [finQ : ∀ μ, Fintype (QPl μ)]

  qv : ∀ μ, QPl μ → ℕ

  qv_gt : ∀ μ v, 1 < qv μ v

  qv_char : ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ v, ∃ p ∈ Qp μ, p.Prime ∧ qv μ v = p

  nu : ∀ μ, QPl μ → ℕ → ℂ
  nu_ne : ∀ μ v i, nu μ v i ≠ 0

  nu_abs : ∀ μ v i, ‖nu μ v i‖ = 1

  ZQ : ∀ μ, QPl μ → ℕ → ℂ

  quotientLocalValueFirst : ∀ μ, QPl μ → ℂ

  typeDim : ∀ μ, QPl μ → ℕ → ℕ

  Comp : ℕ → Type
  [compFin : ∀ j, Fintype (Comp j)]

  degHH : ∀ j, Comp j → D.what₂.Tau → ℝ

  Yv : ∀ j, Comp j → geo.Var

  Ybd : ∀ j c, geo.Cl (Yv j c)

  Lw : ∀ j c, (D.what₂.Tau → Fin D.R.r → ℤ) →+ geo.Dv (Yv j c)

  iMj : ∀ j c, (MjH j).V →ₗ[D.what₂.LL] geo.Fn (Yv j c)
  iMj_mem : ∀ j c x, iMj j c x ∈ geo.H0 (Yv j c) (Lw j c (DV.kapW D j))

  logLam : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ

  logLam_base : ∀ j σ, logLam j σ D.what₂.embLL = Real.log (D.what₂.lamP D.what₂.mu0 j σ)

  kapR : (D.what₂.LL →+* ℂ) → ℝ
  kapR_pos : ∀ e, 0 < kapR e

  kapR_conj : ∀ e, kapR (NumberField.ComplexEmbedding.conjugate e) = kapR e

  Surf : Type
  surfCh2 : Surf → ℝ
  surfDegOm : Surf → ℝ
  SurfFp : Type
  surfFpCh2 : SurfFp → ℝ

attribute [instance] DivX.finQ DivX.compFin DivX.plpFin

def DV.LogLamConj (D : D7) (X : DivX D) : Prop :=
  ∀ j π e, X.logLam j π (NumberField.ComplexEmbedding.conjugate e) = X.logLam j π e

def DV.MjRank (D : D7) (X : DivX D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (X.MjH j).rank = D.what₂.D0

def DV.HidaSetting (D : D7) (XD : DivX D) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev) : Prop :=
  letI := D.host.cmStar
  2 ≤ S.rank ∧ S.SigOK ∧
  (∀ τ : D.what₂.Tau, S.sig (DV.tauEmb D τ) = ((XD.shv S κ).j, (XD.shv S κ).N - (XD.shv S κ).j)) ∧
  2 < D.R.f * ((XD.shv S κ).N - 1)

end Formalism.BasicNotions

end
