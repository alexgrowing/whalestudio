import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

structure PtGeo (l : ℕ) [Fact l.Prime] (Λ : Type) [AddCommGroup Λ] (σ : Type) where

  BB : Type
  [acgBB : AddCommGroup BB]
  tor_fin : ∀ N : ℕ, N ≠ 0 → Finite {z : BB // N • z = 0}

  Sec : ℕ → Type
  [acgSec : ∀ k, AddCommGroup (Sec k)]
  [modSec : ∀ k, Module ℂ_[l] (Sec k)]
  s : Sec 1

  nrm : ∀ k, Sec k → BB → ℝ
  nrm_nonneg : ∀ k F x, 0 ≤ nrm k F x
  nrm_smul : ∀ k (c : ℂ_[l]) F x, nrm k (c • F) x = ‖c‖ * nrm k F x
  nrm_add : ∀ k F F' x, nrm k (F + F') x ≤ max (nrm k F x) (nrm k F' x)

  pull : ∀ N : ℕ, Sec 1 →ₗ[ℂ_[l]] Sec (N ^ 2)
  pull_isom : ∀ N : ℕ, N ≠ 0 → ∀ F x, nrm (N ^ 2) (pull N F) x = nrm 1 F (N • x)

  Up : ∀ N : ℕ, BB → (Sec (N ^ 2) ≃ₗ[ℂ_[l]] Sec (N ^ 2))
  Up_fin : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ m : ℕ, m ≠ 0 ∧ (Up N z) ^ m = 1

  Up_cube : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ ph : BB → ℝ,
    (∀ F x, nrm (N ^ 2) (Up N z F) x = Real.exp (ph x) * nrm (N ^ 2) F (x + z)) ∧
    (∃ C, ∀ x, |ph x| ≤ C) ∧
    ∃ c, ∀ x x' x'', ph (x + x' + x'') - ph (x + x') - ph (x + x'') - ph (x' + x'') + ph x + ph x' + ph x''
      - ph 0 = c

  Gt : Type
  [acgGt : AddCommGroup Gt]
  Y : Type
  [acgY : AddCommGroup Y]
  per : Y →+ Gt
  unif : Gt →+ BB

  YR : Type
  [acgYR : AddCommGroup YR]
  [modYR : Module ℝ YR]
  iY : Y →+ YR
  Bf : YR →ₗ[ℝ] YR →ₗ[ℝ] ℝ
  w0 : YR →ₗ[ℝ] YR
  w0b : YR →ₗ[ℝ] YR

  chr : Y → Gt → ℂ_[l]
  cst : Y → ℂ_[l]
  trop : Gt →+ YR

  SecM : Type
  [acgSecM : AddCommGroup SecM]
  [modSecM : Module ℂ_[l] SecM]
  nrmM : SecM → Gt → ℝ
  nrmM_smul : ∀ (c : ℂ_[l]) F g, nrmM (c • F) g = ‖c‖ * nrmM F g
  nrmM_add : ∀ F F' g, nrmM (F + F') g ≤ max (nrmM F g) (nrmM F' g)
  up : Sec 1 →ₗ[ℂ_[l]] SecM
  be : SecM
  trY : Y → SecM →ₗ[ℂ_[l]] SecM

  Co : Type
  [finCo : Fintype Co]
  ser : ∀ k, Sec k →ₗ[ℂ_[l]] MvPowerSeries Co ℂ_[l]

  H : Type
  [acgH : AddCommGroup H]
  [modH : Module ℂ_[l] H]
  HO : AddSubgroup H
  HO_smul : ∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∀ h ∈ HO, c • h ∈ HO
  Fil : Submodule ℂ_[l] H
  curv : H →ₗ[ℂ_[l]] H →ₗ[ℂ_[l]] ℂ_[l]

  Gm : ℕ → Type
  [acgGm : ∀ k, AddCommGroup (Gm k)]
  [modGm : ∀ k, Module ℂ_[l] (Gm k)]
  germ : ∀ k, Sec k →ₗ[ℂ_[l]] Gm k
  pullG : ∀ N : ℕ, Gm 1 →ₗ[ℂ_[l]] Gm (N ^ 2)
  pullG_germ : ∀ N F, pullG N (germ 1 F) = germ (N ^ 2) (pull N F)
  pullG_inj : ∀ N : ℕ, N ≠ 0 → Function.Injective (pullG N)
  ev0 : ∀ k, Gm k →ₗ[ℂ_[l]] ℂ_[l]
  ev_zero_pull_square : ∀ N G, ev0 (N ^ 2) (pullG N G) = ev0 1 G
  IntG : ∀ k, AddSubgroup (Gm k)
  IntG_smul : ∀ k (c : ℂ_[l]), ‖c‖ ≤ 1 → ∀ G ∈ IntG k, c • G ∈ IntG k
  integral_ev_zero_norm_le_one : ∀ k, ∀ G ∈ IntG k, ‖ev0 k G‖ ≤ 1
  IntG_iff : ∀ k F, germ k F ∈ IntG k ↔ ∀ m, ‖MvPowerSeries.coeff m (ser k F)‖ ≤ 1

  nab : ∀ k, H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm k)
  nabD : H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm 1)

  EL : Set (σ → H)
  lf : σ → H
  lf_mem : lf ∈ EL

  half : ℕ → BB → BB
  half_spec : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 → N • half N z = z
  Uz : ℕ → BB → Gm 1
  Uz_def : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 →
    pullG N (Uz N z) = germ (N ^ 2) (Up N (half N z) (pull N s))

  kr : ℕ → Λ → BB → ℂ_[l]
  kr_per : ∀ (N : ℕ) x w z, kr N (x + N • w) z = kr N x z
  kr_int : ∀ N x z, ‖kr N x z‖ ≤ 1

  key : ℂ_[l]
  key_ne : key ≠ 0

attribute [instance] PtGeo.acgBB PtGeo.acgSec PtGeo.modSec PtGeo.acgGt PtGeo.acgY PtGeo.acgYR PtGeo.modYR
  PtGeo.acgSecM PtGeo.modSecM PtGeo.finCo PtGeo.acgH PtGeo.modH PtGeo.acgGm PtGeo.modGm

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

def mon {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (m : σ →₀ ℕ) : Module.End ℂ_[l] (X.Gm k) :=
  (ord.map fun u => (Dl (L u)) ^ (m u)).prod

def PN {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (P : MvPolynomial σ ℂ_[l]) (g : X.Gm k) : ℂ_[l] :=
  ∑ m ∈ P.support, P.coeff m * X.ev0 k (X.mon ord Dl L m g)

def hat (N e : ℕ) (φ : Λ → ℂ_[l]) (z : X.BB) : ℂ_[l] :=
  ((N : ℂ_[l]) ^ e)⁻¹ * ∑ᶠ c : Λ ⧸ (nsmulAddMonoidHom (α := Λ) N).range,
    φ (Quotient.out c) * X.kr N (Quotient.out c) z

def fG (N e : ℕ) (φ : Λ → ℂ_[l]) : X.Gm 1 :=
  ∑ᶠ z : {z : X.BB // N • z = 0}, X.hat N e φ z.1 • X.Uz N z.1

def Bas : Set (X.Gm 1) := {g | ∃ N : ℕ, N ≠ 0 ∧ ∃ F, X.pullG N g = X.germ (N ^ 2) F}

def Ray : Prop :=
  Function.Surjective X.unif ∧ (∀ g, X.unif g = 0 ↔ g ∈ X.per.range) ∧ (∀ z, X.trop (X.per z) = X.iY z) ∧
  (∀ u u', X.Bf u u' = X.Bf u' u) ∧ (∀ u, 0 ≤ X.Bf u u) ∧ (∀ u u', X.Bf (X.w0 u) u' = X.Bf u (X.w0b u')) ∧
  (∀ u, X.w0 u + X.w0b u = u) ∧
  (∀ z' g, ‖X.chr z' g‖ = (l : ℝ) ^ (-(X.Bf (X.trop g) (X.iY z')))) ∧
  (∀ z, ‖X.cst z‖ = (l : ℝ) ^ (-(X.Bf (X.iY z) (X.w0 (X.iY z))))) ∧
  (∀ z F g, X.nrmM (X.trY z F) g = ‖X.cst z‖ * ‖X.chr z g‖ * X.nrmM F (g + X.per z)) ∧
  (∀ g, X.nrmM X.be g ≤ 1) ∧
  (∀ g, ∀ ε : ℝ, 0 < ε → ∃ S0 : Finset X.Y, ∀ S : Finset X.Y, S0 ⊆ S →
    X.nrmM (X.up X.s - ∑ z ∈ S, X.trY z X.be) g ≤ ε) ∧
  (∀ F g, X.nrm 1 F (X.unif g) = X.nrmM (X.up F) g * (l : ℝ) ^ (-(X.Bf (X.trop g) (X.trop g) / 2))) ∧
  (∀ t : X.Co → ℂ_[l], (∀ a, ‖t a‖ < 1) → ∃ g : X.Gt, X.trop g = 0 ∧ ∀ k (F : X.Sec k), ∃ v : ℂ_[l],
    HasSum (fun m : X.Co →₀ ℕ => MvPowerSeries.coeff m (X.ser k F) * m.prod fun a e => t a ^ e) v ∧
      X.nrm k F (X.unif g) = ‖v‖)

def Conn : Prop :=
  (∀ k, ∀ h ∈ X.HO, ∀ g ∈ X.IntG k, X.nab k h g ∈ X.IntG k) ∧
  (∀ k h h' g, X.nab k h (X.nab k h' g) - X.nab k h' (X.nab k h g) = ((k : ℂ_[l]) * X.curv h h') • g) ∧
  (∀ h ∈ X.HO, ∀ h' ∈ X.HO, ‖X.curv h h'‖ ≤ 1) ∧ (∀ n ∈ X.Fil, ∀ n' ∈ X.Fil, X.curv n n' = 0) ∧
  (∀ k, ∀ n ∈ X.Fil, ∀ F, X.nab k n (X.germ k F) = 0) ∧
  (∀ N : ℕ, N ≠ 0 → ∀ h g, X.nab (N ^ 2) h (X.pullG N g) = (N : ℂ_[l]) • X.pullG N (X.nab 1 h g))

def Indep (ord : List σ) (P : MvPolynomial σ ℂ_[l]) : Prop :=
  ∀ L ∈ X.EL, ∀ L' ∈ X.EL, ∀ g ∈ X.Bas, X.PN ord X.nabD L P g = X.PN ord (X.nab 1) L' P g

def Eig (vd : ℝ) : Prop :=
  ∃ L ∈ X.EL, ∃ U : σ → X.H, (∀ u, U u ∈ X.HO) ∧ ∀ u, L u - U u ∈ X.Fil ∧
    ∀ d : ℂ_[l], ‖d‖ ≤ (l : ℝ) ^ (-vd) → d • (L u - U u) ∈ X.HO

def Good : Prop := ∀ z : X.Y, z = 0

end PtGeo

variable (D : Formalism.BasicNotions.D7)

def Per {L V : Type} [AddCommGroup L] (n : ℕ) (φ : L → V) : Prop :=
  ∀ x z : L, φ (x + (n : ℤ) • z) = φ x

def PerI {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]
    (I : Ideal (𝓞 E)) (φ : L → V) : Prop :=
  ∀ x : L, ∀ y ∈ I • (⊤ : Submodule (𝓞 E) L), φ (x + y) = φ x

def ConjPl (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) → (x ∈ P.asIdeal ↔ y ∈ P'.asIdeal)

def VacOff {L V : Type} [AddCommGroup L] [Module (𝓞 D.host.E) L] (φ : L → V) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), ¬ IsSplitPl D.host w →
    ∃ I : Ideal (𝓞 D.host.E), IsCoprime I w.asIdeal ∧ PerI I φ

def SplitLev (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    IsSplitPl D.host w

open scoped Classical in

def vdd (l : ℕ) : ℝ :=
  ⨆ v : placesOver D.host.E l,
    ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 D.host.E))).count
        (v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal : ℝ) /
      ((v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal.ramificationIdx ℤ : ℝ)

variable {D}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

def iO (i : D.ntw.Tw) : D.ntw.O i →+* ℂ_[D.ntw.l i] :=
  (D.nth.iC i).comp (algebraMap (D.ntw.O i) (KK i))

def c1 (i : D.ntw.Tw) {σ : Type} (P : MvPolynomial σ (D.ntw.O i)) : ℝ :=
  vdd D (D.ntw.l i) * (P.totalDegree : ℝ) / 2

def cB (i : D.ntw.Tw) {σ : Type} (P : MvPolynomial σ (D.ntw.O i)) (ck : ℝ) : ℝ :=
  ck + c1 i P + (D.nth.aL i : ℝ) * P.totalDegree + 2 * (D.nth.aL i : ℝ) * D.R.f * D.R.r * D.R.nV

def dat (i : D.ntw.Tw) (j : ℕ) (φl φn : D.nth.Lt i j → D.ntw.O i) : D.nth.Lt i j → KK i :=
  fun x => algebraMap (D.ntw.O i) (KK i) (φl x * φn x)

def Ball (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {f | ∀ y, ‖D.nth.ev i j b f y‖ ≤ 1}

def GalF (i : D.ntw.Tw) (F : Subfield (KK i)) : Set (RingAut ℂ_[D.ntw.l i]) :=
  {s | (∀ x, ‖s x‖ = ‖x‖) ∧ ∀ x ∈ F, s (D.nth.iC i x) = D.nth.iC i x}

def QSet (i : D.ntw.Tw) (M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  (∀ P ∈ Q, IsSplitPl D.host P ∧ Ideal.absNorm P.asIdeal % (2 * D.ntw.l i ^ M) = 1) ∧
  (∀ P ∈ Q, P ∉ D.ntw.S0 i) ∧ (∀ P ∈ Q, ∀ P', ConjPl D P P' → P' ∈ Q) ∧
  (∀ P ∈ Q, ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal))

def DelOK (i : D.ntw.Tw) (M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)) : Prop :=
  IsOpen (δ.ker : Set (G D.host.E D.nd.Om)) ∧ AntiHom D.ntw.cc δ ∧
  (∀ v, v ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, δ σ = 1) ∧
  (∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := D.host.E) A, δ σ = 1) ∧
  (∀ (q : ↥Q) (v : HeightOneSpectrum (𝓞 D.host.E)), v ≠ q.1 → ¬ ConjPl D q.1 v →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A,
      Multiplicative.toAdd (δ σ) q = 0)

def delY (i : D.ntw.Tw) (j : ℕ) {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)) (y : D.nth.Pt i j) :
    DelQM D.host (D.ntw.l i) Q M :=
  Multiplicative.toAdd (δ (D.nth.recDet i j y))

variable (D) in

structure Geo where

  pt : ∀ i j (_ : D.nth.Pt i j), PtGeo (D.ntw.l i) (D.nth.Lt i j) (D.nth.Let i j)

  ord : ∀ i j, List (D.nth.Let i j)
  ord_nodup : ∀ i j, (ord i j).Nodup
  ord_mem : ∀ i j u, u ∈ ord i j

  thV_def : ∀ i j (φ : D.nth.Lt i j → KK i) (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i))
    (y : D.nth.Pt i j) (n : ℕ), Odd n → Nat.Coprime n (D.ntw.l i) → SplitLev D n →
    Per (D.ntw.l i ^ D.nth.aL i * n) φ →
    D.nth.thV i j φ P y = (pt i j y).key * (pt i j y).PN (ord i j) (pt i j y).nabD (pt i j y).lf
      (P.map (iO i)) ((pt i j y).fG (D.ntw.l i ^ D.nth.aL i * n) (2 * D.R.f * D.R.r * D.R.nV)
        (fun x => D.nth.iC i (φ x)))

  det_actK : ∀ i j P P', ConjPl D P P' → ∀ (k : D.nth.Kq i j P) (y : D.nth.Pt i j) {A : Type} [CommGroup A]
    (χ : G D.host.E D.nd.Om →* A), IsOpen (χ.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc χ →
    (∀ v, v = P ∨ v = P' → ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B v →
      ∀ σ ∈ Ine (F := D.host.E) B, χ σ = 1) →
    χ (D.nth.recDet i j (D.nth.actK i j P k y)) = χ (D.nth.recDet i j y)

  Ks : ∀ i : D.ntw.Tw, Subfield (KK i)
  Ks_le : ∀ i, Ks i ≤ D.nth.MaximalUnramifiedExtension i
  Ks_E : ∀ i (τ : D.host.E →+* ℂ_[D.ntw.l i]) (x : D.host.E), ∃ z ∈ Ks i, D.nth.iC i z = τ x
  Ks_zeta : ∀ i k, D.ntw.l i = D.host.g k → ∃ z ∈ Ks i, IsPrimitiveRoot z (D.ntw.l i)

  actG : ∀ i j, RingAut ℂ_[D.ntw.l i] → D.nth.Pt i j → D.nth.Pt i j
  actG_one : ∀ i j y, actG i j 1 y = y
  actG_mul : ∀ i j, ∀ s ∈ GalF i (Ks i), ∀ t ∈ GalF i (Ks i), ∀ y,
    actG i j (s * t) y = actG i j s (actG i j t y)

  tB : ∀ i j s y, (pt i j y).BB →+ (pt i j (actG i j s y)).BB
  tB_bij : ∀ i j s y, Function.Bijective (tB i j s y)
  tH : ∀ i j s y, (pt i j y).H →+ (pt i j (actG i j s y)).H
  tH_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) h, tH i j s y (c • h) = s c • tH i j s y h
  tG : ∀ i j s y, (pt i j y).Gm 1 →+ (pt i j (actG i j s y)).Gm 1
  tG_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) g, tG i j s y (c • g) = s c • tG i j s y g

  FQ : ∀ i j, Bool → Finset (HeightOneSpectrum (𝓞 D.host.E)) → Submodule ℂ_[D.ntw.l i] (D.nth.Pt i j → ℂ_[D.ntw.l i])

  Fm_desc : ∀ i j b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) → ∀ F : D.nth.Pt i j → ℂ_[D.ntw.l i],
    (∃ f, D.nth.ev i j b f = F) ↔ F ∈ FQ i j b QP ∧ (∀ s ∈ GalF i ⊤, ∀ y, F (actG i j s y) = s (F y)) ∧
      ∀ P ∈ QP, ∀ (k : D.nth.Kq i j P) y, F (D.nth.actK i j P k y) = F y

  FmUr_def : ∀ i j b (f : D.nexp.Fm i j b), f ∈ D.nth.FmUr i j b ↔
    ∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, D.nth.ev i j b f (actG i j s y) = s (D.nth.ev i j b f y)

abbrev CKey (D : Formalism.BasicNotions.D7) : Type := D.ntw.Tw → ℕ → ℝ

def CoefficientBoundGeometric (X : Geo D) (ck : CKey D) : Prop :=
  ∀ (i : D.ntw.Tw) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ φl : D.nth.Lt i j → D.ntw.O i, Per (D.ntw.l i ^ D.nth.aL i) φl →
  ∀ P ∈ D.nth.Harm i j, ∀ n : ℕ, Odd n → Nat.Coprime n (D.ntw.l i) → SplitLev D n →
  ∀ φn : D.nth.Lt i j → D.ntw.O i, Per n φn → VacOff D φn → ∀ y : D.nth.Pt i j, (X.pt i j y).Good →
    ‖D.nth.thV i j (dat i j φl φn) P y‖ ≤ (D.ntw.l i : ℝ) ^ cB i P (ck i j)

variable (D) in

def ShaBoundTheoremB : Prop :=
  ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)),
    1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    ∀ f ∈ Ball i j b, f ∈ D.nth.FmUr i j b → D.nexp.hkF i j b k P f ∈ Ball i j b

variable (D) in

def IntegralitySecondClauseSupLattice : Prop :=
  ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)),
    1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    ∀ f ∈ D.nexp.Bsup i j b, D.nexp.hkF i j b k P f ∈ D.nexp.Bsup i j b

def PhiOK (i : D.ntw.Tw) (j : ℕ) (M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i) : Prop :=
  (∀ q a, ∀ P', ConjPl D q.1 P' → PerI (q.1.asIdeal * P'.asIdeal) (Φ q a)) ∧
  ∀ q a x, ∃ m : ℕ, ∃ z : ℤ,
    ((Ideal.absNorm q.1.asIdeal : ℕ) : KK i) ^ m * Φ q a x = (z : KK i)

def KqInv (i : D.ntw.Tw) (j : ℕ) {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i) : Prop :=
  ∀ P ∈ D.nth.Harm i j, ∀ q q' : ↥Q, ConjPl D q.1 q'.1 → ∀ ψ' : D.nth.Lt i j → KK i,
    (∃ n' : ℕ, Odd n' ∧ Nat.Coprime n' (D.ntw.l i) ∧ Per (D.ntw.l i ^ D.nth.aL i * n') ψ') →
    (∃ I : Ideal (𝓞 D.host.E), IsCoprime I (q.1.asIdeal * q'.1.asIdeal) ∧ PerI I ψ') →
    ∀ (b b' : ZMod (D.ntw.l i ^ M)) (k : D.nth.Kq i j q.1) (y : D.nth.Pt i j),
      D.nth.thV i j (fun x => ψ' x * (Φ q (b - delY i j δ (D.nth.actK i j q.1 k y) q) x *
          Φ q' (b' - delY i j δ (D.nth.actK i j q.1 k y) q') x)) P (D.nth.actK i j q.1 k y) =
        D.nth.thV i j (fun x => ψ' x * (Φ q (b - delY i j δ y q) x * Φ q' (b' - delY i j δ y q') x)) P y

def coef (i : D.ntw.Tw) (j : ℕ) {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i)
    (φl φn : D.nth.Lt i j → D.ntw.O i) (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i))
    (b : DelQM D.host (D.ntw.l i) Q M) (y : D.nth.Pt i j) : ℂ_[D.ntw.l i] :=
  D.nth.thV i j (fun x => dat i j φl φn x * ∏ q : ↥Q, Φ q ((b - delY i j δ y) q) x) P y

def HypC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (φl φn : D.nth.Lt i j → D.ntw.O i)
    (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (n M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i) : Prop :=
  Per (D.ntw.l i ^ D.nth.aL i) φl ∧ P ∈ D.nth.Harm i j ∧ Odd n ∧ Nat.Coprime n (D.ntw.l i) ∧ SplitLev D n ∧
  Per n φn ∧
  (∀ q ∈ Q, Nat.Coprime n (Ideal.absNorm q.asIdeal)) ∧
  (∃ d : D.nexp.Dat i j b, D.nth.datPhi i j b d = dat i j φl φn ∧ D.nth.datP i j b d = P) ∧
  QSet i M Q ∧ DelOK i M Q δ ∧ PhiOK i j M Q Φ ∧ KqInv i j δ Φ

def IntegralityThirdClause (ck : CKey D) : Prop :=
  ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m → ∀ (φl φn : D.nth.Lt i j → D.ntw.O i)
    (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (n M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i),
    HypC i j b φl φn P n M Q δ Φ → ∀ a : DelQM D.host (D.ntw.l i) Q M,
    ∃ f : D.nexp.Fm i j b, (∀ y, D.nth.ev i j b f y = coef i j δ Φ φl φn P a y) ∧
      ∀ y, ‖D.nth.ev i j b f y‖ ≤ (D.ntw.l i : ℝ) ^ cB i P (ck i j)

def IntegralityThirdClauseSupLattice (ck : CKey D) : Prop :=
  ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m → ∀ (φl φn : D.nth.Lt i j → D.ntw.O i)
    (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (n M : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i),
    HypC i j b φl φn P n M Q δ Φ → ∀ a : DelQM D.host (D.ntw.l i) Q M,
    ∃ z : KK i, ‖D.nth.iC i z‖ ≤ (D.ntw.l i : ℝ) ^ cB i P (ck i j) ∧
      ∃ g ∈ D.nexp.Bsup i j b, ∀ y, D.nth.ev i j b (z • g) y = coef i j δ Φ φl φn P a y

def ShaBoundAndIntegrality (ck : CKey D) : Prop := ShaBoundTheoremB D ∧ IntegralityThirdClause ck

def IntegralityConstantsSupLattice (ck : CKey D) : Prop := IntegralitySecondClauseSupLattice D ∧ IntegralityThirdClauseSupLattice ck

variable (D) in

def aux₃ : Prop := ∃ ck : CKey D, ShaBoundAndIntegrality ck

variable (D) in

def IntegralitySupLattice : Prop := ∃ ck : CKey D, IntegralityConstantsSupLattice ck

def ConjugationNormInvariance (X : Geo D) : Prop := ∃ ck : CKey D, CoefficientBoundGeometric X ck

variable (X : Geo D)

def adm1 : Prop := ∀ i j y, (X.pt i j y).Ray

def adm2 : Prop := ∀ i j y, (X.pt i j y).Conn

def adm3 : Prop :=
  ∀ i j b (d : D.nexp.Dat i j b) (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    D.nth.datP i j b d ∈ D.nth.Harm i j →
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal)) →
    ∀ Ψ : ↥QP → D.nth.Lt i j → KK i,
    (∀ (q : ↥QP) P', ConjPl D q.1 P' → PerI (q.1.asIdeal * P'.asIdeal) (Ψ q)) →
    (fun y => D.nth.thV i j (fun x => D.nth.datPhi i j b d x * ∏ q : ↥QP, Ψ q x) (D.nth.datP i j b d) y)
      ∈ X.FQ i j b QP

def ArchimedeanSignatureMatching : Prop :=
  ∀ i j y, ∀ P ∈ D.nth.Harm i j, (X.pt i j y).Indep (X.ord i j) (P.map (iO i))

def adm5 : Prop := ∀ i j y, (X.pt i j y).Eig (vdd D (D.ntw.l i))

def HeckeCorrespondenceReflex : Prop :=
  ∀ i j b k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∀ s ∈ GalF i (X.Ks i), ∀ c y,
    D.nth.hkMove i j k P c (X.actG i j s y) = X.actG i j s (D.nth.hkMove i j k P c y) ∧
    D.nth.hkU i j b k P c (X.actG i j s y) = s (D.nth.hkU i j b k P c y)

def TorsionSectionsReflex : Prop :=
  ∀ i j, ∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y,
    (∀ g, (X.pt i j (X.actG i j s y)).ev0 1 (X.tG i j s y g) = s ((X.pt i j y).ev0 1 g)) ∧
    (∀ h g, (X.pt i j (X.actG i j s y)).nabD (X.tH i j s y h) (X.tG i j s y g) =
      X.tG i j s y ((X.pt i j y).nabD h g)) ∧
    (∀ L ∈ (X.pt i j y).EL, (fun u => X.tH i j s y (L u)) ∈ (X.pt i j (X.actG i j s y)).EL) ∧
    ∀ n : ℕ, Odd n → Nat.Coprime n (D.ntw.l i) → ∀ x z, (D.ntw.l i ^ D.nth.aL i * n) • z = 0 →
      (X.pt i j (X.actG i j s y)).kr (D.ntw.l i ^ D.nth.aL i * n) x (X.tB i j s y z) •
          (X.pt i j (X.actG i j s y)).Uz (D.ntw.l i ^ D.nth.aL i * n) (X.tB i j s y z) =
        X.tG i j s y ((X.pt i j y).kr (D.ntw.l i ^ D.nth.aL i * n) x z •
          (X.pt i j y).Uz (D.ntw.l i ^ D.nth.aL i * n) z)

def LogLambdaEstimatesOnComponents : Prop :=
  ∀ i j, ∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, ∀ (A : Type) [CommGroup A] (χ : G D.host.E D.nd.Om →* A),
    IsOpen (χ.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc χ →
    (∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B v →
      ∀ σ ∈ Ine (F := D.host.E) B, χ σ = 1) →
    χ (D.nth.recDet i j (X.actG i j s y)) = χ (D.nth.recDet i j y)

open scoped Classical in

def GeometricComponentsDet : Prop :=
  ∀ i j b M (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)),
    QSet i M Q → DelOK i M Q δ → ∀ F ∈ X.FQ i j b Q, ∀ a,
    (fun y => if delY i j δ y = a then F y else 0) ∈ X.FQ i j b Q

def adm6 : Prop := HeckeCorrespondenceReflex X ∧ TorsionSectionsReflex X ∧ LogLambdaEstimatesOnComponents X ∧ GeometricComponentsDet X

def KeyValueNormBounded : Prop := ∀ i j, ∃ C : ℝ, ∀ y, ‖(X.pt i j y).key‖ ≤ (D.ntw.l i : ℝ) ^ C

def TraceMapNormalisation : Prop :=
  ∀ i j, ∃ (n : ℕ) (cp : D.nth.Pt i j → Fin n) (u : Fin n → (D.ntw.O i)ˣ) (tr : D.nth.Pt i j → ℂ_[D.ntw.l i]),
    (∀ y, (X.pt i j y).key = iO i (u (cp y) : D.ntw.O i) * tr y) ∧
    (∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, tr (X.actG i j s y) = s (tr y) ∧ cp (X.actG i j s y) = cp y) ∧
    (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∀ (k : D.nth.Kq i j P) y, cp (D.nth.actK i j P k y) = cp y) ∧
    ∀ b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) →
      ∀ F ∈ X.FQ i j b QP, ∀ c, (fun y => if cp y = c then F y else 0) ∈ X.FQ i j b QP

def HeckeFactorNormOne (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ i j b k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    ∀ c y, ‖D.nth.hkU i j b k P c y‖ = 1

def DataSplittingUnramified (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ i j b (d : D.nexp.Dat i j b), ∃ (n : ℕ) (e : Fin n → D.ntw.O i) (d' : Fin n → D.nexp.Dat i j b),
    (∀ t x, D.nth.datPhi i j b (d' t) x ∈ D.nth.MaximalUnramifiedExtension i) ∧
    (∀ t m, algebraMap (D.ntw.O i) (KK i) ((D.nth.datP i j b (d' t)).coeff m) ∈ D.nth.MaximalUnramifiedExtension i) ∧
    (∀ x m, D.nth.datPhi i j b d x * algebraMap (D.ntw.O i) (KK i) ((D.nth.datP i j b d).coeff m) =
      ∑ t, algebraMap (D.ntw.O i) (KK i) (e t) *
        (D.nth.datPhi i j b (d' t) x * algebraMap (D.ntw.O i) (KK i) ((D.nth.datP i j b (d' t)).coeff m))) ∧
    (∀ t, (D.nth.datP i j b (d' t)).totalDegree ≤ (D.nth.datP i j b d).totalDegree) ∧
    (D.nth.datP i j b d ∈ D.nth.Harm i j → ∀ t, D.nth.datP i j b (d' t) ∈ D.nth.Harm i j) ∧
    (∀ N : ℕ, Per N (D.nth.datPhi i j b d) → ∀ t, Per N (D.nth.datPhi i j b (d' t))) ∧
    ((∀ x, D.nth.datPhi i j b d x ∈ (algebraMap (D.ntw.O i) (KK i)).range) →
      ∀ t x, D.nth.datPhi i j b (d' t) x ∈ (algebraMap (D.ntw.O i) (KK i)).range)

def admitted : Prop := adm1 X ∧ adm2 X ∧ adm3 X ∧ ArchimedeanSignatureMatching X ∧ adm5 X ∧ adm6 X ∧ KeyValueNormBounded X ∧ TraceMapNormalisation X ∧ HeckeFactorNormOne D

def AdmittedSupLattice : Prop := admitted X ∧ DataSplittingUnramified D

def Stmt : Prop := admitted X → aux₃ D

def IntegralityTheoremSupLattice : Prop := AdmittedSupLattice X → IntegralitySupLattice D

def IntegralityGoodReduction : Prop := admitted X → ConjugationNormInvariance X

end Formalism.MainNotions.ExistsIdealDenominator
