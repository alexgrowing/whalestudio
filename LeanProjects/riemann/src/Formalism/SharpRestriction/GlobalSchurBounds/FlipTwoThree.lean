import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataForms

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def lamCol (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k then hcToWeightQ (D.hcW u τ).u ⟨i, h⟩ else 0

def wJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : ℚ :=
  if h : j < D.R.m then wG D.R ((D.hcW u τ).e ⟨j, h⟩) (j + 1) else 0

def lamLiftN (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if i < D.R.k then lamCol D u τ i else - wJ D u τ ((i - D.R.k) / (D.R.t + 1))

def lamLift (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : Fin (D.R.N j) → ℚ := fun i => lamLiftN D u τ i

def nuLift (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : Fin (D.R.N j) → ℚ :=
  fun i => lamLiftN D u τ i + wJ D u τ j

def absQ {N : ℕ} (v : Fin N → ℚ) : ℚ := ∑ i, v i

def hook {N : ℕ} (nu : Fin N → ℚ) : ℝ :=
  (∏ i : Fin N, (((⌊nu i⌋.toNat + N - 1 - i : ℕ).factorial : ℕ) : ℝ)) /
    ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      (((⌊nu i⌋ - ⌊nu j⌋ + (j : ℤ) - (i : ℤ) : ℤ)) : ℝ)

def dimV {N : ℕ} (lam : Fin N → ℤ) : ℝ :=
  ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℤ) - (i : ℤ) : ℤ) : ℝ))

def plc (D : D7) (τ : D.what₂.Tau) : D.R.GG := ((D.eTau τ : D.R.Psi) : _)

def IsTop (D : D7) (τ : D.what₂.Tau) : Prop := plc D τ ∈ D.host.topPlaces

def IsThick (D : D7) (τ : D.what₂.Tau) : Prop := plc D τ ∈ D.host.thickPlaces

def Nums (D : D7) (T g1 g2 : ℕ) (Cn x b L b' Sc eta : ℝ) : Prop :=
  0 < b ∧ Real.log (x * b * D.host.v) ≤ L ∧
  Real.log T ≤ Cn * D.R.m * L ∧ Real.log g1 ≤ Cn * L ∧ Real.log g2 ≤ Cn * L ∧
  b' ≤ x * b / x ∧ 1 ≤ Sc ∧ 1 ≤ eta ∧ Sc + eta + D.R.m * D.R.t ≤ b' / x ∧
  (D.R.N D.R.m : ℝ) ^ 2 * (L + Real.log T) ≤ D.R.N D.R.m * b' ∧
  (D.R.N D.R.m : ℝ) * L + Real.log T ≤ b' ∧
  (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * (L + Real.log T + Real.log ((g1 : ℝ) * g2)) ≤ D.R.N D.R.m * b' * L ∧
  |dlogL D 1| ≤ Cn * L ∧ 2 ≤ x ∧ 1 ≤ D.host.v ∧
  (1 + 2 * (2 * Cn + 4)) * (D.R.m : ℝ) ^ 3 * D.R.N D.R.m ≤ b'

def Wts (D : D7) (u : D.what₂.Word) (Cn x b b' Sc eta : ℝ) : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ i < D.R.k, ∃ z : ℤ, lamCol D u τ i = z) ∧
    (IsTop D τ → x * b ≤ (lamCol D u τ 0 : ℝ) ∧ (lamCol D u τ 0 : ℝ) ≤ 2 * (x * b) ∧
      b' ≤ -(lamCol D u τ (D.R.k - 1) : ℝ) ∧ -(lamCol D u τ (D.R.k - 1) : ℝ) < 2 * b' ∧
      ∀ i, 0 < i → i < D.R.k - 1 → 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ Sc) ∧
    (¬ IsTop D τ → ∀ i < D.R.k, 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ Cn * Sc) ∧
    (∀ j, j + 1 < D.R.m → wJ D u τ j ≤ wJ D u τ (j + 1)) ∧
    (¬ IsThick D τ → ∀ j < D.R.m, (wJ D u τ j : ℝ) ≤ 2 * b') ∧
    (IsThick D τ → ∀ j < D.R.m, b - D.R.N D.R.m ≤ (wJ D u τ j : ℝ) ∧ (wJ D u τ j : ℝ) ≤ b + eta + 1) ∧
    - lamCol D u τ (D.R.k - 1) ≤ wJ D u τ 0 ∧
    ((wJ D u τ (D.R.m - 1) - wJ D u τ 0 : ℚ) : ℝ) ≤ eta

def Tu (D : D7) (u : D.what₂.Word) : ℕ := (D.mem u).A.T

def dualSub {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    AddSubgroup S.V where
  carrier := {x | ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range}
  zero_mem' := fun y _ => by rw [map_zero]; exact zero_mem _
  add_mem' := fun {a b} ha hb y hy => by rw [map_add]; exact add_mem (ha y hy) (hb y hy)
  neg_mem' := fun {a} ha y hy => by rw [map_neg]; exact neg_mem (ha y hy)

def LatT {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) : Prop :=
  (∀ x ∈ L, x ∈ dualSub S L) ∧ L.toAddSubgroup.relIndex (dualSub S L) = q

def SameCls {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (M : ℕ) {n : ℕ}
    (L L' : Submodule (𝓞 E) S.V) (e e' : Fin n → S.V) : Prop :=
  ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ (∀ x, x ∈ L ↔ γ x ∈ L') ∧
    ∀ a, ∃ z ∈ dualSub S L', γ (e a) - e' a = (M : E) • z

def ClsTie (D : D7) (u : D.what₂.Word) : Prop :=
  (∀ i ≤ D.R.m, (∀ c, LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.clsLat u i c)) ∧
    ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
      (∀ c a, e c a ∈ dualSub (D.sp.X i) (D.clsLat u i c)) ∧
      ∀ c c', SameCls (D.sp.X i) (Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c) (D.clsLat u i c')
        (e c) (e c') → c = c') ∧
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ dualSub D.sp.X' (LP c)) ∧
      ∀ c c', SameCls D.sp.X' (Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') → c = c'

def Conclusion1 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → ClsTie D u →
    (∀ i ≤ D.R.m, Real.log (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤
      C * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 *
        (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) ∧
    Real.log (Fintype.card (D.fm u).clsP : ℝ) ≤
      C * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 *
        (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))

def Interlace {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lt.w i.succ ≤ sg.w i ∧ sg.w i ≤ lt.w i.castSucc

def degP {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i, lt.w i - ∑ i, sg.w i

def baseWeightDifference {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i : Fin n, (sg.w i - lt.w i.succ)

def lenP {n : ℕ} (lt : DomWeight (n + 1)) (i : Fin n) : ℤ := lt.w i.castSucc - lt.w i.succ

def blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).reindex finSumFinEquiv finSumFinEquiv

def scaleMat (n : ℕ) (T : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal fun i => if i = Fin.last n then ((Real.sqrt T : ℝ) : ℂ) else 1

def normTil {n : ℕ} (lt : DomWeight (n + 1)) (G : GL (Fin (n + 1)) ℂ)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) : ℝ :=
  (normFock lt (sqAct ℂ (n + 1) lt G f) (sqAct ℂ (n + 1) lt G f)).re

def PointsLemma (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (n : ℕ), n + 1 = D.R.N D.R.m →
    ∀ (lt : DomWeight (n + 1)), (∀ i : Fin (n + 1), (lt.w i : ℚ) = lamLiftN D u τ i) →
    ∀ (sg : DomWeight n), Interlace lt sg →
    ∀ (G : GL (Fin (n + 1)) ℂ), (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n (Tu D u) →
    ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ f ∈ delSq ℂ (n + 1) lt, P f ∈ delSq ℂ n sg) ∧
      (∃ f ∈ delSq ℂ (n + 1) lt, P f ≠ 0) ∧
      (∀ f ∈ delSq ℤ (n + 1) lt, ∃ g ∈ delSq ℤ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
      (∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
        (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
        ∀ f ∈ delSq ℂ (n + 1) lt, P (sqAct ℂ (n + 1) lt H f) = sqAct ℂ n sg g (P f)) ∧
      (∀ f ∈ delSq ℂ (n + 1) lt,
        (normFock sg (P f) (P f)).re ≤
          Real.exp (-(degP lt sg : ℝ) * Real.log (Tu D u) +
            2 * n * Real.log (lt.spread : ℝ) * (∑ i : Fin n, (min (lenP lt i) (baseWeightDifference lt sg) : ℝ)) +
            Real.log (dimV lt.w)) * normTil lt G f)

def adm3 (D : D7) : Prop := ∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0), Subsingleton ((D.mem u).C.stab 0 c)

def opSq (D : D7) (A B : HLat D.what₂.LL) (s : D.what₂.LL →+* ℂ) (φ : A.V →ₗ[D.what₂.LL] B.V) : ℝ :=
  Formalism.HN.opNormAt A.b A.X B.b B.X (NumberField.InfinitePlace.mk s) φ ^ 2

def opSqPl (D : D7) (A B : HLat D.what₂.LL) (v : NumberField.InfinitePlace D.what₂.LL)
    (φ : A.V →ₗ[D.what₂.LL] B.V) : ℝ :=
  Formalism.HN.opNormAt A.b A.X B.b B.X v φ ^ 2

def thetaLocalFactorAtIndex (D : D7) (_u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  D.gx.thOne s ^ (D.R.f * D.R.N i * D.R.N (i + 1))

def chainL (D : D7) (u : D.what₂.Word) (h : ∀ i, i < D.R.m → (D.fm u).KRat i) :
    (j : ℕ) → j ≤ D.R.m → (((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat j).V)
  | 0, _ => LinearMap.id
  | j + 1, hj => ((D.fm u).KL j (h j hj)).comp (chainL D u h j (Nat.le_of_succ_le hj))

def logOm (D : D7) (τ : D.what₂.Tau) : ℝ := D.gx.logOmMean τ

def aT (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ := (lamCol D u τ 0 : ℝ)

def bT (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ := -(lamCol D u τ (D.R.k - 1) : ℝ)

def tops (D : D7) : Finset D.what₂.Tau := topsOf D.host D.eTau

def LOW (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ := by
  classical
  exact ∑ τ ∈ Finset.univ.filter (fun τ => IsThick D τ),
    (Real.log (hook (nuLift D u τ j)) - (absQ (nuLift D u τ j) : ℝ) * logOm D τ)

def adm1 (D : D7) (Cn C x : ℝ) : Prop :=
  (∀ τ τ' : D.what₂.Tau, logOm D τ = logOm D τ') ∧
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta →
    ∀ τ, |logOm D τ| ≤ C * L

def adm2 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta →
    ∀ i < D.R.m,
      (∀ (s : D.what₂.LL →+* ℂ) (L₁ : (D.mem u).C.cls i) (L₁' : (D.mem u).C.cls (i + 1)),
        (D.fm u).thFree i s L₁ L₁' = thetaLocalFactorAtIndex D u i s) ∧
      (∑ s : D.what₂.LL →+* ℂ, Real.log (thetaLocalFactorAtIndex D u i s ^ 2)) /
          (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) ≤
        C * D.R.f * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * L

def ArchimedeanSignatureMatching (D : D7) : Prop := ∀ u, Function.Injective (D.fm u).til

def adm7 (D : D7) : Prop := ∀ u, ∀ i < D.R.m, (D.fm u).KRat i

abbrev Gx (D : D7) (i : ℕ) : Type := D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N (i + 1))

def Hherm (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z w : Gx D i → ℂ) : ℂ :=
  ∑ g, z g * star (w g) / ((Real.pi * D.gx.Om g.1 s : ℝ) : ℂ)

def Hq (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z : Gx D i → ℂ) : ℝ :=
  ∑ g, ‖z g‖ ^ 2 / (Real.pi * D.gx.Om g.1 s)

def dz (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : MeasureTheory.Measure (Gx D i → ℂ) :=
  ENNReal.ofReal (∏ g : Gx D i, (Real.pi * D.gx.Om g.1 s)⁻¹) • MeasureTheory.volume

def dens (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) (z : Gx D i → ℂ) : ℝ :=
  ‖Th z‖ ^ 2 * Real.exp (-Real.pi * Hq D i s z)

def trans (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (x : Gx D i → ℂ) (Th : (Gx D i → ℂ) → ℂ) :
    (Gx D i → ℂ) → ℂ :=
  fun z => Th (z - x) * Complex.exp (Real.pi * Hherm D i s z x - ((Real.pi * Hq D i s x / 2 : ℝ) : ℂ))

structure Torus (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) where
  La : AddSubgroup (Gx D i → ℂ)
  F : Set (Gx D i → ℂ)
  fund : MeasureTheory.IsAddFundamentalDomain La F (dz D i s)
  covol : dz D i s F = 1
  Hmin : ∀ y ∈ La, y ≠ 0 → ∃ β : D.host.E, β ≠ 0 ∧
    (∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (β * (a : D.host.E)) = (n : ℚ)) ∧
    Hq D i s y = 2 * ∑ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖

def Torus.Admis {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) : Prop :=
  Differentiable ℂ Th ∧ (∀ y ∈ T.La, ∀ z, dens D i s Th (z + y) = dens D i s Th z) ∧
  MeasureTheory.IntegrableOn (dens D i s Th) T.F (dz D i s)

def Torus.l2Sq {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) : ℝ :=
  ∫ z in T.F, dens D i s Th z ∂(dz D i s)

def ThetaSupremumBound (D : D7) : Prop :=
  ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ), T.Admis Th → ∀ z,
    dens D i s Th z ≤ (4 : ℝ) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      T.l2Sq Th

def jet {σ : Type} (cf : (σ →₀ ℕ) → ℂ) (Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ e ∈ Q.support, Q.coeff e * (e.prod fun _ n => (n.factorial : ℂ)) * cf e

def fockSq {σ : Type} (Q : MvPolynomial σ ℂ) : ℝ :=
  ∑ e ∈ Q.support, ‖Q.coeff e‖ ^ 2 * (e.prod fun _ n => (n.factorial : ℝ))

structure KerData (D : D7) (u : D.what₂.Word) where

  embS : ∀ i (s : D.what₂.LL →+* ℂ), ((D.fm u).lat i).V →ₛₗ[s] ((D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)

  ipS : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i →
    (((D.mem u).C.Y i → ℂ) →ₗ⋆[ℂ] ((D.mem u).C.Y i → ℂ) →ₗ[ℂ] ℂ)
  tor : ∀ i (s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → Torus D i s

  Th : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i → ℂ) → ℂ

  cf : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i →₀ ℕ) → ℂ
  cf_sum : ∀ i < D.R.m, ∀ s L L' z, HasSum (fun e => cf i s L L' e * e.prod fun g n => z g ^ n) (Th i s L L' z)

  e0 : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i → ℂ) → ℂ
  initial_theta_admissible : ∀ i < D.R.m, ∀ s L L', (tor i s L L').Admis (e0 i s L L')

  levelZeroComparison_norm : ∀ i < D.R.m, ∀ s L L', (D.fm u).thFree i s L L' ^ 2 = (tor i s L L').l2Sq (e0 i s L L')

  Q : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) →
    ((D.fm u).lat i).V → ((D.fm u).lat (i + 1)).V → MvPolynomial (Gx D i) ℂ

namespace KerData

variable {D : D7} {u : D.what₂.Word} (X : KerData D u)

def nrm (i : ℕ) (s : D.what₂.LL →+* ℂ) (c : (D.mem u).C.cls i) (x : ((D.fm u).lat i).V) : ℝ :=
  (X.ipS i s c (X.embS i s x c) (X.embS i s x c)).re

def ConjMetric : Prop :=
  (∀ i ≤ D.R.m, X.embS i D.what₂.embLL = (D.fm u).emb i ∧ X.ipS i D.what₂.embLL = (D.fm u).ipV i) ∧
  (∀ i ≤ D.R.m, ∀ s c x, 0 ≤ X.nrm i s c x) ∧
  ∀ i ≤ D.R.m, ∀ s x, (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
    ∑ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ * X.nrm i s c x

def KerAt (s : D.what₂.LL →+* ℂ) : Prop :=
  ∀ i < D.R.m, ∀ (h : (D.fm u).KRat i) (x : ((D.fm u).lat i).V) (y : ((D.fm u).lat (i + 1)).V),
    (∀ L', X.ipS (i + 1) s L' (X.embS (i + 1) s y L') (X.embS (i + 1) s ((D.fm u).KL i h x) L') =
      ∑ L, ((Nat.card ((D.mem u).C.stab i L) : ℂ))⁻¹ * jet (X.cf i s L L') (X.Q i s L L' x y)) ∧
    ∀ L L', (∀ e ∈ (X.Q i s L L' x y).support, ∀ τ,
        ((∑ ac : Fin (D.R.N i) × Fin (D.R.N (i + 1)), e (τ, ac) : ℕ) : ℚ) = absQ (nuLift D u τ i)) ∧
      fockSq (X.Q i s L L' x y) ≤ (∏ τ, hook (nuLift D u τ i)) * X.nrm i s L x * X.nrm (i + 1) s L' y

def KerTie : Prop := X.KerAt D.what₂.embLL

end KerData

def AdmittedGaloisConjugateKernels {D : D7} {u : D.what₂.Word} (X : KerData D u) : Prop := ∀ s, X.KerAt s

def adm5 {D : D7} {u : D.what₂.Word} (X : KerData D u) (C : ℝ) : Prop :=
  ∀ i < D.R.m, ∀ s L L', ∃ (κ : ℂ) (n : ℕ) (c : Fin n → ℂ) (x : Fin n → Gx D i → ℂ),
    (∀ z, X.Th i s L L' z = κ * ∑ k, c k * trans D i s (x k) (X.e0 i s L L') z) ∧
    ‖κ‖ ^ 2 * (∑ k, ‖c k‖) ^ 2 ≤ Real.exp (C * D.R.f *
      ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
      (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)))

def Conclusion2 (D : D7) (Cn Cd C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ClsTie D u → ∀ X : KerData D u, X.ConjMetric → AdmittedGaloisConjugateKernels X → adm5 X Cd →
    ∀ i < D.R.m, ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
      opSq D ((D.fm u).lat i) ((D.fm u).lat (i + 1)) s ((D.fm u).KL i hK) ≤
        Real.exp ((∑ τ, (Real.log (hook (nuLift D u τ i)) -
            (absQ (nuLift D u τ i) : ℝ) * Real.log (D.gx.Om τ s))) +
          Real.log (thetaLocalFactorAtIndex D u i s ^ 2) +
          C * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (i + 1) : ℝ) ^ 2 *
            (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)))

def HookLengthFactorialBound : Prop :=
  ∀ (N : ℕ) (nu : Fin N → ℚ), (∀ i, ∃ z : ℕ, nu i = z) → Antitone nu →
    hook nu ≤ ∏ i : Fin N, (((⌊nu i⌋.toNat + N - 1 - i : ℕ).factorial : ℕ) : ℝ) ∧
    ∀ h : 0 < N, (∑ i : Fin N, Real.log (((⌊nu i⌋.toNat + N - 1 - i : ℕ).factorial : ℕ) : ℝ)) -
      (N : ℝ) ^ 2 * Real.log ((nu ⟨0, h⟩ : ℝ) + N) ≤ Real.log (hook nu)

def baseWeightDifferenceAtTau (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℤ :=
  ∑ i : Fin (D.R.N D.R.m - 1), (((D.fm u).sg τ).w i - ((D.fm u).lam D.R.m τ).w ⟨i.1 + 1, by omega⟩)

def lenM (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin (D.R.N D.R.m - 1)) : ℤ :=
  ((D.fm u).lam D.R.m τ).w ⟨i.1, by omega⟩ - ((D.fm u).lam D.R.m τ).w ⟨i.1 + 1, by omega⟩

def SgHyp (D : D7) (u : D.what₂.Word) (Cn Sc eta : ℝ) : Prop :=
  (D.fm u).SgInterlace ∧ ∀ τ : D.what₂.Tau,
    (IsTop D τ → (baseWeightDifferenceAtTau D u τ : ℝ) ≤ bT D u τ + eta + Sc ∧
      |((D.fm u).deg τ : ℝ) - (aT D u τ - bT D u τ)| ≤ Cn * (Sc + eta + D.R.m * D.R.t)) ∧
    (¬ IsTop D τ → (baseWeightDifferenceAtTau D u τ : ℝ) ≤ eta + Sc ∧
      -(Sc + eta) - Cn * ((D.R.m : ℝ) * D.R.t) ≤ ((D.fm u).deg τ : ℝ)) ∧
    ∃ S : Finset (Fin (D.R.N D.R.m - 1)), S.card ≤ 3 ∧ ((∑ i ∈ Sᶜ, lenM D u τ i : ℤ) : ℝ) ≤ eta + Sc

def BeOnBd (D : D7) (u : D.what₂.Word) (Cn : ℝ) : Prop :=
  ∀ τ : D.what₂.Tau, (D.fm u).beOn τ ^ 2 ≤
    Real.exp (Cn * D.R.N D.R.m * Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) *
        (∑ i, ((min (lenM D u τ i) (baseWeightDifferenceAtTau D u τ) : ℤ) : ℝ)) +
      Real.log (dimV ((D.fm u).lam D.R.m τ).w))

def ptB (D : D7) (u : D.what₂.Word) : ℝ :=
  ∏ τ, (Tu D u : ℝ) ^ (-((D.fm u).deg τ)) * (D.fm u).beOn τ ^ 2

def adm6 (D : D7) : Prop :=
  ∀ u, ∃ h : (D.fm u).PRat, ∀ (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat D.R.m).V),
    (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
      ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re

def ProjectionOperatorEstimate (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    SgHyp D u Cn Sc eta → BeOnBd D u Cn →
    ∀ (hP : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ),
      opSq D ((D.fm u).lat D.R.m) (D.fm u).ptLat s ((D.fm u).PtL hP) ≤
        Real.exp (-(∑ t ∈ tops D, aT D u t * Real.log (Tu D u)) +
          C * D.host.TT.card * b' * (Real.log (Tu D u) + D.R.N D.R.m * L) +
          C * D.R.f * (eta + 3 * Sc + D.R.m * D.R.t) * (Real.log (Tu D u) + D.R.N D.R.m * L) +
          C * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * L)

def Conclusion4 (D : D7) (Cn Cd C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    SgHyp D u Cn Sc eta → BeOnBd D u Cn →
    ClsTie D u → ∀ X : KerData D u, X.ConjMetric → AdmittedGaloisConjugateKernels X → adm5 X Cd →
    ∀ (hK : ∀ i, i < D.R.m → (D.fm u).KRat i) (hP : (D.fm u).PRat),
      (∏ v : NumberField.InfinitePlace D.what₂.LL,
          opSqPl D ((D.fm u).lat 0) (D.fm u).ptLat v
            (((D.fm u).PtL hP).comp (chainL D u hK D.R.m le_rfl))) ≤
        Real.exp ((Formalism.HN.nPl D.what₂.LL : ℝ) *
          ((∑ _j ∈ Finset.range D.R.m, ∑ t ∈ tops D,
              (aT D u t * Real.log (aT D u t) - aT D u t - aT D u t * logOm D t)) -
            (∑ t ∈ tops D, aT D u t * Real.log (Tu D u)) +
            (∑ j ∈ Finset.range D.R.m, LOW D u j) +
            C * D.R.f * D.R.m * D.R.N D.R.m * b' * L))

section Tensor

variable {ι : Type} [Fintype ι]

def ten {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def TSpan (K : Type) [Field K] {n : ℕ} (lam : ι → DomWeight n) :
    Submodule K (MvPolynomial (ι × Fin n × Fin n) K) :=
  Submodule.span K {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ delSq K n (lam τ)) ∧ p = ten f}

def actAll {K : Type} [Field K] {n : ℕ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) : MvPolynomial (ι × Fin n × Fin n) K :=
  (∏ τ, (g τ).det ^ (lam τ).detShift) •
    MvPolynomial.aeval (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2)) p

def nfAll {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

end Tensor

def IntSpanAt (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW D.what₂.places w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = r • ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ))}

def LocBasis (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) : Prop :=
  IsUnit γ.det ∧ locW D.what₂.places w Q.L =
    Submodule.span (intW D.what₂.places w) (Set.range fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i))

structure ColVal (D : D7) (u : D.what₂.Word) where

  ne : Nonempty ((D.mem u).C.cls 0)
  rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)
  Q : (D.mem u).C.cls 0 → D.what₂.Tau → HLat D.what₂.LL
  Q_good : ∀ c τ, (Q c τ).Good
  eQ : ∀ c τ, (Q c τ).ι ≃ Fin (D.R.N 0)

  bc : ∀ c τ, (D.sp.X 0).V →+ (Q c τ).V
  bc_smul : ∀ c τ (a : D.host.E) y, bc c τ (a • y) = rho τ a • bc c τ y

  bc_L : ∀ c τ, (Q c τ).L = Submodule.span (𝓞 D.what₂.LL) (bc c τ '' (D.clsLat u 0 c : Set (D.sp.X 0).V))

  bc_norm : ∀ c τ (v : InfinitePlace D.what₂.LL) y,
    (Formalism.HermitianLatticesTheory.majAt (Q c τ).b (Q c τ).X v (bc c τ y) (bc c τ y)).re =
      (v.embedding (rho τ ((D.sp.X 0).hT y y))).re

  latT : ∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)

  co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
    ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
  co_inj : Function.Injective co

  co_range : ∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)

  fin : ∀ (w : D.what₂.places.Pl)
    (γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL),
    (∀ c τ, LocBasis D w (Q c τ) (eQ c τ) (γ c τ)) →
    ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
      ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)

  inf : ∀ (v : InfinitePlace D.what₂.LL) x,
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
      ∑ c, (nfAll ((D.fm u).lam 0)
        (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))
        (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))).re

def Conclusion5 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ColVal D u →
    -(∑ t ∈ tops D, aT D u t / D.R.k * Real.log (Tu D u)) - C * D.host.TT.card * (x * b) * Real.log D.R.k -
        C * D.R.f * D.R.k * (b' + Sc) * Real.log D.R.k - C * D.R.f * Sc * Real.log (Tu D u) -
        C * D.R.f * (D.R.k : ℝ) ^ 2 * L ≤ ((D.fm u).lat 0).mu

def Conclusion6 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ColVal D u →
    ((D.fm u).lat 0).muMax ≤ C * D.host.TT.card * (x * b) * Real.log (D.R.k * D.host.v) +
      C * D.R.f * (b' + Sc) * (D.R.k * Real.log (D.R.k * D.host.v) + Real.log (Tu D u)) +
      C * D.R.f * (D.R.k : ℝ) ^ 2 * L

def admitted (D : D7) (Cn Cper Cth x : ℝ) : Prop :=
  adm1 D Cn Cper x ∧ adm2 D Cn Cth x ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm6 D ∧ adm7 D

def Conclusion₂ (D : D7) (Cn Cd C1 C2 C4 C5 C6 x : ℝ) : Prop :=
  Conclusion1 D Cn C1 x ∧ Conclusion2 D Cn Cd C2 x ∧ PointsLemma D ∧ Conclusion4 D Cn Cd C4 x ∧ Conclusion5 D Cn C5 x ∧ Conclusion6 D Cn C6 x ∧
  ThetaSupremumBound D ∧ HookLengthFactorialBound

def Stmt (D : D7) (Cn Cd Cper Cth C1 C2 C4 C5 C6 x : ℝ) : Prop :=
  admitted D Cn Cper Cth x → Conclusion₂ D Cn Cd C1 C2 C4 C5 C6 x

def ConditionalProjectionOperatorEstimate (D : D7) (Cn C x : ℝ) : Prop := adm6 D → ProjectionOperatorEstimate D Cn C x

def famC {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (P : D7 → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cn : ℝ, ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P (Fm.D x i) Cn C x

def famD {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (P : D7 → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cn Cd : ℝ, ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P (Fm.D x i) Cn Cd C x

def fam0 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (P : D7 → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P (Fm.D x i)

def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm adm1
def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm adm2
def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm adm3
def admF4 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm ArchimedeanSignatureMatching
def admF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm adm6
def admF7 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm adm7
def ConclusionF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm Conclusion1
def ConclusionF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famD Fm Conclusion2

def ConclusionF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), PointsLemma (Fm.D x i)
def FamilyEstimateFour {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famD Fm Conclusion4
def ConclusionF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm Conclusion5
def ConclusionF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm Conclusion6
def FamilySupremumBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), ThetaSupremumBound (Fm.D x i)
def FamilyProjectionEstimate {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm ProjectionOperatorEstimate

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm ∧ admF4 Fm ∧ admF6 Fm ∧ admF7 Fm
def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ConclusionF1 Fm ∧ ConclusionF2 Fm ∧ ConclusionF3 Fm ∧ FamilyEstimateFour Fm ∧ ConclusionF5 Fm ∧ ConclusionF6 Fm ∧ FamilySupremumBound Fm ∧ HookLengthFactorialBound

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ConclusionOnFamily Fm

def ShareFamilyAtConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF6 Fm → FamilyProjectionEstimate Fm

end Formalism.MainNotions.flipTwoThree
