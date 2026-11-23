import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OffCharsSeparates
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices (gramA gramInvA idemFin idemInf IsProbPair)
open GlobalTheory.BesselCompare (eMat)
open GlobalTheory.WeilTieCompare (kap kapT IsChange)
open scoped TensorProduct

namespace GlobalTheory.Per

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnitN (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (ν : Measure (NFlag B e))
    (𝓝 : Set (NFlag B e)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B e) 𝓝 ν ∧ ν 𝓝 = 1

section Bessel

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def besFun (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ)
    (h : GA D A) (n : NFlag B d.e) : ℂ :=
  star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) * star (besChar ψ d (n : GA D B))

def besPer (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure (NFlag B d.e)) (𝓝 : Set (NFlag B d.e)) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ d s φ F h n ∂ν ∂μ

def BesConv (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure (NFlag B d.e)) (𝓝 : Set (NFlag B d.e)) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : Prop :=
  (∀ h, IntegrableOn (besFun ψ d s φ F h) 𝓝 ν) ∧ IntegrableOn (fun h => ∫ n in 𝓝, besFun ψ d s φ F h n ∂ν) 𝓕 μ

end Bessel

structure IsNegLine (L : HSp D) : Prop where
  rank_one : L.rank = 1
  sigOK : L.SigOK
  neg : ∀ τ, L.sig τ = (0, 1)

def lineVec (L : HSp D) : L.V := ∑ i, L.frame i

def lineNorm (L : HSp D) : D.host.E := L.hD (lineVec L) (lineVec L)

def tPt (L A : HSp D) (c : D.host.E) (a : Fin A.rank → AE D) : WA L A := Matrix.of fun _ k => -(incA D c * a k)

def cenCo (L : HSp D) (c : D.host.E) (t : AE D) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) *
    Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * (c * star c) * lineNorm L) * t)

def jacOp (ψ : AddChar (AF D.host.F) ℂ) (L A : HSp D) (c : D.host.E) (a : Fin A.rank → AE D) (t : AE D)
    (f : WA L A → ℂ) : WA L A → ℂ :=
  fun w => ψ (cenCo L c t) * Heisenberg₂ ψ L A (tPt L A c a) f w

structure FJDat (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  line : IsNegLine L
  isom : HSpace.IsIsomEmb A B ι

  ρ : ℕ
  codim : A.rank + 2 * ρ = B.rank

  e : Fin ρ → B.V

  f : Fin ρ → B.V
  ee : ∀ i j, B.hD (e i) (e j) = 0
  ff : ∀ i j, B.hD (f i) (f j) = 0
  ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0
  eA : ∀ i x, B.hD (e i) (ι x) = 0
  fA : ∀ i x, B.hD (f i) (ι x) = 0

  β : Fin (ρ - 1) → D.host.E
  β_ne : ∀ i, β i ≠ 0

  c : D.host.E
  c_ne : c ≠ 0

namespace FJDat

variable {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : FJDat L A B ι)

abbrev eM : Matrix (Fin B.rank) (Fin d.ρ) D.host.E := eMat B d.e

abbrev N : Subgroup (GA D B) := NFlag B d.eM

def fTop : B.V := ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then d.f i else 0

def aCo (n : GA D B) : Fin A.rank → AE D :=
  (gramInvA A).mulVec fun i => hA B (actV B n d.fTop) (vecA B (ι (A.frame i)))

def tCo (n : GA D B) : AE D := hA B (actV B n d.fTop) (vecA B d.fTop)

def jac (ψ : AddChar (AF D.host.F) ℂ) (n : GA D B) (f : WA L A → ℂ) : WA L A → ℂ :=
  jacOp ψ L A d.c (d.aCo n) (d.tCo n) f

def chr (ψ : AddChar (AF D.host.F) ℂ) (n : GA D B) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin (d.ρ - 1), incA D (d.β i) *
    hA B (actV B n (d.e ⟨i.1 + 1, by have := i.2; omega⟩)) (vecA B (d.f ⟨i.1, by have := i.2; omega⟩))))

def theta (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (n : GA D B) (g : GA D A) : ℂ :=
  d.jac ψ n (Om g) 0

def perFun (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (s : GA D A → GA D B) (φ : GA D A → ℂ)
    (F : GA D B → ℂ) (g : GA D A) (n : d.N) : ℂ :=
  star (φ g) * F ((n : GA D B) * s g) * d.theta ψ Om n g * star (d.chr ψ n)

def per (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure d.N) (𝓝 : Set d.N) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : ℂ :=
  ∫ g in 𝓕, ∫ n in 𝓝, d.perFun ψ Om s φ F g n ∂ν ∂μ

def Conv (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure d.N) (𝓝 : Set d.N) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : Prop :=
  (∀ g, IntegrableOn (d.perFun ψ Om s φ F g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, d.perFun ψ Om s φ F g n ∂ν) 𝓕 μ

end FJDat

def coefH (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (m : Measure (WA V W) × Set (WA V W)) (f : WA V W → ℂ)
    (u : WA V W) : ℂ :=
  ∫ w in m.2, Heisenberg₂ ψ V W u f w * star (f w) ∂m.1

def IsPureAt (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ε : AE D) (f : WA V W → ℂ) : Prop :=
  AllSome (fun m : Measure (WA V W) × Set (WA V W) => IsProbPair V W m.1 m.2) fun m =>
    ∀ x y : WA V W, ε • x = x → ε • y = 0 →
      coefH ψ V W m f (x + y) * coefH ψ V W m f 0 = coefH ψ V W m f x * coefH ψ V W m f y

def IsVacAE (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WA V W → ℂ) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ u ∈ latVWS V W S, Heisenberg₂ ψ V W u f = f

structure IsFact (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WA V W → ℂ) : Prop where
  fin : ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsPureAt ψ V W (idemFin D v) f
  inf : ∀ v : InfinitePlace D.host.F, IsPureAt ψ V W (idemInf D v) f
  vac : IsVacAE ψ V W f

section Comparison₂

variable {X : ThetaX D} {T : ThetaTied D X}

def factSet (Wl : WeilTied D X T) (V W : HSp D) : Set (X.Sch V W) := {Φ | IsFact Wl.ψ V W (Wl.evS V W Φ)}

def omZ (Wl : WeilTied D X T) (L A : HSp D) (Φ : X.Sch L A) (g : GA D A) : WA L A → ℂ :=
  Wl.evS L A (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ)

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def IsBesPos (Wl : WeilTied D X T) (d : BesDat A B ι) (p : X.Pos A B ι) : Prop :=
  ∀ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ ν 𝓝, IsUnitN B d.e ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
    ∀ (σ : X.FJd A B ι) (φ : X.AF A) (F : X.cusp B), IsAniso A ∨ φ ∈ X.cusp A →
      X.Bper A B ι p σ φ F = (T.petC A : ℂ) * besPer Wl.ψ d μ 𝓕 ν 𝓝 s (T.ev A φ) (T.ev B (F : X.AF B))

def IsFJPos (Wl : WeilTied D X T) {L : HSp D} (k : X.FJd A B ι ≃ₗ[ℂ] X.Sch L A) (d : FJDat L A B ι)
    (p : X.Pos A B ι) : Prop :=
  ∀ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
    ∀ (σ : X.FJd A B ι) (φ : X.AF A) (F : X.cusp B), IsAniso A ∨ φ ∈ X.cusp A →
      X.Bper A B ι p σ φ F =
        (T.petC A : ℂ) * d.per Wl.ψ (omZ Wl L A (k σ)) μ 𝓕 ν 𝓝 s (T.ev A φ) (T.ev B (F : X.AF B))

def trCusp (X : ThetaX D) (B : HSp D) (y : X.Gf B) (F : X.cusp B) : X.cusp B := ⟨X.actF B y F, X.actF_cusp B y F F.2⟩

def IsTranslSum (X : ThetaX D) (p p₀ : X.Pos A B ι) : Prop :=
  ∀ (σ : X.FJd A B ι) (F : X.cusp B), ∃ (n : ℕ) (a : Fin n → ℂ) (σ' : Fin n → X.FJd A B ι) (y : Fin n → X.Gf B),
    ∀ φ, X.Bper A B ι p σ φ F = ∑ i, a i * X.Bper A B ι p₀ (σ' i) φ (trCusp X B (y i) F)

end Comparison₂

def FJInt (D : D7) : Prop :=
  ∀ (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι),
    1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 →
    ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F →
      d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F

def FactPure (D : D7) : Prop :=
  ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), IsThetaFun ψ V W f →
    (IsFact ψ V W f ↔ GlobalTheory.Mem.Th.IsPureFun ψ V W f)

structure FJTied {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) where

  line : HSp D
  line_neg : IsNegLine line

  eFJ : ∀ t j, j < D.R.m → Odd j → X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j) ≃ₗ[ℂ] X.Sch line (X.Xs t j)

  fj : ∀ t j (hj : j < D.R.m) (ho : Odd j) (d : FJDat line (X.Xs t j) (X.Ys t j) (X.iXYs t j)),
    ∃ p, IsFJPos Wl (eFJ t j hj ho) d p

  fj_only : ∀ t j (hj : j < D.R.m) (ho : Odd j) (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)),
    ∃ d : FJDat line (X.Xs t j) (X.Ys t j) (X.iXYs t j), IsFJPos Wl (eFJ t j hj ho) d p

structure PerTied {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) extends FJTied Wl where

  bes : ∀ t j, j < D.R.m → Even j → ∀ d : BesDat (X.Xs t j) (X.Ys t j) (X.iXYs t j),
    (d.y : GA D (X.Ys t j)) = 1 → ∃ p, IsBesPos Wl d p

  bes_all : ∀ t j, j < D.R.m → Even j → ∀ p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j),
    ∃ d : BesDat (X.Xs t j) (X.Ys t j) (X.iXYs t j), (d.y : GA D (X.Ys t j)) = 1 ∧
      ∃ p₀, IsBesPos Wl d p₀ ∧ IsTranslSum X p p₀

  fact : ∀ V W : HSp D, V.rank ≠ W.rank → X.fact V W = factSet Wl V W

theorem kap_symm_tPt (L A : HSp D) (c : D.host.E) (a : Fin A.rank → AE D) (i : Fin L.rank) (k : Fin A.rank) :
    (kap L A).symm (tPt L A c a) i k = incA D (-(c * L.hD (L.frame i) (lineVec L))) * a k := by
  have : L.hD (L.frame i) (lineVec L) = ∑ m, L.gram m i := by
    simp only [HSpace.hD, lineVec, map_sum, LinearMap.sum_apply, HSpace.gram]
  rw [this, WeilTieCompare.kap_symm_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gramA, Matrix.map_apply, tPt, Matrix.of_apply, map_neg, map_mul,
    map_sum, Finset.mul_sum, neg_mul, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by ring

theorem lineNorm_eq (L : HSp D) : lineNorm L = ∑ i, ∑ k, L.gram k i := by
  simp only [lineNorm, HSpace.hD, lineVec, map_sum, LinearMap.sum_apply, HSpace.gram]

theorem star_lineNorm (L : HSp D) : star (lineNorm L) = lineNorm L := L.herm.eq _ _

theorem tPt_add (L A : HSp D) (c : D.host.E) (a a' : Fin A.rank → AE D) :
    tPt L A c (a + a') = tPt L A c a + tPt L A c a' := by
  ext i k; simp only [tPt, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; ring

theorem tPt_zero (L A : HSp D) (c : D.host.E) : tPt L A c 0 = 0 := by
  ext i k; simp [tPt]

theorem hHom_tPt {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E) (a a' : Fin A.rank → AE D) :
    hHom L A (tPt L A c a') (tPt L A c a) = incA D (c * star c * lineNorm L) * hA A a a' := by
  unfold hHom
  rw [if_pos hr, lineNorm_eq]
  simp only [tPt, Matrix.of_apply, hA, map_neg, map_mul, map_sum, DualPairCheck.cA_incA, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm_cycle]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem cA_hA (A : HSp D) (a a' : Fin A.rank → AE D) : cA D (hA A a a') = hA A a' a := by
  simp only [hA, map_sum, map_mul, DualPairCheck.cA_cA, DualPairCheck.cA_incA, DualPairCheck.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cenCo_add (L : HSp D) (c : D.host.E) (t t' : AE D) : cenCo L c (t + t') = cenCo L c t + cenCo L c t' := by
  simp only [cenCo, mul_add, map_add]

theorem cenCo_zero (L : HSp D) (c : D.host.E) : cenCo L c 0 = 0 := by
  simp only [cenCo, mul_zero, map_zero]

theorem cenCo_conj (L : HSp D) (c : D.host.E) (t : AE D) : cenCo L c (cA D t) = -cenCo L c t := by
  have h1 : star (D.host.xi0 * (c * star c) * lineNorm L) = -(D.host.xi0 * (c * star c) * lineNorm L) := by
    rw [star_mul', star_mul', star_mul', star_star, star_lineNorm, DualPairCheck.star_purely_imaginary_eq_neg]; ring
  have h2 : incA D (D.host.xi0 * (c * star c) * lineNorm L) * cA D t =
      -cA D (incA D (D.host.xi0 * (c * star c) * lineNorm L) * t) := by
    rw [(cA D).map_mul, DualPairCheck.cA_incA, h1, (incA D).map_neg]; ring
  unfold cenCo
  rw [h2, LinearMap.map_neg, DualPairCheck.trace_cA, mul_neg]

theorem symplH_tPt {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E) (a a' : Fin A.rank → AE D) :
    symplH L A (tPt L A c a) (tPt L A c a') = cenCo L c (-hA A a' a) := by
  rw [← cA_hA, ← map_neg, cenCo_conj]
  unfold symplH sympl cenCo
  rw [hHom_tPt hr, mul_neg, map_neg, mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_assoc D.host.xi0]

theorem jacOp_mul (ψ : AddChar (AF D.host.F) ℂ) {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E)
    (a a' : Fin A.rank → AE D) (t t' : AE D) (f : WA L A → ℂ) :
    jacOp ψ L A c a t (jacOp ψ L A c a' t' f) = jacOp ψ L A c (a + a') (t + t' - hA A a' a) f := by
  funext w
  have h := congrFun (DualPairCheck.heis_heis ψ L A (tPt L A c a) (tPt L A c a') f) w
  rw [symplH_tPt hr] at h
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h
  simp only [jacOp, Heisenberg₂, sub_eq_add_neg, cenCo_add, AddChar.map_add_eq_mul, tPt_add]
  linear_combination ψ (cenCo L c t) * ψ (cenCo L c t') * h

theorem symplH_zero_left (V W : HSp D) (x : WA V W) : symplH V W 0 x = 0 := by
  have := DualPairCheck.symplH_add_left V W 0 0 x
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem heis_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WA V W → ℂ) : Heisenberg₂ ψ V W 0 f = f := by
  funext w
  have := DualPairCheck.symplH_add_right V W w 0 0
  rw [add_zero] at this
  simp only [Heisenberg₂, left_eq_add.mp this, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem jacOp_centre (ψ : AddChar (AF D.host.F) ℂ) (L A : HSp D) (c : D.host.E) (t : AE D) (f : WA L A → ℂ) :
    jacOp ψ L A c 0 t f = ψ (cenCo L c t) • f := by
  funext w
  simp only [jacOp, tPt_zero, heis_zero, Pi.smul_apply, smul_eq_mul]

theorem IsNegLine.lineNorm_neg {L : HSp D} (h : IsNegLine L) (τ : D.host.E →+* ℂ) : (τ (lineNorm L)).re < 0 := by
  have h1 := h.sigOK τ
  rw [h.neg τ] at h1
  have h2 := Formalism.UG.P.stdform_sig_neg _ h1 (fun _ => 1) (fun e => one_ne_zero (congrFun e ⟨0, by rw [h.rank_one]; omega⟩))
  rw [lineNorm_eq, Finset.sum_comm]
  simpa [Formalism.UG.P.stdformQ, Formalism.UG.hform] using h2

namespace FJDat

variable {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : FJDat L A B ι)

theorem isIsoSub : IsIsoSub B d.eM := by
  refine ⟨Fintype.linearIndependent_iff.2 fun g hg i => ?_, ?_⟩
  · have h0 : ∑ l, g l • d.e l = 0 := by
      apply B.frame.repr.injective
      refine Finsupp.ext fun k => ?_
      simpa [eMat] using congrFun hg k
    have h1 := congrArg (B.hT (d.f i)) h0
    have ef : ∀ l, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun l => d.ef l i
    simpa [map_sum, ef] using h1
  · funext i j
    rw [BesselCompare.cT_mul]
    exact d.ee j i

include d in
theorem even_codim : Even (B.rank - A.rank) := ⟨d.ρ, by have := d.codim; omega⟩

theorem hA_aCo (n : GA D B) (i : Fin A.rank) :
    hA A (d.aCo n) (vecA A (A.frame i)) = hA B (actV B n d.fTop) (vecA B (ι (A.frame i))) := by
  have h := congrFun (Matrix.mulVec_mulVec (fun i => hA B (actV B n d.fTop) (vecA B (ι (A.frame i)))) (gramA A)
    (gramInvA A)) i
  rw [WeilTieCompare.gram_mul_inv, Matrix.one_mulVec] at h
  rw [← h]
  have hv : ∀ k, cA D (vecA A (A.frame i) k) = if i = k then 1 else 0 := fun k => by
    unfold vecA
    rw [DualPairCheck.cA_incA, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · rw [star_one, map_one]
    · rw [star_zero, map_zero]
  change ∑ k, ∑ j, cA D (vecA A (A.frame i) k) * incA D (A.gram k j) * d.aCo n j = ∑ j, incA D (A.gram i j) * d.aCo n j
  simp only [hv, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem theta_eq (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (n : GA D B) (g : GA D A) :
    d.theta ψ Om n g = ψ (cenCo L d.c (d.tCo n)) * Om g (tPt L A d.c (d.aCo n)) := by
  simp only [theta, jac, jacOp, Heisenberg₂, symplH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem actV_one (v : B.V) : actV B 1 v = vecA B v := by
  unfold actV; rw [BesselCompare.mt_one, Matrix.one_mulVec]

theorem hD_fTop (y : B.V) (h : ∀ i, B.hD (d.f i) y = 0) : B.hD d.fTop y = 0 := by
  unfold HSpace.hD at h ⊢
  rw [fTop, map_sum]
  exact Finset.sum_eq_zero fun i _ => by split_ifs <;> simp [h]

theorem coords_of (n : GA D B) (a : Fin A.rank → AE D) (b : Fin d.ρ → AE D)
    (h : actV B n d.fTop = vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec a + ∑ l, b l • vecA B (d.e l)) :
    d.aCo n = a ∧ d.tCo n = ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then b i else 0 := by
  rw [BesselCompare.frameMat_eq, BesselCompare.eMat_mulVec] at h
  have key : ∀ y, hA B (actV B n d.fTop) (vecA B y) = incA D (B.hD d.fTop y) +
      ∑ k, a k * incA D (B.hD (ι (A.frame k)) y) + ∑ l, b l * incA D (B.hD (d.e l) y) := fun y => by
    simp only [h, BesselCompare.hA_add, BesselCompare.hA_sum, BesselCompare.hA_smul, BesselCompare.hA_vec]
  constructor
  · have e : (fun i => hA B (actV B n d.fTop) (vecA B (ι (A.frame i)))) = (gramA A).mulVec a := by
      funext i
      rw [key, d.hD_fTop _ fun l => d.fA l _]
      simp only [d.eA, map_zero, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
      exact Finset.sum_congr rfl fun k _ => (mul_comm _ _).trans (congrArg (incA D · * a k) (d.isom _ _))
    rw [aCo, e, Matrix.mulVec_mulVec, WeilTieCompare.inv_mul_gram, Matrix.one_mulVec]
  · have e : ∀ l, B.hD (d.e l) d.fTop = if l.1 + 1 = d.ρ then 1 else 0 := fun l => by
      have ef : ∀ i, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i => d.ef l i
      unfold HSpace.hD
      rw [fTop, map_sum, LinearMap.sum_apply, Finset.sum_eq_single l]
      · split_ifs
        · rw [ef, if_pos rfl]
        · rw [map_zero, LinearMap.zero_apply]
      · intro i _ hi
        split_ifs
        · rw [ef, if_neg hi.symm]
        · rw [map_zero, LinearMap.zero_apply]
      · exact fun hl => absurd (Finset.mem_univ l) hl
    have e' : ∀ x, B.hD (ι x) d.fTop = 0 := fun x => BesselCompare.hD_swap_zero (d.hD_fTop _ fun l => d.fA l x)
    rw [tCo, key, d.hD_fTop _ fun i => BesselCompare.hD_swap_zero (d.hD_fTop _ fun j => d.ff j i)]
    simp only [e, e', map_zero, mul_zero, Finset.sum_const_zero, zero_add]
    exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

theorem jac_of_fix (ψ : AddChar (AF D.host.F) ℂ) (n : GA D B) (hn : actV B n d.fTop = vecA B d.fTop)
    (f : WA L A → ℂ) : d.jac ψ n f = f := by
  have ha : d.aCo n = 0 := by
    unfold aCo
    simp only [hn, BesselCompare.hA_vec, d.hD_fTop _ fun i => d.fA i _, map_zero]
    exact Matrix.mulVec_zero _
  have ht : d.tCo n = 0 := by
    unfold tCo
    rw [hn, BesselCompare.hA_vec, d.hD_fTop _ fun i =>
      BesselCompare.hD_swap_zero (d.hD_fTop _ fun j => d.ff j i), map_zero]
  rw [jac, ha, ht, jacOp_centre, cenCo_zero, AddChar.map_zero_eq_one, one_smul]

theorem theta_one (ψ : AddChar (AF D.host.F) ℂ) (Om : GA D A → WA L A → ℂ) (g : GA D A) : d.theta ψ Om 1 g = Om g 0 := by
  rw [theta, d.jac_of_fix ψ 1 (actV_one _)]

theorem chr_one (ψ : AddChar (AF D.host.F) ℂ) : d.chr ψ 1 = 1 := by
  unfold chr
  rw [Finset.sum_eq_zero, map_zero, AddChar.map_zero_eq_one]
  intro i _
  rw [actV_one, BesselCompare.hA_vec, d.ef, if_neg (by simp), map_zero, mul_zero]

end FJDat

theorem probPair_change {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (h1 : Continuous κ) (h2 : Continuous κ.symm)
    (h3 : ∀ x, κ x ∈ ratL V W ↔ x ∈ ratL A B) (m : Measure (WA V W) × Set (WA V W)) (hm : IsProbPair V W m.1 m.2) :
    ∃ m' : Measure (WA A B) × Set (WA A B), IsProbPair A B m'.1 m'.2 ∧
      ∀ φ : WA V W → ℂ, ∫ w in m'.2, φ (κ w) ∂m'.1 = ∫ w in m.2, φ w ∂m.1 := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  have : BorelSpace (WA V W) := ⟨rfl⟩
  have := (GlobalTheory.AdelicMatrixLattice.lattice D A B).1
  have := (GlobalTheory.AdelicMatrixLattice.lattice D V W).1
  obtain ⟨μ, 𝓕⟩ := m
  obtain ⟨hμ, hF, hv⟩ := hm
  let e : WA A B ≃ᵐ WA V W :=
    { toEquiv := κ.toEquiv, measurable_toFun := h1.measurable, measurable_invFun := h2.measurable }
  have hmp : MeasurePreserving e (μ.map κ.symm) μ := MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩
  refine ⟨(μ.map κ.symm, e ⁻¹' 𝓕), ⟨AddEquiv.isAddHaarMeasure_map μ κ.symm h2 (by simpa using h1), ?_, ?_⟩,
    fun φ => hmp.setIntegral_preimage_emb e.measurableEmbedding φ 𝓕⟩
  · let f : ratL V W → ratL A B := fun y => ⟨κ.symm y, (h3 _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f :=
      ⟨fun a b hab => Subtype.ext (κ.symm.injective (congrArg Subtype.val hab)),
        fun x => ⟨⟨κ x, (h3 _).2 x.2⟩, Subtype.ext (κ.symm_apply_apply _)⟩⟩
    refine IsAddFundamentalDomain.preimage_of_equiv (G := ratL V W) (H := ratL A B) hF hmp.quasiMeasurePreserving hf ?_
    intro y x
    change κ (κ.symm y + x) = y + κ x
    rw [map_add, κ.apply_symm_apply]
  · exact (hmp.measure_preimage_emb e.measurableEmbedding 𝓕).trans hv

theorem isPureAt_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (ε : AE D) (f : WA V W → ℂ) : IsPureAt ψ V W ε f ↔ IndefiniteRowSideFullHecke.SplittingKernelQuotients.PureAt ψ ε (f ∘ κ) := by
  have hs := hκ.2.2.2.2.1
  have key : ∀ (m : Measure (WA V W) × Set (WA V W)) (m' : Measure (WA A B) × Set (WA A B)),
      (∀ u, coefH ψ V W m f (κ u) = IndefiniteRowSideFullHecke.SplittingKernelQuotients.coef ψ m' (f ∘ κ) u) →
      ((∀ x y : WA V W, ε • x = x → ε • y = 0 →
        coefH ψ V W m f (x + y) * coefH ψ V W m f 0 = coefH ψ V W m f x * coefH ψ V W m f y) ↔
      ∀ x y : WA A B, ε • x = x → ε • y = 0 → IndefiniteRowSideFullHecke.SplittingKernelQuotients.coef ψ m' (f ∘ κ) (x + y) * IndefiniteRowSideFullHecke.SplittingKernelQuotients.coef ψ m' (f ∘ κ) 0 =
        IndefiniteRowSideFullHecke.SplittingKernelQuotients.coef ψ m' (f ∘ κ) x * IndefiniteRowSideFullHecke.SplittingKernelQuotients.coef ψ m' (f ∘ κ) y) := by
    intro m m' h
    rw [κ.surjective.forall]
    refine forall_congr' fun x => ?_
    rw [κ.surjective.forall]
    refine forall_congr' fun y => ?_
    rw [← hs, ← hs, κ.injective.eq_iff, κ.map_eq_zero_iff, ← h, ← h, ← h, ← h, map_add, map_zero]
  have hw : ∀ u w, Heisenberg₂ ψ V W (κ u) f (κ w) * star (f (κ w)) = IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.rho ψ u (f ∘ κ) w * star ((f ∘ κ) w) :=
    fun u w => congrArg (· * star (f (κ w))) (congrFun (WeilTieCompare.heis_change hκ ψ u f) w)
  refine and_congr (iff_of_true (WeilTieCompare.exists_probPair V W) (WeilTieCompare.exists_probPair A B))
    ⟨fun h m' hm' => ?_, fun h m hm => ?_⟩
  · obtain ⟨m, hm, hi⟩ := probPair_change κ.symm hκ.2.1 hκ.1
      (fun x => (hκ.2.2.2.1 (κ.symm x)).symm.trans (by rw [κ.apply_symm_apply])) m' hm'
    refine (key m m' fun u => ?_).1 (h m hm)
    refine Eq.trans ?_ (hi fun w => IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.rho ψ u (f ∘ κ) w * star ((f ∘ κ) w))
    simp only [← hw, κ.apply_symm_apply]
    rfl
  · obtain ⟨m', hm', hi⟩ := probPair_change κ hκ.1 hκ.2.1 hκ.2.2.2.1 m hm
    refine (key m m' fun u => ?_).2 (h m' hm')
    refine (hi fun w => Heisenberg₂ ψ V W (κ u) f w * star (f w)).symm.trans ?_
    simp only [hw]
    rfl

theorem isFact_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (f : WA V W → ℂ) : IsFact ψ V W f ↔ IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsPure ψ (f ∘ κ) ∧ IsVacAE ψ V W f :=
  ⟨fun h => ⟨⟨fun v => (isPureAt_iff hκ ψ _ f).1 (h.fin v), fun v => (isPureAt_iff hκ ψ _ f).1 (h.inf v)⟩, h.vac⟩,
    fun h => ⟨fun v => (isPureAt_iff hκ ψ _ f).2 (h.1.1 v), fun v => (isPureAt_iff hκ ψ _ f).2 (h.1.2 v), h.2⟩⟩

theorem coefH_smul (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (m) (c : ℂ) (f : WA V W → ℂ) (u : WA V W) :
    coefH ψ V W m (c • f) u = c * star c * coefH ψ V W m f u := by
  unfold coefH
  rw [← integral_const_mul]
  congr 1
  funext w
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem IsFact.smul {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {f : WA V W → ℂ} (h : IsFact ψ V W f) (c : ℂ) :
    IsFact ψ V W (c • f) := by
  have k : ∀ ε, IsPureAt ψ V W ε f → IsPureAt ψ V W ε (c • f) := fun ε h => ⟨h.1, fun m hm x y hx hy => by
    simp only [coefH_smul]
    linear_combination (c * star c) ^ 2 * h.2 m hm x y hx hy⟩
  obtain ⟨S, hS⟩ := h.vac
  refine ⟨fun v => k _ (h.fin v), fun v => k _ (h.inf v), S, fun u hu => funext fun w => ?_⟩
  have := congrFun (hS u hu) w
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination c * this

section Comparison₂

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

theorem resEta_line (T : ThetaTied D X) {L : HSp D} (h : L.rank = 1) : ResEta D (T.eChr X.etaT⁻¹) L.rank := by
  rw [h, map_inv]; exact resEta_inv T.etaT_res

theorem resEta_pow (T : ThetaTied D X) (n : ℕ) : ResEta D (T.eChr (X.etaT ^ n)) n :=
  ⟨T.etaT_res.1, fun η hη a => by rw [map_pow, MonoidHom.pow_apply, T.etaT_res.2 η hη a, pow_one]⟩

theorem omZ_eq (Wl : WeilTied D X T) {L A : HSp D} (hL : L.rank = 1) (hA : 1 < A.rank) (χ : X.Chr)
    (hχ : ResEta D (T.eChr χ) A.rank) (Φ : X.Sch L A) (g : GA D A) :
    omZ Wl L A Φ g = Wl.evS L A (Wl.om L A X.etaT⁻¹ χ (1, g) Φ) := by
  have h0 : ResEta D (T.eChr (χ⁻¹ * X.etaT ^ A.rank)) 0 := by
    rw [map_mul, map_inv]
    exact resEta_parity (resEta_mul (resEta_inv hχ) (resEta_pow T _)) (by omega)
  have hx : IsDetRoot L 1 1 := by simp [IsDetRoot]
  have := Wl.om_tw.twW_up L A X.etaT⁻¹ χ _ (hL ▸ hA) (resEta_line T hL) hχ h0 1 g 1 hx
  rw [mul_inv_cancel_left, map_one, inv_one, Circle.coe_one, one_smul] at this
  rw [omZ, this]

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem isBesPos_of_besselTied (Bt : BesselTied D X T Wl) (ho : Odd (B.rank - A.rank)) (hr : A.rank ≤ B.rank)
    (hs : A.SigOK) (hι : HSpace.IsIsomEmb A B ι) (p : X.Pos A B ι) (hp : ∃ u, HEq p (X.posSym u)) :
    IsBesPos Wl (Bt.dat A B ι ho p) p := by
  intro μ 𝓕 hv ν 𝓝 hN s hs' σ φ F hφ
  rw [Bt.bper A B ι ho hr hs hι p hp σ μ 𝓕 hv ν 𝓝 hN.1 hN.2.1 hN.2.2 s hs' φ F hφ, Bt.besC_one, one_mul]
  rfl

theorem trCusp_one (F : X.cusp B) : trCusp X B 1 F = F := Subtype.ext (by simp [trCusp])

theorem isTranslSum_refl (p : X.Pos A B ι) : IsTranslSum X p p :=
  fun σ F => ⟨1, fun _ => 1, fun _ => σ, fun _ => 1, fun φ => by simp [trCusp_one]⟩

theorem IsTranslSum.exists_ne_zero {p p₀ : X.Pos A B ι} (h : IsTranslSum X p p₀) {σ φ F}
    (hne : X.Bper A B ι p σ φ F ≠ 0) : ∃ σ' y, X.Bper A B ι p₀ σ' φ (trCusp X B y F) ≠ 0 := by
  obtain ⟨n, a, σ', y, hs⟩ := h σ F
  rw [hs] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨σ' i, y i, right_ne_zero_of_mul hi⟩

theorem isAniso_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) : IsAniso V := by
  refine (BesselCompare.isAniso_iff V).2 fun v hv => ?_
  by_contra hne
  have h1 := hs D.host.φ₀
  rw [hp] at h1
  have h2 := Formalism.UG.P.stdform_sig_pos _ h1 (fun k => D.host.φ₀ (BesselCompare.co V v k)) fun e => hne (by
    apply V.frame.repr.injective
    refine Finsupp.ext fun k => ?_
    simpa [BesselCompare.co] using congrFun e k)
  have hc := D.host.isCMField_hostE
  have h3 : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀
  have h4 := congrArg (fun a => (D.host.φ₀ a).re) ((BesselCompare.hT_co V v v).symm.trans hv)
  simp only [map_sum, map_mul, h3, map_zero, Complex.zero_re] at h4
  exact h2.ne' h4

theorem isAniso_Xs (T : ThetaTied D X) (t : ℕ) {j : ℕ} (hj : j ≤ D.R.m) : IsAniso (X.Xs t j) :=
  isAniso_of_posDef (X.Xs_sig t j hj).1 (T.xs_pos t j hj)

theorem one_lt_rank_Xs (X : ThetaX D) (t : ℕ) {j : ℕ} (hj : j ≤ D.R.m) : 1 < (X.Xs t j).rank := by
  rw [X.Xs_rank t j hj]
  have := D.R.m_add_three_le_k
  omega

theorem PerTied.mem_fact_iff (P : PerTied Wl) (hr : A.rank < B.rank) :
    (∀ Φ, Φ ∈ X.fact A B ↔ IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS A B Φ ∘ kap A B) ∧ IsVacAE Wl.ψ A B (Wl.evS A B Φ)) ∧
    ∀ Φ, Φ ∈ X.fact B A ↔ IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS B A Φ ∘ kapT A B) ∧ IsVacAE Wl.ψ B A (Wl.evS B A Φ) :=
  ⟨fun Φ => by rw [P.fact A B hr.ne]; exact isFact_iff (WeilTieCompare.isChange_kap hr.le) _ _,
    fun Φ => by rw [P.fact B A hr.ne']; exact isFact_iff (WeilTieCompare.isChange_kapT hr) _ _⟩

theorem FJTied.fj_all (J : FJTied Wl) (t j : ℕ) (hj : j < D.R.m) (ho : Odd j)
    (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)) :
    ∃ (d : FJDat J.line (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (p₀ : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)),
      IsFJPos Wl (J.eFJ t j hj ho) d p₀ ∧ IsTranslSum X p p₀ :=
  (J.fj_only t j hj ho p).elim fun d hd => ⟨d, p, hd, isTranslSum_refl p⟩

theorem PerTied.fj_all (P : PerTied Wl) (t j : ℕ) (hj : j < D.R.m) (ho : Odd j)
    (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)) :
    ∃ (d : FJDat P.line (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (p₀ : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)),
      IsFJPos Wl (P.eFJ t j hj ho) d p₀ ∧ IsTranslSum X p p₀ :=
  P.toFJTied.fj_all t j hj ho p

theorem IsFJPos.isLinearMap {L : HSp D} {k : X.FJd A B ι ≃ₗ[ℂ] X.Sch L A} {d : FJDat L A B ι} {p : X.Pos A B ι}
    (h : IsFJPos Wl k d p) {μ 𝓕 ν 𝓝} (hv : IsVolPair D A μ 𝓕) (hN : IsUnitN B d.eM ν 𝓝) {s : GA D A → GA D B}
    (hs : ∀ g, EmbRel B A ι (s g) g) {φ : X.AF A} (hφ : IsAniso A ∨ φ ∈ X.cusp A) (F : X.cusp B)
    (hc : ∀ Φ, d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s (T.ev A φ) (T.ev B (F : X.AF B))) :
    IsLinearMap ℂ fun σ => X.Bper A B ι p σ φ F := by
  refine ⟨fun σ σ' => ?_, fun c σ => ?_⟩
  · simp only [h μ 𝓕 hv ν 𝓝 hN s hs _ φ F hφ, FJDat.per]
    rw [← mul_add, ← integral_add (hc _).2 (hc _).2]
    congr 2
    funext g
    rw [← integral_add ((hc _).1 g) ((hc _).1 g)]
    congr 1
    funext n
    simp only [FJDat.perFun, FJDat.theta_eq, omZ, map_add, Pi.add_apply]
    ring
  · simp only [h μ 𝓕 hv ν 𝓝 hN s hs _ φ F hφ, FJDat.per, smul_eq_mul]
    rw [mul_left_comm, ← integral_const_mul c]
    congr 2
    funext g
    rw [← integral_const_mul c]
    congr 1
    funext n
    simp only [FJDat.perFun, FJDat.theta_eq, omZ, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem FJTied.isLinearMap (J : FJTied Wl) (hI : FJInt D)
    (hN : ∀ (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → ∃ ν 𝓝, IsUnitN B e ν 𝓝)
    (t j : ℕ) (hj : j < D.R.m) (ho : Odd j) {μ 𝓕} (hv : IsVolPair D (X.Xs t j) μ 𝓕)
    (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (φ F) : IsLinearMap ℂ fun σ => X.Bj t j p σ φ F := by
  obtain ⟨d, hd⟩ := J.fj_only t j hj ho p
  obtain ⟨ν, 𝓝, hν⟩ := hN _ _ _ d.isIsoSub
  have hs := fun g => (GlobalTheory.AutFunCompare.embRel_iff _ _ _ d.isom _ g).2 rfl
  have ha := isAniso_Xs T t hj.le
  exact hd.isLinearMap hv hν hs (Or.inl ha) F fun Φ =>
    hI X T Wl _ _ _ _ d (one_lt_rank_Xs X t hj.le) ha μ 𝓕 hv.1.1 hv.2 ν 𝓝 hν _ hs Φ _ _ (T.ev_aut _ _) (T.ev_aut _ _)

theorem codim_XYs (X : ThetaX D) (t : ℕ) {j : ℕ} (hj : j < D.R.m) :
    (X.Ys t j).rank - (X.Xs t j).rank = D.R.m - 1 - j := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [X.Xs_rank t j hj.le, X.Ys_rank t j hj.le, mul_add, mul_one]
  omega

theorem odd_codim_XYs (X : ThetaX D) (t : ℕ) {j : ℕ} (hj : j < D.R.m) (he : Even j) :
    Odd ((X.Ys t j).rank - (X.Xs t j).rank) := by
  have hm := Nat.even_iff.1 D.R.m_even
  rw [codim_XYs X t hj, Nat.odd_iff]
  rw [Nat.even_iff] at he
  omega

theorem coefH_eq_thCoef (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (m : Measure (WA V W) × Set (WA V W)) (f : WA V W → ℂ)
    (u : WA V W) : coefH ψ V W m f u = GlobalTheory.Mem.Th.thCoef ψ V W m.1 m.2 f u := rfl

theorem isBesPos_iff_besGlob (d : BesDat A B ι) (p : X.Pos A B ι) :
    IsBesPos Wl d p ↔ GlobalTheory.Mem.Th.BesGlob T Wl.ψ d p :=
  ⟨fun h σ μ 𝓕 hv s hs φ F hφ ν 𝓝 h1 h2 h3 => h μ 𝓕 hv ν 𝓝 ⟨h1, h2, h3⟩ s hs σ φ F hφ,
    fun h μ 𝓕 hv ν 𝓝 hN s hs σ φ F hφ => h σ μ 𝓕 hv s hs φ F hφ ν 𝓝 hN.1 hN.2.1 hN.2.2⟩

theorem isPureAt_of_all {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {ε : AE D} {f : WA V W → ℂ}
    (h : GlobalTheory.Mem.Th.IsPureAt ψ V W ε f) : IsPureAt ψ V W ε f :=
  ⟨WeilTieCompare.exists_probPair V W, fun m hm x y hx hy =>
    (h.2 m ⟨hm.1, hm.2.1⟩).2 x y (fun i j => congrFun (congrFun hx i) j) (fun i j => congrFun (congrFun hy i) j)⟩

theorem isFact_of_isPureFun {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {f : WA V W → ℂ}
    (h : GlobalTheory.Mem.Th.IsPureFun ψ V W f) (hv : IsVacAE ψ V W f) : IsFact ψ V W f :=
  ⟨fun v => isPureAt_of_all (h.1 v), fun v => isPureAt_of_all (h.2 v), hv⟩

section Realises

open GlobalTheory.Mem.Th (Realises WeilFun Tow RecFun InfF)

variable {θ : InfF D} {Bt : BesselTied D X T Wl} {Wf : WeilFun D Wl.ψ} {Tw : Tow D} {Rc : RecFun D θ Wl.ψ}

theorem bes_of_realises (h : Realises Bt Wf Tw Rc) (t j : ℕ) (hj : j < D.R.m) (he : Even j)
    (d : BesDat (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (hd : (d.y : GA D (X.Ys t j)) = 1) : ∃ p, IsBesPos Wl d p :=
  (h.besAll _ _ _ (odd_codim_XYs X t hj he) (X.Xs_sig t j hj.le).1 (X.iXYs_isom t j hj) d hd).imp fun p hp =>
    (isBesPos_iff_besGlob d p).2 hp.2

theorem bes_only_of_realises (h : Realises Bt Wf Tw Rc) (t j : ℕ) (hj : j < D.R.m) (he : Even j)
    (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)) :
    (∃ d : BesDat (X.Xs t j) (X.Ys t j) (X.iXYs t j), (d.y : GA D (X.Ys t j)) = 1 ∧ IsBesPos Wl d p) ∨ ∃ u,
      (⟨_, _, _, p⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι) = ⟨_, _, _, X.pos1 u⟩ :=
  (h.besOnly _ _ _ (odd_codim_XYs X t hj he) (X.Xs_sig t j hj.le).1 (X.iXYs_isom t j hj) p).imp_left fun hp =>
    ⟨_, Bt.dat_y _ _ _ _ p, (isBesPos_iff_besGlob _ p).2 hp⟩

theorem fact_of_realises (h : Realises Bt Wf Tw Rc) (hF : FactPure D) (V W : HSp D) : X.fact V W = factSet Wl V W := by
  ext Φ
  have hΦ : Wl.evS V W Φ ∈ Set.range (Wl.evS V W) := ⟨Φ, rfl⟩
  rw [h.sch] at hΦ
  exact (h.fact V W Φ).trans (hF _ Wl.ψ_std V W _ hΦ).symm

def PerTied.ofRealises (h : Realises Bt Wf Tw Rc) (J : FJTied Wl) (hF : FactPure D)
    (h1 : ∀ u, ∃ d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0), (d.y : GA D (D.sp.Y 0)) = 1 ∧
      ∃ p₀, IsBesPos Wl d p₀ ∧ IsTranslSum X (X.pos1 u) p₀) : PerTied Wl where
  toFJTied := J
  bes := bes_of_realises h
  bes_all t j hj he p := by
    rcases bes_only_of_realises h t j hj he p with ⟨d, hd, hp⟩ | ⟨u, hu⟩
    · exact ⟨d, hd, p, hp, isTranslSum_refl p⟩
    · have key : ∀ q : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι, q = ⟨_, _, _, X.pos1 u⟩ →
          ∃ d : BesDat q.1 q.2.1 q.2.2.1, (d.y : GA D q.2.1) = 1 ∧ ∃ p₀, IsBesPos Wl d p₀ ∧ IsTranslSum X q.2.2.2 p₀ := by
        rintro q rfl
        exact h1 u
      exact key _ hu
  fact V W _ := fact_of_realises h hF V W

end Realises

end Comparison₂

def negLine (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 1 (fun _ => true) 0 1

theorem negLine_gram (D : D7) (i j) : (negLine D).gram i j = -1 :=
  (Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 1 (fun _ => true) 0 1 i j).trans (if_pos (Subsingleton.elim _ _))

theorem isNegLine_negLine (D : D7) : IsNegLine (negLine D) := by
  refine ⟨rfl, fun τ => ?_, fun _ => rfl⟩
  have : (negLine D).gram.map τ = -(1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    rw [Matrix.map_apply, negLine_gram, map_neg, map_one, Subsingleton.elim (α := Fin 1) i j]
    exact congrArg Neg.neg (Matrix.one_apply_eq (α := ℂ) (n := Fin 1) j).symm
  rw [this]
  exact Formalism.UG.P.stdform_sig_neg_one (n := Fin 1)

example (D : D7) : lineNorm (negLine D) = -1 := by
  rw [lineNorm_eq]
  exact (Fin.sum_univ_one _).trans ((Fin.sum_univ_one _).trans (negLine_gram D _ _))

def sixSpace (D : D7) : HSp D :=
  Examples₂.stdSpace Examples₂.star_isIntegral 6 ![false, false, false, true, false, true] 4 2

def twoToSix (D : D7) : (Fin 2 → D.host.E) →ₗ[D.host.E] (Fin 6 → D.host.E) where
  toFun x := ![x 0, x 1, 0, 0, 0, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

theorem sixSpace_hT (D : D7) (x y : Fin 6 → D.host.E) : (sixSpace D).hT x y =
    star (x 0) * y 0 + star (x 1) * y 1 + star (x 2) * y 2 - star (x 3) * y 3 + star (x 4) * y 4 - star (x 5) * y 5 := by
  refine (Examples₂.diagForm_apply 6 _ x y).trans ?_
  simp [Fin.sum_univ_six, Examples₂.sgn]
  ring

def eSix (D : D7) : Fin 2 → Fin 6 → D.host.E := ![![0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 1]]

def fSix (D : D7) : Fin 2 → Fin 6 → D.host.E := ![![0, 0, 2⁻¹, -2⁻¹, 0, 0], ![0, 0, 0, 0, 2⁻¹, -2⁻¹]]

theorem six_rel (D : D7) (i j : Fin 2) (x : Fin 2 → D.host.E) :
    (sixSpace D).hT (eSix D j) (eSix D i) = 0 ∧ (sixSpace D).hT (fSix D j) (fSix D i) = 0 ∧
    (sixSpace D).hT (fSix D j) (eSix D i) = (if i = j then 1 else 0) ∧
    (sixSpace D).hT (twoToSix D x) (eSix D i) = 0 ∧ (sixSpace D).hT (twoToSix D x) (fSix D i) = 0 := by
  have h2 : star (2⁻¹ : D.host.E) = 2⁻¹ := by rw [star_inv₀, star_ofNat]
  have h3 : (2⁻¹ : D.host.E) + 2⁻¹ = 1 := by norm_num
  simp only [sixSpace_hT]
  fin_cases i <;> fin_cases j <;> simp [eSix, fSix, twoToSix, h2, h3]

theorem six_isom (D : D7) :
    HSpace.IsIsomEmb (Examples₂.posSpace Examples₂.star_isIntegral 2) (sixSpace D) (twoToSix D) := by
  intro (x : Fin 2 → D.host.E) (y : Fin 2 → D.host.E)
  refine (sixSpace_hT D (twoToSix D x) (twoToSix D y)).trans (Eq.trans ?_ (Examples₂.diagForm_apply 2 _ x y).symm)
  simp [twoToSix, Fin.sum_univ_two, Examples₂.sgn]

def sixDat (D : D7) (β c : D.host.E) (hβ : β ≠ 0) (hc : c ≠ 0) :
    FJDat (negLine D) (Examples₂.posSpace Examples₂.star_isIntegral 2) (sixSpace D) (twoToSix D) where
  line := isNegLine_negLine D
  isom := six_isom D
  ρ := 2
  codim := (rfl : 2 + 2 * 2 = 6)
  e := eSix D
  f := fSix D
  ee i j := (six_rel D i j 0).1
  ff i j := (six_rel D i j 0).2.1
  ef i j := (six_rel D i j 0).2.2.1
  eA i x := (six_rel D i i x).2.2.2.1
  fA i x := (six_rel D i i x).2.2.2.2
  β _ := β
  β_ne _ := hβ
  c := c
  c_ne := hc

def topDat {L : HSp D} (hL : IsNegLine L) (A : HSp D) : FJDat L A A LinearMap.id where
  line := hL
  isom _ _ := rfl
  ρ := 0
  codim := rfl
  e := Fin.elim0
  f := Fin.elim0
  ee i := i.elim0
  ff i := i.elim0
  ef i := i.elim0
  eA i := i.elim0
  fA i := i.elim0
  β := Fin.elim0
  β_ne i := i.elim0
  c := -1
  c_ne := neg_ne_zero.2 one_ne_zero

example {L : HSp D} (hL : IsNegLine L) (A : HSp D) (ψ Om s φ F g n) :
    (topDat hL A).perFun ψ Om s φ F g n = star (φ g) * F ((n : GA D A) * s g) * Om g 0 := by
  have h0 : (topDat hL A).fTop = 0 := Finset.sum_of_isEmpty (ι := Fin 0) _
  have hv : vecA A 0 = 0 := by funext i; simp [vecA]
  have h1 : (topDat hL A).chr ψ n = 1 := by
    unfold FJDat.chr
    rw [Finset.sum_eq_zero, map_zero, AddChar.map_zero_eq_one]
    exact fun i _ => Fin.elim0 i
  rw [FJDat.perFun, h1, star_one, mul_one, FJDat.theta,
    (topDat hL A).jac_of_fix ψ n (by rw [h0, actV, hv, Matrix.mulVec_zero])]

example (L A : HSp D) (a : Fin A.rank → AE D) (i k) :
    (kap L A).symm (tPt L A (-1) a) i k = incA D (L.hD (L.frame i) (lineVec L)) * a k := by
  rw [kap_symm_tPt, neg_mul, one_mul, neg_neg]

end GlobalTheory.Per

end
