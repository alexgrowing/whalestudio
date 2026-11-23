import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.HasLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

variable {D : D7} {a b c n r t : ℕ}

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev cv (D : D7) (v : Pl D) : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E := compFin D.host.F D.host.E v

abbrev mm (x : Mx D a b) (y : Mx D b c) : Mx D a c := HMul.hMul x y

open Classical in

def IsIdem (S : Finset (Pl D)) (e : AE D) : Prop :=
  (∀ w, compInf D.host.F D.host.E w e = 1) ∧ ∀ v, cv D v e = if v ∈ S then 1 else 0

def IntOff (S : Finset (Pl D)) (x : Mx D a b) : Prop := ∀ v ∉ S, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v

open Classical in

def Good (S : Finset (Pl D)) (e : AE D) (Φ : Mx D a b → ℂ) : Prop := ∀ x, Φ x = if IntOff S x then Φ (e • x) else 0

abbrev KOff (D : D7) (n : ℕ) (S : Finset (Pl D)) : Subgroup (G D n) :=
  levelOff D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) S

abbrev KAt (D : D7) (n : ℕ) (v : Pl D) : Subgroup (G D n) := K D n ⊓ atPts D.sp.cm.sig (Jst D n) {v}

def hermS (D : D7) (n : ℕ) (e : AE D) : AddSubgroup (hermA D n) where
  carrier := {x | e • x.1 = x.1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, smul_add] at *
    rw [hx, hy]
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_neg, smul_neg] at *
    rw [hx]

def IsN (g : G D n) : Prop := ∃ x : Mx D n n, mat g = blk4 1 x 0 1

def IsM (g : G D n) : Prop := ∃ x : GL (Fin n) (AE D), mat g = blk4 x.1 0 0 (adj (x⁻¹).1)

def IsW (g : G D n) : Prop := mat g = blk4 0 1 (-1) 0

def jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : Mx D a n :=
  (Matrix.fromCols x v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm

def ip (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) : Mx D a b := mm (adj x) (mm (gA V) y)

def yv (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : Mx D r t := mm (rat b₀.1⁻¹) (ip V z.1 z.2)

def qv (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : Mx D t t :=
  ip V z.2 z.2 - pr b₀ (yv V b₀ z) (yv V b₀ z)

def Free (e : AE D) (z : Mx D a r × Mx D a t) : Prop :=
  ∃ (L₁ : Mx D r a) (L₂ : Mx D t a), mm L₁ z.1 = e • 1 ∧ mm L₁ z.2 = 0 ∧ mm L₂ z.1 = 0 ∧ mm L₂ z.2 = e • 1

structure IsOrb (V : HSp D) (b₀ : HermE D r) (e : AE D) (ν : Measure (Mx D V.rank r × Mx D V.rank t)) : Prop where
  fin : IsFiniteMeasureOnCompacts ν
  supp : ν {z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} = 0
  invU : ∀ h : GA D V, e • (mt V h - 1) = mt V h - 1 → ν.map (fun z => (mm (mt V h) z.1, mm (mt V h) z.2)) = ν
  invS : ∀ y : Mx D r t, e • y = y → ν.map (fun z => (z.1, z.2 + mm z.1 y)) = ν
  cov : ∀ g : GL (Fin t) (AE D), e • (g.1 - 1) = g.1 - 1 →
    ν.map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν

structure Stg {B W : HSp D} (d : HypDec B W t) (hn : W.rank + t = n) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
    (θ : InfFam D) (μB : Measure (Mx D B.rank n)) (μW : Measure (Mx D W.rank n))
    (ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)) (ωW : G D n →* Module.End ℂ (schwartzA θ W.rank n)) : Prop where
  big : W.rank + 2 < 2 * t
  lt : W.rank < t
  pos : 1 ≤ W.rank
  hψ : IsCharAF D.host.F ψ
  hχ : IsHeckeChar D χ
  hη : ResEta D χ W.rank
  hθ : IsInfFam θ
  hμB : ∃ 𝓕, IsCovolOne (ratMx D B.rank n) μB 𝓕
  hμW : ∃ 𝓕, IsCovolOne (ratMx D W.rank n) μW 𝓕
  hB : IsWeilSch ψ χ θ B μB ωB
  hW : IsWeilSch ψ χ θ W μW ωW

structure IkD {B W : HSp D} (d : HypDec B W t) (n : ℕ) where
  l : Lvl B
  good : l.Good
  νK : Measure l.K
  haarK : νK.IsHaarMeasure
  probK : IsProbabilityMeasure νK
  μ₁ : Measure (Mx D t n)
  cov₁ : ∃ 𝓕, IsCovolOne (ratMx D t n) μ₁ 𝓕
  m : Measure (GA D W)
  haar : m.IsHaarMeasure

def ikp {B W : HSp D} {d : HypDec B W t} (I : IkD d n) (Φ : Mx D B.rank n → ℂ) : Mx D W.rank n → ℂ :=
  ikS d I.μ₁ (projS I.νK Φ)

def orb (W : HSp D) (m : Measure (GA D W)) (Ψ : Mx D W.rank n → ℂ) (x : Matrix (Fin W.rank) (Fin n) D.host.E) : ℂ :=
  ∫ h, Ψ (mm (mt W h⁻¹) (rat x)) ∂m

def ext0 (hn : r + t = n) (x₀ : Matrix (Fin a) (Fin r) D.host.E) : Matrix (Fin a) (Fin n) D.host.E :=
  (Matrix.fromCols x₀ (0 : Matrix (Fin a) (Fin t) D.host.E)).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm

def pch (ψ : AddChar (AF D.host.F) ℂ) (x T : Mx D n n) : ℂ := ψ (halfTr (Matrix.trace (mm x T)))

structure Cut (D : D7) (n : ℕ) (v : Pl D) where
  s : Finset (hermA D n)
  co : hermA D n → ℂ
  inf : ∀ x ∈ s, ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0
  off : ∀ x ∈ s, ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0

def cutF {v : Pl D} (ψ : AddChar (AF D.host.F) ℂ) (C : Cut D n v) (T : Mx D n n) : ℂ := ∑ x ∈ C.s, C.co x * pch ψ x.1 T

def cutR {v : Pl D} (nb : hermA D n → G D n) (C : Cut D n v) (F : G D n → ℂ) (g : G D n) : ℂ :=
  ∑ x ∈ C.s, C.co x * F (g * nb x)

def IntAt (v : Pl D) (x : hermA D n) : Prop :=
  (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧ (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧
    ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v

def Cut.Kills {v : Pl D} (ψ : AddChar (AF D.host.F) ℂ) (C : Cut D n v) (r : ℕ) : Prop :=
  ∀ β : HermE D n, β.1.rank < r → (∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1) → cutF ψ C (rat β.1) = 0

def IdemEx : Prop := ∀ (D : D7) (S : Finset (Pl D)), (∃ e, IsIdem S e) ∧ ∀ e, IsIdem S e → e * e = e ∧ cA D e = e

def GoodEv : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b : ℕ), ∀ Φ ∈ schwartzA θ a b,
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ

def BumpEx : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b : ℕ) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∀ C : Set (Mx D a b), IsCompact C → (∀ x ∈ C, IntOff S x) → ∃ η : Fin a → Mx D 1 b → ℂ,
    ∀ i, η i ∈ schwartzA θ 1 b ∧ HasCompactSupport (η i) ∧ Good S e (η i) ∧ (∀ y, 0 ≤ (η i y).re ∧ (η i y).re ≤ 1 ∧ (η i y).im = 0) ∧
      ∀ x ∈ C, η i (x.submatrix (fun _ => i) id) = 1

def Major : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b : ℕ) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∀ Φ ∈ schwartzA θ a b, Good S e Φ → ∃ Φ₀ ∈ schwartzA θ a b, Good S e Φ₀ ∧ (∀ x, 0 ≤ (Φ₀ x).re ∧ (Φ₀ x).im = 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ Φ₁ ∈ schwartzA θ a b, Good S e Φ₁ ∧ HasCompactSupport Φ₁ ∧ ∀ x, ‖Φ x - Φ₁ x‖ ≤ ε * (Φ₀ x).re

def GenG : Prop := ∀ (D : D7) (n : ℕ) (A : Set (G D n)), IsClosed A → 1 ∈ A →
  (∀ g, IsN g ∨ IsM g ∨ IsW g → ∀ x ∈ A, g * x ∈ A) → A = Set.univ

def GenK : Prop := ∀ (D : D7) (n : ℕ), ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ A : Set (G D n), IsClosed A → 1 ∈ A →
  (∀ g ∈ KOff D n S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D n S ∧ g = w * u * w⁻¹) → ∀ x ∈ A, g * x ∈ A) →
  (KOff D n S : Set (G D n)) ⊆ A

def WMaj : Prop := ∀ (D : D7) (n : ℕ) (V : HSp D) ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ, IsInfFam θ → ∀ μ, (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) → ∀ ω, IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n,
    Continuous (fun u : G D n × Mx D V.rank n => (ω u.1 Φ).1 u.2) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ M ∈ schwartzA θ V.rank n, ∀ g ∈ C, ∀ x, ‖(ω g Φ).1 x‖ ≤ ‖M x‖

def FixW : Prop := ∀ (D : D7) (n : ℕ) (V : HSp D) ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ, IsInfFam θ → ∀ μ, (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) → ∀ ω, IsWeilSch ψ χ θ V μ ω →
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ Φ : schwartzA θ V.rank n, Good S e Φ.1 → ∀ u ∈ KOff D n S, ω u Φ = Φ

def FixTh : Prop := ∀ (D : D7) (ρ p : ℕ) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ∀ θ, IsInfFam θ →
  ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 →
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Good S e (Ω 1) → ∀ u ∈ KOff D p S, ∀ h, Ω (h * u) = Ω h

def ThProd : Prop := ∀ (D : D7) (ρ p : ℕ) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, IsDiagInv b₀ →
  ∀ χ, IsHeckeChar D χ → ResEta D χ ρ → 1 ≤ ρ → ∀ θ, IsInfFam θ → ∀ η : Fin ρ → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p) →
    ∃ Ω, IsTh ψ χ θ b₀ m.μ Ω ∧ ∀ y, Ω 1 y = ∏ i, η i (y.submatrix (fun _ => i) id)

def RowTotal : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ρ p : ℕ) (μ : Measure (Mx D ρ p)), μ.IsAddHaarMeasure →
  ∀ u : Mx D ρ p → ℂ, Continuous u → (∀ η : Fin ρ → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p ∧ HasCompactSupport (η i)) →
    ∫ y, u y * conj (∏ i, η i (y.submatrix (fun _ => i) id)) ∂μ = 0) → u = 0

def MuCell : Prop := ∀ (D : D7) (p : ℕ) (mu : (G D p → ℂ) → ℂ), IsResMu mu → ∀ nb, IsNMap nb → ∀ w, IsW w →
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ lam : Measure (hermS D p e), lam.IsAddHaarMeasure →
    (∀ f, IsRho f → (∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g) → mu f = 0) ∨
    ∃ c : ℝ, 0 < c ∧ ∀ f, IsRho f → (∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g) →
      Integrable (fun x : hermS D p e => f (w * nb x.1)) lam ∧ mu f = c * ∫ x, f (w * nb x.1) ∂lam

structure IsFib (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (b₀ : HermE D r) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (fib : Measure (Mx D V.rank r)) : Prop where
  fin : IsFiniteMeasureOnCompacts fib
  supp : fib {x | ip V x x ≠ rat b₀.1} = 0
  inv : ∀ h : GA D V, fib.map (fun x => mm (mt V h) x) = fib
  int : ∀ φ ∈ schwartzA θ V.rank r, Integrable φ fib ∧ W ψ V μ lam φ b₀ = ∫ x, φ x ∂fib

def FibEx : Prop := ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ ψ, IsCharAF D.host.F ψ → ∀ θ, IsInfFam θ →
  ∀ μ, (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → ∀ lam, (∃ 𝓖, IsCovolOneH lam 𝓖) → ∀ b₀ : HermE D r, b₀.1.det ≠ 0 →
    ∃ fib, IsFib ψ θ V b₀ μ lam fib

def PartFT : Prop := ∀ (D : D7) (n r t : ℕ) (hn : r + t = n) (M : Maps D hn) (V : HSp D) ψ, IsCharAF D.host.F ψ →
  ∀ χ, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ, IsInfFam θ → ∀ μ, (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) →
  ∀ ω, IsWeilSch ψ χ θ V μ ω → ∀ μr μt, (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) → (∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) →
  ∀ Φ : schwartzA θ V.rank n, (ω M.w Φ).1 0 = ∫ x, Φ.1 (jn hn x 0) ∂μr ∧ (fun x => Φ.1 (jn hn x 0)) ∈ schwartzA θ V.rank r ∧
    ∀ w, IsW w → ∀ x v₀, (ω (M.emb w) Φ).1 (jn hn x v₀) = ∫ v, Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V v₀ v))) ∂μt

def RCell : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ (M : Maps D hn) (m : Meas D W.rank t) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
  ∀ μr μt, (∃ 𝓕, IsCovolOne (ratMx D B.rank W.rank) μr 𝓕) → (∃ 𝓕, IsCovolOne (ratMx D B.rank t) μt 𝓕) →
  ∀ fib, IsFib ψ θ B b₀ μr m.lz fib → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ (Φ : schwartzA θ B.rank n) nb, IsNMap nb → ∀ w, IsW w →
    Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt) ∧ ∀ x : hermA D t,
      Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω (w * nb x) =
        ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv B b₀ z)) * pch ψ x.1 (qv B b₀ z) ∂(fib.prod μt)

def PosExt : Prop := ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (A : Submodule ℂ (X → ℂ)), (∀ f ∈ A, Continuous f ∧ HasCompactSupport f) →
  (∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) → (∀ f ∈ A, star f ∈ A) → (∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
  (∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1) →
  (∀ L : A →ₗ[ℂ] ℂ, (∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0) →
    ∃ ν : Measure X, IsFiniteMeasureOnCompacts ν ∧ ∀ f : A, L f = ∫ x, f.1 x ∂ν) ∧
  ∀ ν ν' : Measure X, IsFiniteMeasureOnCompacts ν → IsFiniteMeasureOnCompacts ν' →
    (∀ f ∈ A, ∫ x, f x ∂ν = ∫ x, f x ∂ν') → ν = ν'

def ApproxId : Prop := ∀ (D : D7) (t : ℕ) ψ, IsCharAF D.host.F ψ → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  ∀ lam : Measure (hermS D t e), lam.IsAddHaarMeasure → ∃ (g : ℕ → hermS D t e → ℂ) (G : ℕ → Mx D t t → ℝ),
    (∀ k, Integrable (g k) lam ∧ (∀ x, ‖g k x‖ ≤ 1) ∧ ∀ T ∈ hermA D t, 0 ≤ G k T ∧ ∫ x, g k x * pch ψ x.1.1 T ∂lam = G k T) ∧
    (∀ x, Tendsto (g · x) atTop (𝓝 1)) ∧
    ∀ C : Set (Mx D t t), IsClosed C → (∀ T ∈ C, T ∈ hermA D t ∧ e • T = T ∧ T ≠ 0) → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ T ∈ C, G k T ≤ ε

def EisMeas : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ mu : (G D t → ℂ) → ℂ, IsResMu mu → ∀ (M : Maps D hn) (m : Meas D W.rank t) (b₀ : HermE D W.rank), IsDiagInv b₀ →
  (∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ Φ : schwartzA θ B.rank n, IsRho (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω)) →
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∃ ν, IsOrb (t := t) B b₀ e ν ∧ ∀ Φ : schwartzA θ B.rank n, Good S e Φ.1 →
    ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Good S e (Ω 1) → HasCompactSupport (Ω 1) →
      mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) = ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv B b₀ z)) ∂ν

def NullSing : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  ∀ ν, IsOrb (t := t) V b₀ e ν → ν {z | ¬ Free e z} = 0

def Trans : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  IsOpen {z : Mx D V.rank r × Mx D V.rank t | Free e (e • z.1, e • z.2)} ∧
  ∀ z z' : Mx D V.rank r × Mx D V.rank t, Free e z → Free e z' →
    (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0) →
    (e • z'.1 = z'.1 ∧ e • z'.2 = z'.2 ∧ ip V z'.1 z'.1 = e • rat b₀.1 ∧ qv V b₀ z' = 0) →
    ∃ (h : GA D V) (y : Mx D r t), e • (mt V h - 1) = mt V h - 1 ∧ e • y = y ∧
      z' = (mm (mt V h) z.1, mm (mt V h) (z.2 + mm z.1 y))

def Uniq : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  ∀ ν ν', IsOrb (t := t) V b₀ e ν → IsOrb (t := t) V b₀ e ν' → ν' ≠ 0 → ∃ κ : ℝ≥0, ν = κ • ν'

def NoFrame : Prop := ∀ (D : D7) (t : ℕ) (B W : HSp D), Nonempty (HypDec B W t) → ∀ b₀ : HermE D W.rank, b₀.1.det ≠ 0 →
  (¬ ∃ x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, gramQ W x₀ = b₀.1) →
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ z : Mx D B.rank W.rank × Mx D B.rank t, Free e z → ¬ (ip B z.1 z.1 = e • rat b₀.1 ∧ e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ qv B b₀ z = 0)

def LatBound : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ), ∀ M ∈ schwartzA θ V.rank n,
  ∃ C : ℝ≥0, ∀ h : GA D V, ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
    ‖M (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C

def QK : Prop := ∀ (D : D7) (t : ℕ) (B W : HSp D) (d : HypDec B W t) (l : Lvl B), l.Good → ∀ νK : Measure l.K,
  νK.IsHaarMeasure → ∀ s : GA D B → ℝ≥0∞, Measurable s →
  (∀ (q : GlobalTheory.RegSW.stab d) h, s (q * h) = ((GlobalTheory.RegSW.absDet d q ^ (W.rank + t) : ℝ≥0) : ℝ≥0∞) * s h) →
  ∀ g, ∫⁻ k, s (k * g) ∂νK = ∫⁻ k, s k ∂νK

def IkSch : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (I : IkD d n) θ, IsInfFam θ →
  ∀ Φ ∈ schwartzA θ B.rank n, projS I.νK Φ ∈ schwartzA θ B.rank n ∧ ikp I Φ ∈ schwartzA θ W.rank n

def IkEq : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ (I : IkD d n) (Φ : schwartzA θ B.rank n) (Ψ : schwartzA θ W.rank n), Ψ.1 = ikp I Φ.1 → ∀ g, (ωW g Ψ).1 = ikp I (ωB g Φ).1

def ThetaSideMeasure : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ →
  ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 →
  ∃ ν : Measure (Mx D B.rank W.rank × Mx D B.rank t), IsOrb B b₀ 1 ν ∧
    (∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ν {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0) ∧
    ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t,
      Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) ν ∧
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) ∧
      ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂ν =
        ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ

def ToS : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 →
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ ν, IsOrb (t := t) V b₀ 1 ν →
    IsOrb V b₀ e ((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map fun z => (e • z.1, e • z.2)) ∧
    ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z) ∧ yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z

def MuId : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ mu : (G D t → ℂ) → ℂ, IsResMu mu → ∀ (M : Maps D hn) (m : Meas D W.rank t) (b₀ : HermE D W.rank), IsDiagInv b₀ →
  (∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ Φ : schwartzA θ B.rank n, IsRho (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω)) → ∀ I : IkD d n,
    ((¬ ∃ x₀, gramQ W x₀ = b₀.1) → ∀ (Φ : schwartzA θ B.rank n) Ω, IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) →
      mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) = 0) ∧
    ∀ x₀, gramQ W x₀ = b₀.1 → ∃ κ : ℂ, ∀ (Φ : schwartzA θ B.rank n) Ω, IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) →
      mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) =
        κ * ∫ y, orb W I.m (ikp I fun X => Φ.1 (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (Ω 1 y) ∂m.μ

def CoefId : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ I : IkD d n, ∀ H, IsHt H → ∀ Φ : schwartzA θ B.rank n, ∀ U dd E σ,
    IsCont H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) U dd E σ → ∀ ε, IsRad U dd ((t : ℂ) / 2) ε →
    ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∃ κ : ℂ, ∀ β : HermE D n, β.1.rank = W.rank → ∀ g,
      ((¬ ∃ x, gramQ W x = β.1) → fc ψ lam 𝓖 nb (cf dd E ((t : ℂ) / 2) ε 1) β g = 0) ∧
      ∀ x, gramQ W x = β.1 → fc ψ lam 𝓖 nb (cf dd E ((t : ℂ) / 2) ε 1) β g = κ * orb W I.m (ikp I (ωB g Φ).1) x

def thS (W : HSp D) (m : Measure (GA D W)) (𝓕 : Set (GA D W)) (Ψ : Mx D W.rank n → ℂ) : ℂ :=
  ∫ h in 𝓕, ∑' x : {x : Matrix (Fin W.rank) (Fin n) D.host.E // x.rank = W.rank}, Ψ (mm (mt W h⁻¹) (rat x.1)) ∂m

def ThCoef : Prop := ∀ (D : D7) (n : ℕ) (W : HSp D) ψ, IsCharAF D.host.F ψ → ∀ θ, IsInfFam θ → ∀ (m : Measure (GA D W)) 𝓕,
  m.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 m → ∀ lam 𝓖, IsCovolOneH (D := D) (r := n) lam 𝓖 →
  ∀ Ψ ∈ schwartzA θ W.rank n, m 𝓕 ≠ ⊤ ∧
    Continuous (fun x : hermA D n => thS W m 𝓕 fun X => pch ψ x.1 (ip W X X) * Ψ X) ∧ ∀ β : HermE D n,
    ((¬ ∃ x, x.rank = W.rank ∧ gramQ W x = β.1) →
      ∫ x in 𝓖, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0) ∧
    ∀ x₀, x₀.rank = W.rank → gramQ W x₀ = β.1 →
      ∫ x in 𝓖, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) ∂lam = orb W m Ψ x₀

def FourierPt : Prop := ∀ (D : D7) (n : ℕ) ψ, IsCharAF D.host.F ψ → ∀ lam 𝓖, IsCovolOneH (D := D) (r := n) lam 𝓖 →
  ∀ f : hermA D n → ℂ, Continuous f → (∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x) →
    (∀ β : HermE D n, ∫ x in 𝓖, f x * conj (pch ψ x.1 (rat β.1)) ∂lam = 0) → f = 0

def WeakApproximationFinitePlace : Prop := ∀ (D : D7) (n : ℕ) (v : Pl D) (U : Subgroup (G D n)), IsOpen (U : Set (G D n)) → ∀ g : G D n,
  ∃ γ ∈ GF D n, ∃ g' : G D n, proj D.sp.cm.sig (Jst D n) v g' = 1 ∧ ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k

def JPos : Prop := ∀ (D : D7) (n r t : ℕ), r + t = n → 1 ≤ r → ∀ ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ r →
  ∀ nb, IsNMap nb → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ (C : Cut D n v) (c : ℂ → ℂ), C.Kills ψ r ∧ Differentiable ℂ c ∧
    c ((t : ℂ) / 2) ≠ 0 ∧ ∀ νv : Measure (KAt D n v), νv.IsHaarMeasure → IsProbabilityMeasure νv →
    ∀ (z : ℂ) (f : G D n → ℂ), Continuous f → IsLaw χ z f → (∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) →
      ∀ g, ∫ k, cutR nb C f (g * k) ∂νv = c z * f g

def CfRel : Prop := ∀ (D : D7) (n : ℕ) χ, IsHeckeChar D χ → ∀ H : G D n → ℝ≥0, IsHt H → ∀ (s₀ : ℂ) φ, Continuous φ → IsLaw χ s₀ φ →
  ∀ U d E σ, IsCont H φ s₀ U d E σ → ∀ ε, IsRad U d s₀ ε → ∀ nb, IsNMap nb → ∀ (v : Pl D) (C : Cut D n v) (c : ℂ → ℂ),
  Differentiable ℂ c → ∀ νv : Measure (KAt D n v), IsProbabilityMeasure νv →
    (∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g) →
    ∀ k, 1 ≤ k → (∀ j, k < j → cf d E s₀ ε j = 0) → ∀ g, ∫ u, cutR nb C (cf d E s₀ ε k) (g * u) ∂νv = c s₀ * cf d E s₀ ε k g

def CfInv : Prop := ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0) (s₀ : ℂ) φ U d E σ, IsCont H φ s₀ U d E σ → ∀ ε, IsRad U d s₀ ε →
  ∀ u : G D n, (∀ g, H (g * u) = H g) → (∀ g, φ (g * u) = φ g) → ∀ k g, cf d E s₀ ε k (g * u) = cf d E s₀ ε k g

def ThBdd : Prop := ∀ (D : D7) (n : ℕ) (W : HSp D) ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ W.rank →
  ∀ θ, IsInfFam θ → ∀ μ, (∃ 𝓕, IsCovolOne (ratMx D W.rank n) μ 𝓕) → ∀ ω, IsWeilSch ψ χ θ W μ ω → ∀ nb, IsNMap nb →
  ∀ (v : Pl D) (C : Cut D n v), C.Kills ψ W.rank → ∀ Ψ Ψ' : schwartzA θ W.rank n, (∀ k ∈ KAt D n v, ω k Ψ = Ψ) →
    Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ →
    Continuous (fun u : G D n × GA D W => theta ω Ψ' u.1 u.2) ∧
    (∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h) ∧
    (∃ U : Subgroup (G D n), IsOpen (U : Set (G D n)) ∧ ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ') ∧
    (∀ K₀ : Set (G D n), IsCompact K₀ → ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Ψ' g h‖ ≤ b) ∧
    ∀ (x : hermA D n) (g : G D n), proj D.sp.cm.sig (Jst D n) v g = 1 →
      (∀ X, (ω g Ψ').1 X = cutF ψ C (ip W X X) * (ω g Ψ).1 X) ∧ ∀ h, theta ω Ψ' (nb x * g) h =
        ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
          pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))

def CutLow : Prop := ∀ (D : D7) (n r : ℕ) ψ, IsCharAF D.host.F ψ → ∀ nb, IsNMap nb → ∀ (v : Pl D) (C : Cut D n v), C.Kills ψ r →
  ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → (∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) →
    (RankLT ψ F r → cutR nb C F = 0) ∧
    (∃ U : Subgroup (G D n), IsOpen (U : Set (G D n)) ∧ ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g,
      cutR nb C F (g * k) = cutR nb C F g) ∧
    ∀ lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n) g, proj D.sp.cm.sig (Jst D n) v g = 1 →
      fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g ∧
      (β.1.rank < r → fc ψ lam 𝓖 nb (cutR nb C F) β g = 0)

def CutId : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) ψ χ θ μB μW ωB ωW,
    Stg d hn ψ χ θ μB μW ωB ωW →
  ∀ I : IkD d n, ∀ H, IsHt H → ∀ Φ : schwartzA θ B.rank n, ∀ U dd E σ,
    IsCont H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) U dd E σ → ∀ ε, IsRad U dd ((t : ℂ) / 2) ε → ∀ nb, IsNMap nb →
    ∀ (v : Pl D) (C : Cut D n v), C.Kills ψ W.rank → (∀ k ∈ KAt D n v, ωB k Φ = Φ ∧ ∀ g, H (g * k) = H g) →
    ∀ 𝓕, IsFundamentalDomain (GQ W) 𝓕 I.m → ∀ Ψ Ψ' : schwartzA θ W.rank n, Ψ.1 = ikp I Φ.1 →
      Ψ' = ∑ x ∈ C.s, C.co x • ωW (nb x) Ψ →
      ∃ κ : ℂ, ∀ g, cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g = κ * ∫ h in 𝓕, theta ωW Ψ' g h ∂I.m

end PositivityTheory.Rg.Rsw.L

end
