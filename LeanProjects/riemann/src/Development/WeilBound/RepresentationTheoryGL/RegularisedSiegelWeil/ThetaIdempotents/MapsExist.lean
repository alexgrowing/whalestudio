import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw

variable {D : D7} {n ρ p : ℕ}

def IsLaw (χ : (AE D)ˣ →* Circle) (s : ℂ) (φ : G D n → ℂ) : Prop :=
  ∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → ∀ g,
    φ (q * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s + (n : ℂ) / 2) * φ g

def IsHt (H : G D n → ℝ≥0) : Prop :=
  Continuous H ∧ (∀ g, 0 < H g) ∧ ∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → ∀ g,
    H (q * g) = absA D (Matrix.GeneralLinearGroup.det a) * H g

def fam (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₁ z : ℂ) (g : G D n) : ℂ := npow (H g) (z - s₁) * φ g

def eisS (f : G D n → ℂ) (g : G D n) : ℂ := GlobalTheory.Eis.cosetSum (P D n) (GF D n) f g

structure IsCont (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₀ : ℂ) (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (σ : ℝ) :
    Prop where
  isOpen : IsOpen U
  right : IsRightDomain U
  mem : s₀ ∈ U
  ne : d ≠ 0
  hol : ∀ g, DifferentiableOn ℂ (E · g) U
  cont : ContinuousOn (fun y : ℂ × G D n => E y.1 y.2) (U ×ˢ Set.univ)
  inv : ∀ z ∈ U, ∀ γ ∈ GF D n, ∀ g, E z (γ * g) = E z g
  eq : ∀ z : ℂ, σ < z.re → ∀ g, E z g = d.eval z * eisS (fam H φ s₀ z) g

def IsRad (U : Set ℂ) (d : Polynomial ℂ) (s₀ : ℂ) (ε : ℝ) : Prop :=
  0 < ε ∧ Metric.closedBall s₀ ε ⊆ U ∧ ∀ z ∈ Metric.closedBall s₀ ε, z ≠ s₀ → d.eval z ≠ 0

def cf (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) (g : G D n) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (E z g / d.eval z)

def bl {R : Type} (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (b : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) : Matrix (Fin n) (Fin n) R :=
  (Matrix.fromBlocks a b c d).submatrix (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm

structure Maps (D : D7) (hn : ρ + p = n) where

  emb : G D p →* G D n

  nzx : hermA D ρ → Mx D ρ p → G D n

  sh : Mx D ρ p → G D n

  w : G D n
  emb_cont : Continuous emb
  nzx_cont : Continuous fun u : hermA D ρ × Mx D ρ p => nzx u.1 u.2
  sh_cont : Continuous sh
  emb_mat : ∀ (h : G D p) (a b c d : Mx D p p), mat h = blk4 a b c d →
    mat (emb h) = blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)
  nzx_mat : ∀ z x, mat (nzx z x) = blk4 1 (bl hn z.1 x (adj x) 0) 0 1
  sh_mat : ∀ y, mat (sh y) = blk4 (bl hn 1 y 0 1) 0 0 (bl hn 1 0 (-adj y) 1)
  w_mat : mat w = blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def chz (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (z : hermA D ρ) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ)))

def pr (b₀ : HermE D ρ) (x y : Mx D ρ p) : Mx D p p :=
  HMul.hMul (adj x) (HMul.hMul (b₀.1.map (incA D)) y : Mx D ρ p)

def IsDiagInv (b₀ : HermE D ρ) : Prop := b₀.1.IsDiag ∧ b₀.1.det ≠ 0

structure IsTh (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (b₀ : HermE D ρ) (μ : Measure (Mx D ρ p))
    (Ω : G D p → Mx D ρ p → ℂ) : Prop where
  mem : ∀ h, Ω h ∈ schwartzA θ ρ p
  cont : Continuous fun u : G D p × Mx D ρ p => Ω u.1 u.2
  maj : ∀ C : Set (G D p), IsCompact C → ∃ M ∈ schwartzA θ ρ p, ∀ h ∈ C, ∀ y, ‖Ω h y‖ ≤ ‖M y‖
  levi : ∀ (g : G D p) (a : GL (Fin p) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ h y,
    Ω (g * h) y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((ρ : ℂ) / 2) *
      Ω h (HMul.hMul y a.1 : Mx D ρ p)
  unip : ∀ (g : G D p) (b : Mx D p p), mat g = blk4 1 b 0 1 → ∀ h y,
    Ω (g * h) y = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) * Ω h y
  weyl : ∀ g : G D p, mat g = blk4 0 1 (-1) 0 → ∀ h x,
    Ω (g * h) x = ∫ y, Ω h y * ψ (trA (Matrix.trace (pr b₀ x y))) ∂μ

structure Meas (D : D7) (ρ p : ℕ) where
  lz : Measure (hermA D ρ)
  𝓖 : Set (hermA D ρ)
  μ : Measure (Mx D ρ p)
  𝓕 : Set (Mx D ρ p)
  hz : IsCovolOneH lz 𝓖
  hμ : IsCovolOne (ratMx D ρ p) μ 𝓕

section Fun

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)

def zc (F : G D n → ℂ) (g : G D n) : ℂ := ∫ z in m.𝓖, F (M.nzx z 0 * g) * conj (chz ψ b₀ z) ∂m.lz

def pc (F : G D n → ℂ) (g : G D n) : ℂ := ∫ x in m.𝓕, zc M m ψ b₀ F (M.nzx 0 x * g) ∂m.μ

def FJ (F : G D n → ℂ) (g : G D n) (φ : Mx D ρ p → ℂ) : ℂ := ∫ y, pc M m ψ b₀ F (M.sh y * g) * conj (φ y) ∂m.μ

def Wz (f : G D n → ℂ) (g : G D n) : ℂ := ∫ z, f (M.w * M.nzx z 0 * g) * conj (chz ψ b₀ z) ∂m.lz

def Rsec (f : G D n → ℂ) (g : G D n) (Ω : G D p → Mx D ρ p → ℂ) (h : G D p) : ℂ :=
  ∫ y, Wz M m ψ b₀ f (M.sh y * M.emb h * g) * conj (Ω h y) ∂m.μ

def th (φ : Mx D ρ p → ℂ) (z : hermA D ρ) (x y : Mx D ρ p) : ℂ :=
  chz ψ b₀ z * ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
    ψ (trA (Matrix.trace (pr b₀ x (ξ.map (incA D))))) * φ (ξ.map (incA D) + y)

end Fun

def IsExt (hn : ρ + p = n) (b₀ : HermE D ρ) (β : HermE D n) : Prop := β.1 = bl hn b₀.1 0 0 0

def RankLT (ψ : AddChar (AF D.host.F) ℂ) (F : G D n → ℂ) (k : ℕ) : Prop :=
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ β : HermE D n, k ≤ β.1.rank → ∀ g, fc ψ lam 𝓖 nb F β g = 0

def IsRho (f : G D p → ℂ) : Prop := Continuous f ∧ IsLaw 1 ((p : ℂ) / 2) f

structure IsResMu (mu : (G D p → ℂ) → ℂ) : Prop where
  add : ∀ f f', IsRho f → IsRho f' → mu (f + f') = mu f + mu f'
  smul : ∀ (c : ℂ) f, IsRho f → mu (c • f) = c * mu f
  pos : ∀ f, IsRho f → (∀ g, 0 ≤ (f g).re ∧ (f g).im = 0) → 0 ≤ (mu f).re ∧ (mu f).im = 0
  bound : ∀ H : G D p → ℝ≥0, IsHt H → ∃ C : ℝ, ∀ f, IsRho f → ∀ B : ℝ, (∀ g, ‖f g‖ ≤ B * (H g : ℝ) ^ p) → ‖mu f‖ ≤ C * B
  inv_n : ∀ (x : G D p) (b : Mx D p p), mat x = blk4 1 b 0 1 → ∀ f, IsRho f → mu (fun g => f (g * x)) = mu f
  inv_rat : ∀ γ ∈ GF D p, ∀ f, IsRho f → mu (fun g => f (g * γ)) = mu f
  lim : ∀ f : ℝ → G D p → ℂ, ContinuousOn (fun u : ℝ × G D p => f u.1 u.2) (Set.Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ Set.univ) →
    (∀ σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (f σ)) → ∀ a : ℂ,
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (f σ) 1) (𝓝[>] ((p : ℝ) / 2)) (𝓝 a) → a = mu (f (p / 2))

def MapsExist : Prop := ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), Nonempty (Maps D hn) ∧ Nonempty (Meas D ρ p)

def HtExist : Prop := ∀ (D : D7) (n : ℕ), (∃ H : G D n → ℝ≥0, IsHt H) ∧
  ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c

def ZUnfold : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ →
  ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ χ, IsHeckeChar D χ → ∀ (s : ℂ) (f : G D n → ℂ), Continuous f → IsLaw χ s f →
    (n : ℝ) / 2 < s.re → ∀ g,
    HasSum (fun u : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E =>
      Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)) (zc M m ψ b₀ (eisS f) g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ,
      Summable c ∧ ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u

def ThTwist : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ →
  ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ χ, IsHeckeChar D χ → ∀ θ, IsInfFam θ → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω →
  ∀ γ ∈ GF D p, ∀ z x y z' x' y', M.emb γ * (M.nzx z x * M.sh y) = M.nzx z' x' * M.sh y' * M.emb γ →
    th ψ b₀ (Ω 1) z x y = th ψ b₀ (Ω γ) z' x' y'

def FJEis : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ →
  ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ χ χ', IsHeckeChar D χ → IsHeckeChar D χ' → ∀ θ, IsInfFam θ →
  ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (s : ℂ) (f : G D n → ℂ), Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re → ∀ g,
    FJ M m ψ b₀ (eisS f) g (Ω 1) = eisS (Rsec M m ψ b₀ f g Ω) 1

def PcBound : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
    (∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → Continuous (pc M m ψ b₀ F)) ∧
    ∀ g, ∃ C : Set (G D n), IsCompact C ∧ (∀ z x y, ∃ γ ∈ GF D n, γ * (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) ∈ C) ∧
      ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → ∀ B : ℝ, (∀ c ∈ C, ‖F c‖ ≤ B) →
        ∀ y, ‖pc M m ψ b₀ F (M.sh y * g)‖ ≤ B

def RSec : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ →
  ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ χ χ', IsHeckeChar D χ → IsHeckeChar D χ' → ∀ θ, IsInfFam θ →
  ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ H, IsHt H → ∀ (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ → ∀ g,
    ContinuousOn (fun u : ℂ × G D p => Rsec M m ψ b₀ (fam H φ s₁ u.1) g Ω u.2)
      ({z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} ×ˢ Set.univ) ∧
    (∀ h, DifferentiableOn ℂ (fun z => Rsec M m ψ b₀ (fam H φ s₁ z) g Ω h) {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re}) ∧
    ∀ z : ℂ, ((ρ : ℝ) - p) / 2 < z.re → IsLaw (χ * χ'⁻¹) z (Rsec M m ψ b₀ (fam H φ s₁ z) g Ω)

def EisHol : Prop :=
  ∀ (D : D7) (p : ℕ) χ, IsHeckeChar D χ → ∀ (c : ℝ) (f : ℂ → G D p → ℂ),
    ContinuousOn (fun u : ℂ × G D p => f u.1 u.2) ({z : ℂ | c < z.re} ×ˢ Set.univ) →
    (∀ h, DifferentiableOn ℂ (f · h) {z : ℂ | c < z.re}) → (∀ z : ℂ, c < z.re → IsLaw χ z (f z)) →
    ∀ h, DifferentiableOn ℂ (fun z => eisS (f z) h) {z : ℂ | c < z.re ∧ (p : ℝ) / 2 < z.re}

def ThTotal : Prop :=
  ∀ (D : D7) (ρ p : ℕ) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, IsDiagInv b₀ →
  ∀ χ, IsHeckeChar D χ → ResEta D χ ρ → (ρ = 0 → χ = 1) → ∀ θ, IsInfFam θ → ∀ u : Mx D ρ p → ℂ, Continuous u → (∃ B, ∀ y, ‖u y‖ ≤ B) →
    (∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∫ y, u y * conj (Ω 1 y) ∂m.μ = 0) → u = 0

def CfFJ : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0) φ s₀ U d E σ, IsCont H φ s₀ U d E σ → ∀ ε, IsRad U d s₀ ε →
    (∀ k, Continuous (cf d E s₀ ε k) ∧ LeftInv (GF D n) (cf d E s₀ ε k)) ∧ (∃ N, ∀ k, N < k → cf d E s₀ ε k = 0) ∧
    ∀ (ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) g
      (η : Mx D ρ p → ℂ), Integrable η m.μ →
      DifferentiableOn ℂ (fun z => FJ M m ψ b₀ (E z) g η) U ∧
      ∀ k, FJ M m ψ b₀ (cf d E s₀ ε k) g η =
        (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (FJ M m ψ b₀ (E z) g η / d.eval z)

def PcFc : Prop :=
  ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) ψ, IsCharAF D.host.F ψ →
  ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F →
    ((∀ b₀ : HermE D ρ, IsDiagInv b₀ → ∀ g, pc M m ψ b₀ F g = 0) → RankLT ψ F ρ) ∧
    (RankLT ψ F (ρ + 1) → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ β, IsExt hn b₀ β →
      ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ g, pc M m ψ b₀ F g = fc ψ lam 𝓖 nb F β g)

def SphBound : Prop :=
  ∀ (D : D7) (p : ℕ), 1 ≤ p → ∀ H : G D p → ℝ≥0, IsHt H → ∀ C : Set (G D p), IsCompact C → ∃ B : ℝ,
    ∀ σ ∈ Set.Ioc ((p : ℝ) / 2) (p / 2 + 1), ∀ h ∈ C,
      Summable (fun q : GlobalTheory.Eis.Cosets (P D p) (GF D p) => (H ((q.out : GF D p) * h) : ℝ) ^ (σ + p / 2)) ∧
      (σ - p / 2) * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H ((q.out : GF D p) * h) : ℝ) ^ (σ + p / 2) ≤ B

def ResMu : Prop := ∀ (D : D7) (p : ℕ), 2 ≤ p → ∃ mu : (G D p → ℂ) → ℂ, IsResMu mu

def Polar : Prop :=
  ∀ (D : D7) (n r t : ℕ) (hn : r + t = n), r + 2 < 2 * t → ∀ ψ, IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ → ResEta D χ r →
  (r = 0 → χ = 1) → ∀ θ : InfFam D, IsInfFam θ → ∀ H : G D n → ℝ≥0, IsHt H → ∀ φ, Continuous φ → IsLaw χ ((t : ℂ) / 2) φ →
  ∀ U d E σ, IsCont H φ ((t : ℂ) / 2) U d E σ → ∀ ε, IsRad U d ((t : ℂ) / 2) ε →
    (∀ k, 1 ≤ k → RankLT ψ (cf d E ((t : ℂ) / 2) ε k) (r + 1)) ∧ (∀ k, 2 ≤ k → RankLT ψ (cf d E ((t : ℂ) / 2) ε k) r) ∧
    ∀ mu : (G D t → ℂ) → ℂ, IsResMu mu → ∀ (M : Maps D hn) (m : Meas D r t) (b₀ : HermE D r), b₀.1.det ≠ 0 →
    ∀ β, IsExt hn b₀ β → ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ g,
      IsRho (Rsec M m ψ b₀ φ g Ω) ∧
      ∫ y, fc ψ lam 𝓖 nb (cf d E ((t : ℂ) / 2) ε 1) β (M.sh y * g) * conj (Ω 1 y) ∂m.μ = mu (Rsec M m ψ b₀ φ g Ω)

end PositivityTheory.Rg.Rsw

end
