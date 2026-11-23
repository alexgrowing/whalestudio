import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial MeasureTheory
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Br

structure IsLow (k : ℕ) (φ : TR.Sm ℚ 2) : Prop where
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)
  one : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0

def CapTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : InfinitePlace F) (a b : ℂ), π.HasInfChar v {a, b} →
    ∀ φ ∈ π.V, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = (a + b) • φ ∧
      TR.Eop v 0 0 (TR.Eop v 0 0 φ) + TR.Eop v 0 1 (TR.Eop v 1 0 φ) + TR.Eop v 1 0 (TR.Eop v 0 1 φ) + TR.Eop v 1 1 (TR.Eop v 1 1 φ) =
        (a ^ 2 + b ^ 2 - 1 / 2) • φ

def WtVec : Prop :=
  ∀ π : TR.CuspSub ℚ 2, ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ n : ℤ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * n) • φ

def Sl2Low : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W R L : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ), 3 ≤ k →
    W * R - R * W = (2 : ℂ) • R → W * L - L * W = (-2 : ℂ) • L → (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W) →
    (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - (W * W + (2 : ℂ) • W) →
    (∀ x, H x x = 0 → x = 0) → (∀ x y, H (W x) y = H x (W y)) → (∀ x y, H (R x) y = -H x (L y)) → (∀ x y, H (L x) y = -H x (R y)) →
    (∃ x, x ≠ 0 ∧ ∃ n : ℤ, W x = (n : ℂ) • x) →
    ∃ x, x ≠ 0 ∧ ((W x = (k : ℂ) • x ∧ L x = 0) ∨ (W x = (-(k : ℂ)) • x ∧ R x = 0))

def HolVec : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∀ H, Gk.IsHerm π H → ∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ

def LevelVec : Prop :=
  ∀ (k : ℕ) (π : TR.CuspSub ℚ 2), (∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ) →
    ∃ (N : ℕ) (ψ : DirichletCharacter ℂ N) (ν : HChar ℚ), 1 ≤ N ∧ IsDirOf ψ ν ∧
      ∃ φ ∈ (π.twist ν).V, φ ≠ 0 ∧ IsLow k φ ∧ ∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ

def CharOf : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (ω : HChar ℚ) (φ : TR.Sm ℚ 2), φ ≠ 0 → (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ χ : DirichletCharacter ℂ N, IsDirOf χ ω

def down (k : ℕ) (φ : GA ℚ 2 → ℂ) (z : ℍ) : ℂ :=
  ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 z.im z.im_pos.ne') z.re))

def DownLift : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ φ : TR.Sm ℚ 2, (∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g) → IsLow k φ → (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    Nf.IsLift k N (down k φ.1) φ.1

def DownHol : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), IsLow k φ → MDiff (down k φ.1)

def DownChar : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : ℍ → ℂ) (φ : GA ℚ 2 → ℂ), Nf.IsLift k N f φ →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g) → HasChar k χ f

def PerZero : Prop :=
  ∀ (f : ℍ → ℂ) (N : ℕ), 0 < N → MDiff f → (∀ z : ℍ, f ((N : ℝ) +ᵥ z) = f z) →
    (∃ (C : ℝ) (m : ℕ), ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ N → ‖f z‖ ≤ C * z.im ^ m) →
    (∀ z : ℍ, ∫ t in (0 : ℝ)..N, f (t +ᵥ z) = 0) → IsZeroAtImInfty f

def CuspMean : Prop :=
  ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → ∀ g, ∃ N : ℕ, 0 < N ∧ ∀ y : GL (Fin 2) ℝ,
    Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (g * upR y))) N ∧ ∫ t in (0 : ℝ)..N, φ.1 (upR (aff 1 t) * (g * upR y)) = 0

def DownZero : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), TR.IsCuspForm φ → IsLow k φ → IsZeroAtImInfty (down k φ.1)

def Deadel : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → IsLow k φ →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ f : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ Nf.IsLift k N f φ.1

def UOfSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (x : V) (α β : ℂˣ), GlobalTheory.LFun.IsSatVecGL w ρ x {α, β} →
    Uop w ρ 0 x = ((((normV w : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) • x ∧
    ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x

def EigOf : Prop :=
  ∀ (k N : ℕ), 1 ≤ k → 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : CuspForm (Gamma1 N) (k : ℤ))
    (φ : TR.Sm ℚ 2), Nf.IsLift k N f φ.1 → IsHol k (lev N) ω φ → ∀ (w : Pl ℚ) (α β : ℂˣ), ¬ normV w ∣ N →
    GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α, β} →
    IsEigAt k χ f (normV w) ((((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) ∧ ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def EigEx : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f → f ≠ 0 → ∀ a : ℕ → ℂ,
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p

def ClTwist : Prop :=
  ∀ (N k : ℕ) [NeZero N] (χ ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f →
    ∃ g : CuspForm (Gamma1 (N * N)) (k : ℤ), HasChar k (DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2)) g ∧
      ∀ n : ℕ, coef g n = ψ (n : ZMod N) * coef f n

def MinNew : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    ∃ (f : Newform k) (_ : NeZero f.M) (h : Eigenform k f.M f.χ), h.f = f.f ∧ ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p

def CharEq : Prop :=
  ∀ (k N M : ℕ) [NeZero N] [NeZero M], 2 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (g : Eigenform k N χ)
    (h : Eigenform k M ψ), (∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p) →
    ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → χ (p : ZMod N) = ψ (p : ZMod M)

def RepEig : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), ∀ᶠ w : Pl ℚ in Filter.cofinite, ∃ α β : ℂˣ,
      π.HasSat w {α, β} ∧ g.a (normV w) = (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) ∧
        ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def RepNewAE : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Br
