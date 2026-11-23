import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a r s : ℕ}

def aInf (E : Type) [Field E] (N r : ℕ) (t : ℝ) : GL (Fin N) (Cinf E) :=
  ⟨Matrix.diagonal fun i _ => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0),
    Matrix.diagonal fun i _ => Complex.exp (-(if (i : ℕ) < r then (t : ℂ) else 0)),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i v; simp [← Complex.exp_add],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i v; simp [← Complex.exp_add]⟩

def aT (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ) (t : ℝ) : GA E N := infGL E N (aInf E N r t)

def IsCT (r : ℕ) (φ F : GA E N → ℂ) : Prop :=
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  ∃ (μ : Measure (BlockIx N r → Ad E)) (𝓕 : Set (BlockIx N r → Ad E)), μ.IsAddHaarMeasure ∧
    IsAddFundamentalDomain (ratN E N r) 𝓕 μ ∧ F = PositivityTheory.Affgl.CT.ct μ 𝓕 φ

def Exp (r : ℕ) (φ : GA E N → ℂ) : Set ℂ :=
  {c | ∃ F₀, IsCT r φ F₀ ∧ ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (aT E N r t * g)),
    F ≠ 0 ∧ ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g}

def ExpV (r : ℕ) (V : Submodule ℂ (Sm E N)) : Set ℂ := {c | ∃ φ ∈ V, c ∈ Exp r φ.1}

def pE (E : Type) [Field E] [NumberField E] (N r : ℕ) (c : ℂ) : ℝ :=
  c.re / (Module.finrank ℚ E : ℝ) - (r : ℝ) * ((N : ℝ) - r) / 2

def tw (V : Submodule ℂ (Sm E N)) (z : ℂ) : Submodule ℂ (Sm E N) :=
  V.map (mulChi N (GlobalTheory.CuspRep.Model.absC E z)).toLinearMap

def tens2 (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (GA E r × GA E s → ℂ) :=
  Submodule.span ℂ {F | ∃ φ₁ ∈ V₁, ∃ φ₂ ∈ V₂, F = fun m => φ₁.1 m.1 * φ₂.1 m.2}

def MemInd2 (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (φ : Sm E (r + s)) : Prop :=
  (∀ (x : BlockIx (r + s) r → Ad E) g, φ.1 (unip x * g) = φ.1 g) ∧
    ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      (fun m => φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∈ tens2 V₁ V₂

def Emb (V : Submodule ℂ (Sm E N)) (P : Sm E N → Prop) : Prop :=
  ∃ f : Sm E N →ₗ[ℂ] Sm E N, (∀ φ ∈ V, P (f φ)) ∧ (∀ φ ∈ V, f φ = 0 → φ = 0) ∧ ∀ o, ∀ φ ∈ V, f (act o φ) = act o (f φ)

def AscEmb (V : Submodule ℂ (Sm E N)) (π : CuspSub E a) (d : ℕ) : Prop :=
  ∃ (h : ∑ _ : Fin d, a = N) (ν : Fin d → HChar E), (∀ i, (ν i).IsAbsPow (-spehExp d i + a * spehExp d i)) ∧
    Emb V (· ∈ indForms h fun i => π.twist (ν i))

def RegInt (V : Submodule ℂ (Sm E N)) (τ : E →+* ℂ) : Prop :=
  ∃ m, HasInfCharGL V τ m ∧ m.Nodup ∧ ∀ x ∈ m, ∀ y ∈ m, ∃ n : ℤ, x - y = n

def SatV (V : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  (∃ φ ∈ V, GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B) ∧
    ∀ φ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) φ = φ) → φ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B

def satTw (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun b => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)

structure IsSliceMap (V : Submodule ℂ (Sm E (r + s))) (c : ℂ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop where
  equiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)
  ne : ∃ φ ∈ V, T φ ≠ 0
  unipInv : ∀ φ ∈ V, ∀ (x : BlockIx (r + s) r → Ad E) g, (T φ).1 (unip x * g) = (T φ).1 g
  left : ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s), ∃ ψ : Sm E r, IsAutForm ψ ∧
    (∀ m₁, ψ.1 m₁ = (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ (t : ℝ) m₁, ψ.1 (splitCentre E r t * m₁) = Complex.exp (c * t) * ψ.1 m₁) ∧
    ∀ r₁, 0 < r₁ → r₁ < r → ∀ c₁ ∈ Exp r₁ ψ.1, c₁ ∈ ExpV r₁ V
  right : ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r), ∃ ψ : Sm E s, IsAutForm ψ ∧
    (∀ m₂, ψ.1 m₂ = (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ (t : ℝ) m₂, ψ.1 (splitCentre E s t * m₂) = Complex.exp (-c * t) * ψ.1 m₂) ∧
    ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ ψ.1, c + c₂ ∈ ExpV (r + r₂) V

end PositivityTheory.Rg.Rs

end
